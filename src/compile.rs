use std::{
    any::Any, cell::RefCell, collections::HashMap, iter::once_with, path::Path, process::Command,
    rc::Rc,
};

use inkwell::{
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetTriple},
    types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType, StructType},
    values::{
        AnyValue, BasicMetadataValueEnum, BasicValue, BasicValueEnum, CallSiteValue, FunctionValue,
        PointerValue,
    },
    AddressSpace, IntPredicate, OptimizationLevel,
};

use crate::{
    functions,
    parser::{BinOp, Block, Expression, Program, Statement, Type, Value},
    typecheck::{self, ScopeInfo},
};
const PRINTF: &str = "printf";
const MEMSET: &str = "memset";
pub struct Compiler<'ctx, 'a> {
    pub context: &'ctx Context,
    pub builder: &'a Builder<'ctx>,
    pub module: &'a Module<'ctx>,
    pub vars: HashMap<i32, PointerValue<'ctx>>,
    strings: Rc<RefCell<HashMap<String, PointerValue<'ctx>>>>,
    mapstructs: HashMap<Type, StructType<'ctx>>,
    entrystructs: HashMap<Type, StructType<'ctx>>,
}

pub fn compile(program: Program) {
    let context = Context::create();
    let module = context.create_module("module");
    let builder = context.create_builder();

    let mut c = Compiler {
        context: &context,
        module: &module,
        builder: &builder,
        vars: HashMap::new(),
        strings: Rc::new(RefCell::new(HashMap::new())),
        mapstructs: HashMap::new(),
        entrystructs: HashMap::new(),
    };
    c.compile(program);
}

pub const MAP_CAPACITY: u32 = 0;
pub const MAP_SIZE: u32 = 1;
pub const MAP_KEYS: u32 = 2;
pub const MAP_STATES: u32 = 3;
pub const MAP_VALUES: u32 = 4;

pub const STATE_FREE: u64 = 0;
pub const STATE_TOMB: u64 = 1;
pub const STATE_TAKEN: u64 = 2;

impl<'ctx, 'a> Compiler<'ctx, 'a> {
    fn mapstruct(&mut self, t: &Type) -> &StructType<'ctx> {
        if let Type::Map(k, v) = t {
            let struct_name = format!("{t}");
            let capacity = self.context.i64_type();
            let size = self.context.i64_type();
            let keys = self.llvmtype(k).ptr_type(AddressSpace::default());
            let states = self.llvmtype(&Type::Int).ptr_type(AddressSpace::default());
            let vals = self.llvmtype(v).ptr_type(AddressSpace::default());

            self.mapstructs.entry(t.clone()).or_insert({
                let st = self.context.opaque_struct_type(&struct_name);
                st.set_body(
                    &[
                        capacity.into(),
                        size.into(),
                        keys.into(),
                        states.into(),
                        vals.into(),
                    ],
                    false,
                );
                st
            })
        } else {
            assert!(matches!(t, Type::Map { .. }));
            panic!()
        }
    }

    fn llvmtype(&mut self, t: &Type) -> BasicTypeEnum<'ctx> {
        match t {
            Type::Int => self.context.i64_type().as_basic_type_enum(),
            Type::Float => self.context.f64_type().as_basic_type_enum(),
            Type::Bool => self.context.bool_type().as_basic_type_enum(),
            Type::Char => self.context.i64_type().as_basic_type_enum(),
            Type::Unit => self.context.custom_width_int_type(0).as_basic_type_enum(),
            Type::Map(_, _) => self
                .mapstruct(t)
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum(),
        }
    }
    fn llvmfunctiontype(
        &mut self,
        t: &Type,
        param_types: &[BasicMetadataTypeEnum<'ctx>],
        is_var_args: bool,
    ) -> FunctionType<'ctx> {
        match t {
            Type::Int => self.context.i64_type().fn_type(param_types, is_var_args),
            Type::Float => self.context.f64_type().fn_type(param_types, is_var_args),
            Type::Bool => self.context.bool_type().fn_type(param_types, is_var_args),
            Type::Char => self.context.i64_type().fn_type(param_types, is_var_args),
            Type::Unit => self.context.void_type().fn_type(param_types, is_var_args),
            Type::Map(_, _) => self
                .mapstruct(t)
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum()
                .fn_type(param_types, is_var_args),
        }
    }

    pub fn compile(&mut self, program: Program) {
        //add external functions
        {
            self.module.add_function(
                PRINTF,
                self.context.i32_type().fn_type(
                    &[self
                        .context
                        .i8_type()
                        .ptr_type(AddressSpace::default())
                        .into()],
                    true,
                ),
                Some(Linkage::External),
            );
            self.module.add_function(
                MEMSET,
                self.context.void_type().fn_type(
                    &[
                        self.context
                            .i8_type()
                            .ptr_type(AddressSpace::default())
                            .into(),
                        self.context.i32_type().into(),
                        self.context.i32_type().into(),
                    ],
                    false,
                ),
                Some(Linkage::External),
            );
        }
        // compile program
        program
            .functions
            .iter()
            .map(|f| {
                //add functions to context
                (f, {
                    let params = f
                        .arguments
                        .iter()
                        .map(|t| self.llvmtype(&t.0).into())
                        .collect::<Vec<_>>();
                    self.module.add_function(
                        f.identifier,
                        self.llvmfunctiontype(&f.return_type, params.as_slice(), false),
                        None,
                    )
                })
            })
            .collect::<Vec<_>>()
            .iter()
            .for_each(|(f, function_value)| {
                //compile functions
                self.builder
                    .position_at_end(self.context.append_basic_block(*function_value, "entry"));
                for (t, id) in &f.arguments {
                    let (_, _, i, argnum) =
                        typecheck::find_variable(id, f.body.scopeinfo.clone()).unwrap();
                    let varname = format!("{id}_{i}");
                    self.builder.build_store(
                        {
                            let p = self.builder.build_alloca(self.llvmtype(t), &varname);
                            self.vars.insert(i, p);
                            p
                        },
                        function_value.get_params()[argnum.unwrap() as usize],
                    );
                }
                self.emit_block(&f.body, *function_value);
                if f.return_type == Type::Unit {
                    self.builder.build_return(None);
                }
            });

        //export
        {
            //save llvm ir
            let _result = self.module.print_to_file("./out/main.ll");

            //check module
            if let Err(e) = self.module.verify() {
                println!("{}", e.to_string());
                return;
            }

            //save executable
            Target::initialize_x86(&InitializationConfig::default());

            let opt = OptimizationLevel::Aggressive;
            let reloc = RelocMode::Default;
            let model = CodeModel::Default;
            let target = Target::from_name("x86-64").unwrap();
            let target_machine = target
                .create_target_machine(
                    &TargetTriple::create("x86_64-pc-linux-gnu"),
                    "x86-64",
                    "+avx2",
                    opt,
                    reloc,
                    model,
                )
                .unwrap();

            let _result = target_machine.write_to_file(
                self.module,
                FileType::Assembly,
                Path::new("./out/main.asm"),
            );
            let _result = Command::new("clang")
                .arg("-no-pie")
                .arg("./out/main.asm")
                .arg("-o")
                .arg("./out/main")
                .output();
        }

        //exec
        self.execute()
    }

    fn emit_printf_call(
        &self,
        string: &&str,
        args: &[BasicMetadataValueEnum<'ctx>],
    ) -> CallSiteValue<'ctx> {
        let mut printfargs: Vec<BasicMetadataValueEnum<'ctx>> =
            vec![self.emit_global_string(string, "str").into()];
        printfargs.extend_from_slice(args);
        let f = self.module.get_function(PRINTF).unwrap();
        self.builder.build_call(f, &printfargs, "")
    }

    fn emit_global_string(&self, string: &&str, name: &str) -> PointerValue<'ctx> {
        let string = string.to_owned().to_owned() + "\0";
        if self.strings.borrow().contains_key(&string) {
            return *self.strings.borrow().get(&string).unwrap();
        }
        let ty = self.context.i8_type().array_type(string.len() as u32);
        let gv = self
            .module
            .add_global(ty, Some(AddressSpace::default()), name);
        gv.set_linkage(Linkage::Internal);
        gv.set_initializer(&self.context.const_string(string.as_ref(), false));

        let pointer_value = self.builder.build_pointer_cast(
            gv.as_pointer_value(),
            self.context.i8_type().ptr_type(AddressSpace::default()),
            name,
        );
        self.strings.borrow_mut().insert(string, pointer_value);
        pointer_value
    }

    fn execute(&self) {
        let ee = self
            .module
            .create_jit_execution_engine(OptimizationLevel::None)
            .unwrap();
        let maybe_fn = unsafe { ee.get_function::<unsafe extern "C" fn() -> f64>("main") };

        let compiled_fn = match maybe_fn {
            Ok(f) => f,
            Err(err) => {
                panic!("{:?}", err);
            }
        };

        unsafe {
            compiled_fn.call();
        }
    }

    fn emit_block(&mut self, body: &Block, fv: FunctionValue<'ctx>) {
        for s in &body.statements {
            self.emit_statement(s, fv, body.scopeinfo.clone());
        }
    }

    fn emit_statement(
        &mut self,
        statement: &Statement,
        fv: FunctionValue<'ctx>,
        scopeinfo: Rc<RefCell<ScopeInfo>>,
    ) {
        match &statement.statement {
            crate::parser::StatementType::Assignment(t, id, expr, Some(i)) => {
                let varname = format!("{id}_{i}");
                let pointer = {
                    if t.is_some() {
                        let p = self
                            .builder
                            .build_alloca(self.llvmtype(&(t.as_ref().unwrap().clone())), &varname);
                        self.vars.insert(*i, p);
                        p
                    } else {
                        *self.vars.get(i).unwrap()
                    }
                };
                let value = self.emit_expression(expr, scopeinfo, fv);
                self.builder.build_store(pointer, value);
            }
            crate::parser::StatementType::Creation(maptype, id, Some(i)) => {
                if let Type::Map(k, v) = maptype {
                    let varname = format!("{id}_{i}");
                    let fname = format!("{maptype}_create");
                    let fv = if let Some(fv) = self.module.get_function(&fname) {
                        fv
                    } else {
                        let fv = self.module.add_function(
                            &fname,
                            self.llvmfunctiontype(maptype, &[], false),
                            None,
                        );
                        let call_block = self.builder.get_insert_block().unwrap();
                        self.builder
                            .position_at_end(self.context.append_basic_block(fv, "entry"));
                        let map = self
                            .builder
                            .build_malloc(*self.mapstruct(maptype), &varname)
                            .unwrap();
                        let initial_capacity: u32 = 16;

                        let capacity = self
                            .builder
                            .build_struct_gep(map, MAP_CAPACITY, &(varname.clone() + ".capacity"))
                            .unwrap();
                        self.builder.build_store(
                            capacity,
                            self.context
                                .i64_type()
                                .const_int(initial_capacity.into(), false),
                        );
                        let size = self
                            .builder
                            .build_struct_gep(map, MAP_SIZE, &(varname.clone() + ".size"))
                            .unwrap();
                        self.builder
                            .build_store(size, self.context.i64_type().const_int(0, false));

                        let keys = self
                            .builder
                            .build_struct_gep(map, MAP_KEYS, &(varname.clone() + ".keys"))
                            .unwrap();
                        self.builder.build_store(
                            keys,
                            self.builder.build_bitcast(
                                self.builder
                                    .build_malloc(
                                        self.llvmtype(k).array_type(initial_capacity),
                                        "keys_alloc",
                                    )
                                    .unwrap(),
                                self.llvmtype(k).ptr_type(AddressSpace::default()),
                                "keys_ptr",
                            ),
                        );
                        let states = self
                            .builder
                            .build_struct_gep(map, MAP_STATES, &(varname.clone() + ".states"))
                            .unwrap();
                        let states_alloc = self
                            .builder
                            .build_malloc(
                                self.llvmtype(&Type::Int).array_type(initial_capacity),
                                "states_alloc",
                            )
                            .unwrap();
                        self.builder.build_call(
                            self.module.get_function(MEMSET).unwrap(),
                            &[
                                self.builder
                                    .build_bitcast(
                                        states_alloc,
                                        self.context.i8_type().ptr_type(AddressSpace::default()),
                                        "",
                                    )
                                    .into(),
                                self.context.i32_type().const_zero().into(),
                                self.builder
                                    .build_int_cast(
                                        self.llvmtype(&Type::Int)
                                            .array_type(initial_capacity)
                                            .size_of()
                                            .unwrap(),
                                        self.context.i32_type(),
                                        "",
                                    )
                                    .into(),
                            ],
                            "",
                        );
                        self.builder.build_store(
                            states,
                            self.builder.build_bitcast(
                                states_alloc,
                                self.llvmtype(&Type::Int).ptr_type(AddressSpace::default()),
                                "states_ptr",
                            ),
                        );

                        let values = self
                            .builder
                            .build_struct_gep(map, MAP_VALUES, &(varname.clone() + ".values"))
                            .unwrap();
                        self.builder.build_store(
                            values,
                            self.builder.build_bitcast(
                                self.builder
                                    .build_malloc(
                                        self.llvmtype(v).array_type(initial_capacity),
                                        "values_alloc",
                                    )
                                    .unwrap(),
                                self.llvmtype(v).ptr_type(AddressSpace::default()),
                                "values_ptr",
                            ),
                        );

                        let mapptr = self.builder.build_alloca(self.llvmtype(maptype), &varname);
                        self.builder.build_store(mapptr, map);
                        self.builder.build_return(Some(&map.as_basic_value_enum()));

                        self.builder.position_at_end(call_block);
                        fv
                    };

                    let mapptr = self.builder.build_alloca(self.llvmtype(maptype), &varname);
                    self.builder.build_store(
                        mapptr,
                        self.builder
                            .build_call(fv, &[], "")
                            .try_as_basic_value()
                            .unwrap_left(),
                    );
                    self.vars.insert(*i, mapptr);
                } else {
                    panic!()
                }
            }
            crate::parser::StatementType::Free(_, Some(i)) => {
                //todo make function
                let mapptr = self.vars.get(i).unwrap();
                let map = self.builder.build_load(*mapptr, "").into_pointer_value();
                let keys = self
                    .builder
                    .build_struct_gep(map, MAP_KEYS, "keys_ptr")
                    .unwrap();
                self.builder
                    .build_free(self.builder.build_load(keys, "keys").into_pointer_value());
                let states = self
                    .builder
                    .build_struct_gep(map, MAP_STATES, "states_ptr")
                    .unwrap();
                self.builder.build_free(
                    self.builder
                        .build_load(states, "states")
                        .into_pointer_value(),
                );
                let values = self
                    .builder
                    .build_struct_gep(map, MAP_VALUES, "values_ptr")
                    .unwrap();
                self.builder.build_free(
                    self.builder
                        .build_load(values, "values")
                        .into_pointer_value(),
                );
                self.builder.build_free(map);
            }
            crate::parser::StatementType::If(ifpart, ifelsepart, elseblock) => {
                let condblocks: Vec<_> = once_with(|| ifpart)
                    .chain(ifelsepart.iter())
                    .zip(0..)
                    .map(|((_, _), i)| {
                        (
                            self.context.append_basic_block(fv, &format!("if{i}")),
                            self.context.append_basic_block(fv, &format!("if{i}_end")),
                        )
                    })
                    .collect();
                let afterelselable = self.context.append_basic_block(fv, "else_end");
                for ((cond, block), (thenlable, afterthenlable)) in once_with(|| ifpart)
                    .chain(ifelsepart.iter())
                    .zip(condblocks.iter())
                {
                    let cond = self.emit_expression(cond, scopeinfo.clone(), fv);
                    self.builder.build_conditional_branch(
                        cond.into_int_value(),
                        *thenlable,
                        *afterthenlable,
                    );
                    self.builder.position_at_end(*thenlable);
                    self.emit_block(block, fv);
                    if thenlable.get_terminator().is_none() {
                        self.builder.build_unconditional_branch(afterelselable);
                    }
                    self.builder.position_at_end(*afterthenlable);
                }
                self.builder
                    .get_insert_block()
                    .unwrap()
                    .set_name("elseblock");
                self.emit_block(elseblock, fv);
                self.builder.build_unconditional_branch(afterelselable);
                self.builder.position_at_end(afterelselable);
            }
            crate::parser::StatementType::While((cond, block)) => {
                let condlable = self.context.append_basic_block(fv, "whilecond");
                let whilelable = self.context.append_basic_block(fv, "while");
                let afterwhilelable = self.context.append_basic_block(fv, "afterwhile");
                self.builder.build_unconditional_branch(condlable);
                self.builder.position_at_end(condlable);
                self.builder.build_conditional_branch(
                    self.emit_expression(cond, scopeinfo, fv).into_int_value(),
                    whilelable,
                    afterwhilelable,
                );
                self.builder.position_at_end(whilelable);
                self.emit_block(block, fv);
                if whilelable.get_terminator().is_none() {
                    self.builder.build_unconditional_branch(condlable);
                }
                self.builder.position_at_end(afterwhilelable)
            }
            crate::parser::StatementType::Call(id, args, Some(i)) => {
                self.emit_call(id, args, i, scopeinfo, fv);
            }
            crate::parser::StatementType::Return(e) => {
                self.builder
                    .build_return(Some(&self.emit_expression(e, scopeinfo, fv)));
            }
            crate::parser::StatementType::MapCall(id, id2, args, Some(i)) => {
                self.emit_map_call(id, id2, args, i, scopeinfo, fv);
            }
            _ => {
                panic!("unreachable")
            }
        };
    }

    fn emit_expression(
        &mut self,
        expr: &Expression,
        scopeinfo: Rc<RefCell<ScopeInfo>>,
        fv: FunctionValue<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        match expr {
            Expression::Binary(l, b, r, Some(_)) => {
                let lv = self.emit_expression(l, scopeinfo.clone(), fv);
                let rv = self.emit_expression(r, scopeinfo.clone(), fv);
                match (l.get_type(), b, r.get_type()) {
                    (Type::Int, BinOp::Add, Type::Int) => BasicValueEnum::IntValue(
                        self.builder
                            .build_int_add(lv.into_int_value(), rv.into_int_value(), ""),
                    ),
                    (Type::Int, BinOp::Subtract, Type::Int) => BasicValueEnum::IntValue(
                        self.builder
                            .build_int_sub(lv.into_int_value(), rv.into_int_value(), ""),
                    ),
                    (Type::Int, BinOp::Multiply, Type::Int) => BasicValueEnum::IntValue(
                        self.builder
                            .build_int_mul(lv.into_int_value(), rv.into_int_value(), ""),
                    ),

                    (Type::Int, BinOp::Smaller, Type::Int) => {
                        BasicValueEnum::IntValue(self.builder.build_int_compare(
                            inkwell::IntPredicate::SLT,
                            lv.into_int_value(),
                            rv.into_int_value(),
                            "",
                        ))
                    }
                    (Type::Int, BinOp::SmallerEqual, Type::Int) => {
                        BasicValueEnum::IntValue(self.builder.build_int_compare(
                            inkwell::IntPredicate::SLE,
                            lv.into_int_value(),
                            rv.into_int_value(),
                            "",
                        ))
                    }
                    (Type::Int, BinOp::Greater, Type::Int) => {
                        BasicValueEnum::IntValue(self.builder.build_int_compare(
                            inkwell::IntPredicate::SGT,
                            lv.into_int_value(),
                            rv.into_int_value(),
                            "",
                        ))
                    }
                    (Type::Int, BinOp::GreaterEqual, Type::Int) => {
                        BasicValueEnum::IntValue(self.builder.build_int_compare(
                            inkwell::IntPredicate::SGE,
                            lv.into_int_value(),
                            rv.into_int_value(),
                            "",
                        ))
                    }
                    _ => {
                        panic!("should be exhaustive")
                    }
                }
            }

            Expression::Unary(_, _, Some(_)) => todo!(),
            Expression::Value(v, Some(_)) => self.emit_value(v, scopeinfo, fv),
            _ => {
                panic!("expected type info")
            }
        }
    }

    fn emit_value(
        &mut self,
        val: &Value,
        scopeinfo: Rc<RefCell<ScopeInfo>>,
        fv: FunctionValue<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        match val {
            Value::Number(n) => BasicValueEnum::IntValue(
                self.context
                    .i64_type()
                    .const_int((*n).try_into().unwrap(), false),
            ),
            Value::Char(c) => BasicValueEnum::IntValue(
                self.context
                    .i64_type()
                    .const_int((*c as u32).try_into().unwrap(), false),
            ),
            Value::Bool(b) => BasicValueEnum::IntValue(
                self.context
                    .bool_type()
                    .const_int(if *b { 1 } else { 0 }, false),
            ),
            Value::Call(id, args, Some(i)) => self
                .emit_call(id, args, i, scopeinfo, fv)
                .try_as_basic_value()
                .unwrap_left(),
            Value::Identifier(id, Some(_)) => {
                let foundvar = typecheck::find_variable(id, scopeinfo).unwrap();
                self.builder
                    .build_load(*self.vars.get(&foundvar.2).unwrap(), "")
            }
            Value::MapCall(id, id2, exprs, Some(i)) => {
                self.emit_map_call(id, id2, exprs, i, scopeinfo, fv)
            }
            _ => panic!("unreachable"),
        }
    }

    fn emit_call(
        &mut self,
        id: &&str,
        args: &[Expression],
        i: &i32,
        scopeinfo: Rc<RefCell<ScopeInfo>>,
        fv: FunctionValue<'ctx>,
    ) -> CallSiteValue<'ctx> {
        let args: Vec<_> = args
            .iter()
            .map(|expr| {
                BasicMetadataValueEnum::from(self.emit_expression(expr, scopeinfo.clone(), fv))
            })
            .collect();
        if *i == -1 {
            match *id {
                functions::PRINT_INT => self.emit_printf_call(&"%lu", &args),
                functions::PRINT_BOOL => self.emit_printf_call(&{ "%d" }, &args),
                functions::PRINTLN => self.emit_printf_call(&{ "\n" }, &args),
                functions::PRINT_CHAR => self.emit_printf_call(&{ "%c" }, &args),
                _ => {
                    panic!("unknown function: {id}")
                }
            }
        } else {
            self.builder
                .build_call(self.module.get_function(id).unwrap(), &args, "")
        }
    }

    fn emit_map_call(
        &mut self,
        id: &&str,
        id2: &&str,
        args: &[Expression],
        i: &i32,
        scopeinfo: Rc<RefCell<ScopeInfo>>,
        fv: FunctionValue<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        let args: Vec<BasicMetadataValueEnum<'ctx>> = args
            .iter()
            .map(|expr| {
                BasicMetadataValueEnum::from(self.emit_expression(expr, scopeinfo.clone(), fv))
            })
            .collect();
        if let Some((_, Type::Map(k, v), i, _)) = typecheck::find_variable(id, scopeinfo) {
            let llvmkeytype = self.llvmtype(&k);
            let llvmvaluetype = self.llvmtype(&v);
            let maptype = Type::Map(k, v);
            let llvmmaptype = self.llvmtype(&maptype);
            let mapptr = *self.vars.get(&i).unwrap();
            let map = self.builder.build_load(mapptr, id).into_pointer_value();
            let mut allargs: Vec<BasicMetadataValueEnum<'ctx>> = vec![map.into()];
            allargs.extend_from_slice(&args);
            match *id2 {
                functions::SIZE => {
                    let size = self
                        .builder
                        .build_struct_gep(map, MAP_SIZE, &(id.to_string() + ".size"))
                        .unwrap();
                    self.builder.build_load(size, "")
                }
                functions::INSERT => {
                    let fname = format!("{}_insert", &maptype);
                    let fv = if let Some(fv) = self.module.get_function(&fname) {
                        fv
                    } else {
                        const MAP_PARAM: u32 = 0;
                        const KEY_PARAM: u32 = 1;
                        const VALUE_PARAM: u32 = 2;
                        let fv = self.module.add_function(
                            &fname,
                            self.llvmfunctiontype(
                                &Type::Unit,
                                &[llvmmaptype.into(), llvmkeytype.into(), llvmvaluetype.into()],
                                false,
                            ),
                            None,
                        );
                        let call_block = self.builder.get_insert_block().unwrap();
                        self.builder
                            .position_at_end(self.context.append_basic_block(fv, "entry"));

                        /*
                        insert(map, k, v) {
                            if (map.len + 1) > 0.75 * map.capacity {
                                rebuild(map)
                            }
                            i = hash(k) % map.capacity
                            while map.state[i] == TAKEN && map.keys[i] != k {
                                i = (i + 1) % map.capacity
                            }
                            if map.states[i] == FREE {
                                map.size = map.size + 1
                            }
                            map.states[i] = TAKEN
                            map.keys[i] = k
                            map.values[i] = v
                        }
                        */
                        let sizeptr = self
                            .builder
                            .build_struct_gep(
                                fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                                MAP_SIZE,
                                &(id.to_string() + ".size.ptr"),
                            )
                            .unwrap();
                        let size = self.builder.build_load(sizeptr, "size");

                        let capacity = self.builder.build_load(
                            self.builder
                                .build_struct_gep(
                                    fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                                    MAP_CAPACITY,
                                    &(id.to_string() + ".capacity.ptr"),
                                )
                                .unwrap(),
                            "capacity",
                        );

                        let rehashblock = self.context.append_basic_block(fv, "rehash");
                        let afterhash = self.context.append_basic_block(fv, "afterhash");
                        self.builder.build_conditional_branch(
                            self.builder.build_int_compare(
                                inkwell::IntPredicate::UGE,
                                self.builder.build_int_mul(
                                    size.into_int_value(),
                                    self.context.i64_type().const_int(4, false),
                                    "",
                                ),
                                self.builder.build_int_mul(
                                    capacity.into_int_value(),
                                    self.context.i64_type().const_int(3, false),
                                    "",
                                ),
                                "cond",
                            ),
                            rehashblock,
                            afterhash,
                        );

                        self.builder.position_at_end(rehashblock);
                        //todo
                        self.builder.build_unreachable();

                        self.builder.position_at_end(afterhash);

                        //todo hash function
                        let hash = self.builder.build_bitcast(
                            fv.get_nth_param(KEY_PARAM).unwrap(),
                            self.llvmtype(&Type::Int),
                            "hash",
                        );
                        let idx = self.builder.build_alloca(self.context.i64_type(), "idx");
                        self.builder.build_store(
                            idx,
                            self.builder.build_int_unsigned_rem(
                                hash.into_int_value(),
                                capacity.into_int_value(),
                                "",
                            ),
                        );

                        let whilecond = self.context.append_basic_block(fv, "whilecond");
                        self.builder.build_unconditional_branch(whilecond);
                        self.builder.position_at_end(whilecond);

                        let states = self.builder.build_load(
                            self.builder
                                .build_struct_gep(
                                    fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                                    MAP_STATES,
                                    &(id.to_string() + ".states.ptr"),
                                )
                                .unwrap(),
                            "states",
                        );
                        let state = unsafe {
                            self.builder.build_gep(
                                states.into_pointer_value(),
                                &[self.builder.build_load(idx, "").into_int_value()],
                                "",
                            )
                        };
                        self.emit_printf_call(
                            &"STATE = %lu\n",
                            &[self.builder.build_load(state, "state_idx").into()],
                        );

                        let whilecond2 = self.context.append_basic_block(fv, "whilecond2");
                        let whilebody = self.context.append_basic_block(fv, "whilebody");
                        let afterwhile = self.context.append_basic_block(fv, "afterwhile");
                        self.builder.build_conditional_branch(
                            self.builder.build_int_compare(
                                IntPredicate::EQ,
                                self.builder.build_load(state, "state_idx").into_int_value(),
                                self.context.i64_type().const_int(STATE_TAKEN, false),
                                "is_state_taken",
                            ),
                            whilecond2,
                            afterwhile,
                        );
                        self.builder.position_at_end(whilecond2);
                        let keys = self.builder.build_load(
                            self.builder
                                .build_struct_gep(
                                    fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                                    MAP_STATES,
                                    &(id.to_string() + ".keys.ptr"),
                                )
                                .unwrap(),
                            "keys",
                        );
                        let key = unsafe {
                            self.builder.build_gep(
                                keys.into_pointer_value(),
                                &[self.builder.build_load(idx, "").into_int_value()],
                                "",
                            )
                        };
                        self.builder.build_conditional_branch(
                            self.builder.build_int_compare(
                                IntPredicate::NE,
                                self.builder.build_load(key, "keys_idx").into_int_value(),
                                fv.get_nth_param(KEY_PARAM).unwrap().into_int_value(), //todo fix for map type use equal function
                                "is_not_eq_key",
                            ),
                            whilebody,
                            afterwhile,
                        );
                        self.builder.position_at_end(whilebody);
                        self.builder.build_store(
                            idx,
                            self.builder.build_int_add(
                                self.builder.build_load(idx, "").into_int_value(),
                                self.context.i64_type().const_int(1, false),
                                "",
                            ),
                        );
                        self.builder.build_unconditional_branch(whilecond);

                        self.builder.position_at_end(afterwhile);
                        let ifbody = self.context.append_basic_block(fv, "ifbody");
                        let afterif = self.context.append_basic_block(fv, "afterif");
                        self.builder.build_conditional_branch(
                            self.builder.build_int_compare(
                                IntPredicate::EQ,
                                self.builder.build_load(state, "state_idx").into_int_value(),
                                self.context.i64_type().const_int(STATE_FREE, false),
                                "is_state_free",
                            ),
                            ifbody,
                            afterif,
                        );
                        self.builder.position_at_end(ifbody);

                        self.builder.build_store(
                            sizeptr,
                            self.builder.build_int_add(
                                size.into_int_value(),
                                self.context.i64_type().const_int(1, false),
                                "sizeinc",
                            ),
                        );
                        self.emit_printf_call(&"INC SIZE\n", &[]);
                        self.builder.build_unconditional_branch(afterif);
                        self.builder.position_at_end(afterif);

                        // set state key and value
                        self.builder.build_store(
                            unsafe {
                                self.builder.build_gep(
                                    states.into_pointer_value(),
                                    &[self.builder.build_load(idx, "").into_int_value()],
                                    "",
                                )
                            },
                            self.context.i64_type().const_int(STATE_TAKEN, false),
                        );

                        self.builder.build_return(None);
                        self.builder.position_at_end(call_block);
                        fv
                    };
                    self.builder.build_call(fv, &allargs, "");
                    self.context.custom_width_int_type(0).const_zero().into()
                }
                functions::GET => {
                    todo!()
                }
                functions::CLEAR => {
                    todo!()
                }
                _ => {
                    panic!("unreachable")
                }
            }
        } else {
            panic!("should exists")
        }
    }
}
