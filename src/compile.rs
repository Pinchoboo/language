use std::{
    cell::RefCell, collections::HashMap, iter::once_with, path::Path, process::Command, rc::Rc,
};

use inkwell::{
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetTriple},
    types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType, StructType},
    values::{
        BasicMetadataValueEnum, BasicValue, BasicValueEnum, CallSiteValue, FunctionValue,
        PointerValue,
    },
    AddressSpace, IntPredicate, OptimizationLevel,
};

use crate::{
    functions::{self},
    parser::{BinOp, Block, Expression, Program, Statement, Type, Value},
    typecheck::{self, find_structmaptype, find_variable, ScopeInfo},
};
const PRINTF: &str = "printf";
const MEMSET: &str = "memset";
const CALLOC: &str = "calloc";

pub struct Compiler<'ctx, 'a, 'b> {
    pub context: &'ctx Context,
    pub builder: &'a Builder<'ctx>,
    pub module: &'a Module<'ctx>,
    pub vars: HashMap<i32, PointerValue<'ctx>>,
    strings: Rc<RefCell<HashMap<String, PointerValue<'ctx>>>>,
    mapstructs: HashMap<Type<'b>, StructType<'ctx>>,
    structbodies: Vec<(StructType<'ctx>, Vec<BasicTypeEnum<'ctx>>)>,
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
        structbodies: Vec::new(),
    };
    c.compile(program);
}

pub const STRUCT_MAP_SIZE: u32 = 0;
pub const STRUCT_MAP_FLAGS: u32 = 1;

pub const MAP_CAPACITY: u32 = 0;
pub const MAP_SIZE: u32 = 1;
pub const MAP_TOMBS: u32 = 2;
pub const MAP_KEYS: u32 = 3;
pub const MAP_STATES: u32 = 4;
pub const MAP_VALUES: u32 = 5;

pub const STATE_FREE: u64 = 0;
pub const STATE_TAKEN: u64 = 1;
pub const STATE_TOMB: u64 = 2;

impl<'ctx, 'a, 'b> Compiler<'ctx, 'a, 'b> {
    fn llvmstruct(&mut self, t: &Type<'b>, si: Rc<RefCell<ScopeInfo<'b>>>) -> StructType<'ctx> {
        match t {
            Type::Map(k, v) => {
                let struct_name = format!("{t}");
                let capacity = self.context.i64_type();
                let size = self.context.i64_type();
                let tombs = self.context.i64_type();
                let keys = self
                    .llvmtype(k, si.clone())
                    .ptr_type(AddressSpace::default());
                let states = self
                    .llvmtype(&Type::Int, si.clone())
                    .ptr_type(AddressSpace::default());
                let vals = self.llvmtype(v, si).ptr_type(AddressSpace::default());

                *self.mapstructs.entry(t.clone()).or_insert({
                    let st = self.context.opaque_struct_type(&struct_name);
                    st.set_body(
                        &[
                            capacity.into(),
                            size.into(),
                            tombs.into(),
                            keys.into(),
                            states.into(),
                            vals.into(),
                        ],
                        false,
                    );
                    st
                })
            }
            Type::StructMap(id) => {
                let (_, ty, n) = typecheck::find_structmaptype(id, si.clone()).unwrap();
                let struct_name = format!("{t}_{n}");
                let size = self.context.i64_type();

                if !self.mapstructs.contains_key(t) {
                    let st = self.context.opaque_struct_type(&struct_name);
                    self.mapstructs.insert(t.clone(), st);
                    let mut fieldtypes = vec![
                        size.into(),
                        self.llvmtype(&Type::Bool, si.clone())
                            .ptr_type(AddressSpace::default())
                            .into(),
                    ];
                    for (_, t) in ty {
                        fieldtypes.push(self.llvmtype(&t, si.clone()));
                    }
                    st.set_body(&fieldtypes, false);
                }

                *self.mapstructs.get(&t.clone()).unwrap()
            }
            _ => {
                assert!(matches!(t, Type::Map { .. }));
                panic!()
            }
        }
    }

    fn llvmtype(&mut self, t: &Type<'b>, si: Rc<RefCell<ScopeInfo<'b>>>) -> BasicTypeEnum<'ctx> {
        match t {
            Type::Int => self.context.i64_type().as_basic_type_enum(),
            Type::Float => self.context.f64_type().as_basic_type_enum(),
            Type::Bool => self.context.bool_type().as_basic_type_enum(),
            Type::Char => self.context.i64_type().as_basic_type_enum(),
            Type::Unit => self.context.custom_width_int_type(0).as_basic_type_enum(),
            Type::Map(_, _) | Type::StructMap(_) => self
                .llvmstruct(t, si)
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum(),
        }
    }
    fn llvmfunctiontype(
        &mut self,
        t: &Type<'b>,
        si: Rc<RefCell<ScopeInfo<'b>>>,
        param_types: &[BasicMetadataTypeEnum<'ctx>],
        is_var_args: bool,
    ) -> FunctionType<'ctx> {
        match t {
            Type::Int => self.context.i64_type().fn_type(param_types, is_var_args),
            Type::Float => self.context.f64_type().fn_type(param_types, is_var_args),
            Type::Bool => self.context.bool_type().fn_type(param_types, is_var_args),
            Type::Char => self.context.i64_type().fn_type(param_types, is_var_args),
            Type::Unit => self.context.void_type().fn_type(param_types, is_var_args),
            Type::Map(_, _) | Type::StructMap(_) => self
                .llvmstruct(t, si)
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum()
                .fn_type(param_types, is_var_args),
        }
    }

    pub fn compile(&mut self, program: Program<'b>) {
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
            self.module.add_function(
                CALLOC,
                self.context
                    .i8_type()
                    .ptr_type(AddressSpace::default())
                    .fn_type(
                        &[
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
                        .map(|t| self.llvmtype(&t.0, program.scopeinfo.clone()).into())
                        .collect::<Vec<_>>();
                    self.module.add_function(
                        f.identifier,
                        self.llvmfunctiontype(
                            &f.return_type,
                            program.scopeinfo.clone(),
                            params.as_slice(),
                            false,
                        ),
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
                            let p = self
                                .builder
                                .build_alloca(self.llvmtype(t, f.body.scopeinfo.clone()), &varname);
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
        for (st, args) in &self.structbodies {
            st.set_body(args, false);
        }
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
                .arg("-g")
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
            .create_jit_execution_engine(OptimizationLevel::Aggressive)
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

    fn emit_block(&mut self, body: &Block<'b>, fv: FunctionValue<'ctx>) {
        for s in &body.statements {
            self.emit_statement(s, fv, body.scopeinfo.clone());
        }
    }

    fn emit_statement(
        &mut self,
        statement: &Statement<'b>,
        fv: FunctionValue<'ctx>,
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
    ) {
        match &statement.statement {
            crate::parser::StatementType::Assignment(t, id, expr, Some(i)) => {
                let varname = format!("{id}_{i}");
                let pointer = {
                    if t.is_some() {
                        let p = self.builder.build_alloca(
                            self.llvmtype(&(t.as_ref().unwrap().clone()), scopeinfo.clone()),
                            &varname,
                        );
                        self.vars.insert(*i, p);
                        p
                    } else {
                        *self.vars.get(i).unwrap()
                    }
                };
                let value = self.emit_expression(expr, scopeinfo.clone(), fv);
                self.builder.build_store(pointer, value);
            }
            crate::parser::StatementType::Creation(maptype, id, Some(i)) => {
                if let Type::Map(_k, _v) = maptype {
                    let varname = format!("{id}_{i}");
                    let mapptr = self
                        .builder
                        .build_alloca(self.llvmtype(maptype, scopeinfo.clone()), &varname);
                    self.builder.build_store(
                        mapptr,
                        self.builder
                            .build_call(self.mapcreate(maptype, scopeinfo), &[], "")
                            .try_as_basic_value()
                            .unwrap_left(),
                    );
                    self.vars.insert(*i, mapptr);
                } else if let Type::StructMap(_) = maptype {
                    let varname = format!("{id}_{i}");
                    let mapptr = self
                        .builder
                        .build_alloca(self.llvmtype(maptype, scopeinfo.clone()), &varname);
                    self.builder.build_store(
                        mapptr,
                        self.builder
                            .build_call(self.structmapcreate(maptype, scopeinfo), &[], "")
                            .try_as_basic_value()
                            .unwrap_left(),
                    );
                    self.vars.insert(*i, mapptr);
                } else {
                    panic!()
                }
            }
            crate::parser::StatementType::Free(id, Some(i)) => {
                let var = find_variable(id, scopeinfo.clone());
                match var {
                    Some((_, Type::Map(_, _), _, _)) => {
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
					Some((_, Type::StructMap(_), _, _)) => {
						let mapptr = self.vars.get(i).unwrap();
                        let map = self.builder.build_load(*mapptr, "").into_pointer_value();
						self.builder.build_free(map);
					}
                    _ => {
                        panic!("map variable {id} not found")
                    }
                }
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

    fn mapcreate(
        &mut self,
        maptype: &Type<'b>,
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
    ) -> FunctionValue {
        if let Type::Map(k, v) = maptype {
            let fname = format!("create_{maptype}");
            if let Some(fv) = self.module.get_function(&fname) {
                fv
            } else {
                let initial_capacity: u32 = if Type::Unit.eq(k) { 1 } else if Type::Bool.eq(k) {4} else{ 16 };
                let fv = self.module.add_function(
                    &fname,
                    self.llvmfunctiontype(maptype, scopeinfo.clone(), &[], false),
                    None,
                );
                let call_block = self.builder.get_insert_block().unwrap();
                self.builder
                    .position_at_end(self.context.append_basic_block(fv, "entry"));
                let map = self
                    .builder
                    .build_malloc(self.llvmstruct(maptype, scopeinfo.clone()), "map")
                    .unwrap();

                let capacity = self
                    .builder
                    .build_struct_gep(map, MAP_CAPACITY, "map.capacity")
                    .unwrap();
                self.builder.build_store(
                    capacity,
                    self.context
                        .i64_type()
                        .const_int(initial_capacity.into(), false),
                );
                let size = self
                    .builder
                    .build_struct_gep(map, MAP_SIZE, "map.size")
                    .unwrap();
                self.builder
                    .build_store(size, self.context.i64_type().const_int(0, false));

                let tombs = self
                    .builder
                    .build_struct_gep(map, MAP_TOMBS, "map.tombs")
                    .unwrap();
                self.builder
                    .build_store(tombs, self.context.i64_type().const_int(0, false));

                if !Type::Unit.eq(k) {
                    let keys = self
                        .builder
                        .build_struct_gep(map, MAP_KEYS, "map.keys")
                        .unwrap();
                    self.builder.build_store(
                        keys,
                        self.builder.build_bitcast(
                            self.builder
                                .build_malloc(
                                    self.llvmtype(k, scopeinfo.clone())
                                        .array_type(initial_capacity),
                                    "keys_alloc",
                                )
                                .unwrap(),
                            self.llvmtype(k, scopeinfo.clone())
                                .ptr_type(AddressSpace::default()),
                            "keys_ptr",
                        ),
                    );
                }
                let states = self
                    .builder
                    .build_struct_gep(map, MAP_STATES, "map.states")
                    .unwrap();
                let states_alloc = self
                    .builder
                    .build_malloc(
                        self.llvmtype(&Type::Int, scopeinfo.clone())
                            .array_type(initial_capacity),
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
                                self.llvmtype(&Type::Int, scopeinfo.clone())
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
                        self.llvmtype(&Type::Int, scopeinfo.clone())
                            .ptr_type(AddressSpace::default()),
                        "states_ptr",
                    ),
                );

                if !Type::Unit.eq(v) {
                    let values = self
                        .builder
                        .build_struct_gep(map, MAP_VALUES, "map.values")
                        .unwrap();
                    self.builder.build_store(
                        values,
                        self.builder.build_bitcast(
                            self.builder
                                .build_malloc(
                                    self.llvmtype(v, scopeinfo.clone())
                                        .array_type(initial_capacity),
                                    "values_alloc",
                                )
                                .unwrap(),
                            self.llvmtype(v, scopeinfo.clone())
                                .ptr_type(AddressSpace::default()),
                            "values_ptr",
                        ),
                    );
                }

                let mapptr = self
                    .builder
                    .build_alloca(self.llvmtype(maptype, scopeinfo.clone()), "map");
                self.builder.build_store(mapptr, map);
                self.builder.build_return(Some(&map.as_basic_value_enum()));

                self.builder.position_at_end(call_block);
                fv
            }
        } else {
            panic!("{maptype} is not a map");
        }
    }

    fn emit_expression(
        &mut self,
        expr: &Expression,
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
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
                    (Type::Int, BinOp::Equal, Type::Int) => {
                        BasicValueEnum::IntValue(self.builder.build_int_compare(
                            inkwell::IntPredicate::EQ,
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
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
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
                if let Some(foundvar) = typecheck::find_variable(id, scopeinfo.clone()) {
                    self.builder
                        .build_load(*self.vars.get(&foundvar.2).unwrap(), "")
                } else {
                    panic!()
                }
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
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
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
                functions::PRINT_LN => self.emit_printf_call(&{ "\n" }, &args),
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
        _i: &i32,
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
        fv: FunctionValue<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        let var = typecheck::find_variable(id, scopeinfo.clone());
        if let Some((_, Type::Map(k, v), i, _)) = var {
            let llvmkeytype = self.llvmtype(&k, scopeinfo.clone());
            let llvmvaluetype = self.llvmtype(&v, scopeinfo.clone());
            let maptype = Type::Map(k.clone(), v.clone());
            let llvmmaptype = self.llvmtype(&maptype, scopeinfo.clone());
            let mapptr = *self.vars.get(&i).unwrap();
            let map = self.builder.build_load(mapptr, id).into_pointer_value();
            let mut allargs: Vec<BasicMetadataValueEnum<'ctx>> = vec![map.into()];
            let args: Vec<BasicMetadataValueEnum<'ctx>> = args
                .iter()
                .map(|expr| {
                    BasicMetadataValueEnum::from(self.emit_expression(expr, scopeinfo.clone(), fv))
                })
                .collect();
            allargs.extend_from_slice(&args);
            match *id2 {
                functions::SIZE => {
                    let size = self
                        .builder
                        .build_struct_gep(map, MAP_SIZE, &(id.to_string() + ".size"))
                        .unwrap();
                    self.builder.build_load(size, "")
                }
                functions::CAPACITY => {
                    let capacity = self
                        .builder
                        .build_struct_gep(map, MAP_CAPACITY, &(id.to_string() + ".capacity"))
                        .unwrap();
                    self.builder.build_load(capacity, "")
                }
                functions::TOMBS => {
                    let tombs = self
                        .builder
                        .build_struct_gep(map, MAP_TOMBS, &(id.to_string() + ".tombs"))
                        .unwrap();
                    self.builder.build_load(tombs, "")
                }
                functions::INSERT => {
                    self.builder
                        .build_call(self.mapinsert(&maptype, scopeinfo), &allargs, "");
                    self.context.custom_width_int_type(0).const_zero().into()
                }
                functions::GET => {
                    let fname = format!("{}_get", &maptype);
                    let fv = if let Some(fv) = self.module.get_function(&fname) {
                        fv
                    } else {
                        const MAP_PARAM: u32 = 0;
                        const KEY_PARAM: u32 = 1;
                        let param_types = if Type::Unit.ne(&k) {
                            vec![llvmmaptype.into(), llvmkeytype.into()]
                        } else {
                            vec![llvmmaptype.into()]
                        };
                        let fv = self.module.add_function(
                            &fname,
                            self.llvmfunctiontype(&v, scopeinfo.clone(), &param_types, false),
                            None,
                        );
                        let call_block = self.builder.get_insert_block().unwrap();
                        self.builder
                            .position_at_end(self.context.append_basic_block(fv, "entry"));
                        /*
                        get(map, k) {
                            IF V == UNIT {
                                return
                            }
                            IF K == UNIT {
                                return map.values[0]
                            }
                            i = hash(k) % map.capacity
                            while map.state[i] != FREE {
                                if map.state[i] == TAKEN && map.keys[i] == k {
                                    return map.values[i]
                                }
                                i = (i + 1) % map.capacity
                            }
                            return null
                        }
                        */

                        if Type::Unit.eq(&v) {
                            self.builder.build_return(None);
                        } else if Type::Unit.eq(&k) {
                            self.builder.build_return(Some(&self.builder.build_load(
                                unsafe {
                                    self.builder.build_gep(
                                        self.builder
                                            .build_load(
                                                self.builder
                                                    .build_struct_gep(
                                                        fv.get_nth_param(MAP_PARAM)
                                                            .unwrap()
                                                            .into_pointer_value(),
                                                        MAP_VALUES,
                                                        &(id.to_string() + ".values.ptr"),
                                                    )
                                                    .unwrap(),
                                                "values",
                                            )
                                            .into_pointer_value(),
                                        &[self.context.i64_type().const_zero()],
                                        "",
                                    )
                                },
                                "",
                            )));
                        } else {
                            let hash = self
                                .builder
                                .build_call(
                                    self.hash(&k, scopeinfo.clone()),
                                    &[fv.get_nth_param(KEY_PARAM).unwrap().into()],
                                    "",
                                )
                                .try_as_basic_value()
                                .unwrap_left();
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

                            let keys = self.builder.build_load(
                                self.builder
                                    .build_struct_gep(
                                        fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                                        MAP_KEYS,
                                        &(id.to_string() + ".keys.ptr"),
                                    )
                                    .unwrap(),
                                "keys",
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
                            let whilebody = self.context.append_basic_block(fv, "whilebody");
                            let afterwhile = self.context.append_basic_block(fv, "afterwhile");

                            self.builder.build_unconditional_branch(whilecond);
                            self.builder.position_at_end(whilecond);

                            let state = unsafe {
                                self.builder.build_gep(
                                    states.into_pointer_value(),
                                    &[self.builder.build_load(idx, "").into_int_value()],
                                    "",
                                )
                            };

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
                                    self.builder.build_load(state, "state_idx").into_int_value(),
                                    self.context.i64_type().const_int(STATE_FREE, false),
                                    "is_not_state_free",
                                ),
                                whilebody,
                                afterwhile,
                            );
                            self.builder.position_at_end(whilebody);

                            //if
                            let ifbody = self.context.append_basic_block(fv, "ifbody");
                            let afterif = self.context.append_basic_block(fv, "afterif");

                            self.builder.build_conditional_branch(
                                self.builder.build_and(
                                    self.builder.build_int_compare(
                                        IntPredicate::EQ,
                                        self.builder
                                            .build_load(state, "state_idx")
                                            .into_int_value(),
                                        self.context.i64_type().const_int(STATE_TAKEN, false),
                                        "is_state_taken",
                                    ),
                                    self.builder.build_int_compare(
                                        IntPredicate::EQ,
                                        self.builder.build_load(key, "key_idx").into_int_value(),
                                        fv.get_nth_param(KEY_PARAM).unwrap().into_int_value(),
                                        "is_key_equal",
                                    ),
                                    "ifcond",
                                ),
                                ifbody,
                                afterif,
                            );
                            self.builder.position_at_end(ifbody);
                            self.builder.build_return(Some(&self.builder.build_load(
                                unsafe {
                                    self.builder.build_gep(
                                        self.builder
                                            .build_load(
                                                self.builder
                                                    .build_struct_gep(
                                                        fv.get_nth_param(MAP_PARAM)
                                                            .unwrap()
                                                            .into_pointer_value(),
                                                        MAP_VALUES,
                                                        &(id.to_string() + ".values.ptr"),
                                                    )
                                                    .unwrap(),
                                                "values",
                                            )
                                            .into_pointer_value(),
                                        &[self.builder.build_load(idx, "").into_int_value()],
                                        "",
                                    )
                                },
                                "",
                            )));
                            self.builder.position_at_end(afterif);

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
                            self.emit_printf_call(&"KEY NOT IN MAP\n", &[]);
                            self.builder.build_return(Some(
                                &self.llvmtype(&Type::Int, scopeinfo).const_zero(),
                            ));
                        }
                        self.builder.position_at_end(call_block);
                        fv
                    };
                    self.builder
                        .build_call(fv, &allargs, "")
                        .try_as_basic_value()
                        .unwrap_left()
                }
                functions::CLEAR => {
                    /*
                    clear(map) {
                        map.capacity = 16
                        map.size = 0
                        map.tombs = 0
                        free map.keys
                        map.key = alloc [16 * K]
                        free map.vals
                        map.vals = alloc [16 * v]
                        free map.states
                        map.states = alloc [16 * _]
                    }
                    */
                    let fname = format!("{}_clear", &maptype);
                    let fv = if let Some(fv) = self.module.get_function(&fname) {
                        fv
                    } else {
                        let initial_capacity: u32 = if Type::Unit.eq(&k) { 1 } else if Type::Bool.eq(&k) {4} else{ 16 };
                        let fv = self.module.add_function(
                            &fname,
                            self.llvmfunctiontype(
                                &Type::Unit,
                                scopeinfo,
                                &[llvmmaptype.into()],
                                false,
                            ),
                            None,
                        );
                        let call_location = self.builder.get_insert_block().unwrap();
                        self.builder
                            .position_at_end(self.context.append_basic_block(fv, "entry"));

                        let map = fv.get_nth_param(0).unwrap().into_pointer_value();
                        self.builder.build_store(
                            self.builder
                                .build_struct_gep(map, MAP_CAPACITY, "capacity")
                                .unwrap(),
                            self.context
                                .i64_type()
                                .const_int(initial_capacity.into(), false),
                        );

                        self.builder.build_store(
                            self.builder
                                .build_struct_gep(map, MAP_SIZE, "size")
                                .unwrap(),
                            self.context.i64_type().const_zero(),
                        );
                        self.builder.build_store(
                            self.builder
                                .build_struct_gep(map, MAP_TOMBS, "tombs")
                                .unwrap(),
                            self.context.i64_type().const_zero(),
                        );

                        if Type::Unit.ne(&k) {
                            let keyptr = self
                                .builder
                                .build_struct_gep(map, MAP_KEYS, "keys.ptr")
                                .unwrap();
                            let keys = self.builder.build_load(keyptr, "keys");
                            self.builder.build_free(keys.into_pointer_value());
                            self.builder.build_store(
                                keyptr,
                                self.builder
                                    .build_array_malloc(
                                        llvmkeytype,
                                        self.context
                                            .i32_type()
                                            .const_int(initial_capacity.into(), false),
                                        "",
                                    )
                                    .unwrap(),
                            );
                        }
                        if Type::Unit.ne(&v) {
                            let valuesptr = self
                                .builder
                                .build_struct_gep(map, MAP_VALUES, "values.ptr")
                                .unwrap();
                            let values = self.builder.build_load(valuesptr, "values");
                            self.builder.build_free(values.into_pointer_value());
                            self.builder.build_store(
                                valuesptr,
                                self.builder
                                    .build_array_malloc(
                                        llvmvaluetype,
                                        self.context
                                            .i32_type()
                                            .const_int(initial_capacity.into(), false),
                                        "",
                                    )
                                    .unwrap(),
                            );
                        }
                        let statessptr = self
                            .builder
                            .build_struct_gep(map, MAP_STATES, "states.ptr")
                            .unwrap();
                        let states = self.builder.build_load(statessptr, "states");
                        self.builder.build_free(states.into_pointer_value());
                        self.builder.build_store(
                            statessptr,
                            self.emit_calloc(
                                self.context.i64_type(),
                                self.context
                                    .i32_type()
                                    .const_int(initial_capacity.into(), false)
                                    .into(),
                            ),
                        );

                        self.builder.build_return(None);
                        self.builder.position_at_end(call_location);
                        fv
                    };
                    self.builder.build_call(fv, &[map.into()], "");
                    self.context.custom_width_int_type(0).const_zero().into()
                }
                functions::REMOVE => {
                    /*
                    remove(map, k) {
                        IF K == UNIT {
                            if map.size == 1{
                                map.size = map.size - 1
                                map.tombs = map.tombs + 1
                                map.states[0] = TOMB
                            }
                            return
                        }

                        i = hash(k) % map.capacity
                        while map.state[i] != FREE {
                            if map.state[i] == TOMB {
                                break
                            }
                            if map.keys[i] == k {
                                map.states[i] = TOMB
                                map.tombs = map.tombs + 1
                                map.size = map.size - 1
                                return null
                            }
                            i = (i + 1) % map.capacity
                        }
                        return null
                    }
                    */
                    let fname = format!("{}_remove", &maptype);
                    let fv = if let Some(fv) = self.module.get_function(&fname) {
                        fv
                    } else {
                        const MAP_PARAM: u32 = 0;
                        const KEY_PARAM: u32 = 1;
                        let param_types = if Type::Unit.ne(&k) {
                            vec![llvmmaptype.into(), llvmkeytype.into()]
                        } else {
                            vec![llvmmaptype.into()]
                        };
                        let fv = self.module.add_function(
                            &fname,
                            self.llvmfunctiontype(
                                &Type::Unit,
                                scopeinfo.clone(),
                                &param_types,
                                false,
                            ),
                            None,
                        );
                        let call_block = self.builder.get_insert_block().unwrap();
                        self.builder
                            .position_at_end(self.context.append_basic_block(fv, "entry"));
                        let tombsptr = self
                            .builder
                            .build_struct_gep(
                                fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                                MAP_TOMBS,
                                &(id.to_string() + ".tombs.ptr"),
                            )
                            .unwrap();
                        let tombs = self.builder.build_load(tombsptr, "tombs");
                        let sizeptr = self
                            .builder
                            .build_struct_gep(
                                fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                                MAP_SIZE,
                                &(id.to_string() + ".size.ptr"),
                            )
                            .unwrap();
                        let size = self.builder.build_load(sizeptr, "size");
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

                        if Type::Unit.eq(&k) {
                            let ifbody = self.context.append_basic_block(fv, "ifbody");
                            let afterif = self.context.append_basic_block(fv, "afterif");
                            self.builder.build_conditional_branch(
                                self.builder.build_int_compare(
                                    IntPredicate::EQ,
                                    size.into_int_value(),
                                    self.context.i64_type().const_int(1, false),
                                    "",
                                ),
                                ifbody,
                                afterif,
                            );
                            self.builder.position_at_end(ifbody);

                            self.builder.build_store(
                                tombsptr,
                                self.builder.build_int_add(
                                    tombs.into_int_value(),
                                    self.context.i64_type().const_int(1, false),
                                    "tombsincr",
                                ),
                            );
                            self.builder.build_store(
                                sizeptr,
                                self.builder.build_int_sub(
                                    size.into_int_value(),
                                    self.context.i64_type().const_int(1, false),
                                    "sizedecr",
                                ),
                            );

                            self.builder.build_store(
                                unsafe {
                                    self.builder.build_gep(
                                        states.into_pointer_value(),
                                        &[self.context.i64_type().const_zero()],
                                        "",
                                    )
                                },
                                self.context.i64_type().const_int(STATE_TOMB, false),
                            );
                            self.builder.build_unconditional_branch(afterif);
                            self.builder.position_at_end(afterif)
                        } else {
                            let hashargs = if Type::Unit.ne(&k) {
                                vec![fv.get_nth_param(KEY_PARAM).unwrap().into()]
                            } else {
                                vec![]
                            };
                            let hash = self
                                .builder
                                .build_call(self.hash(&k, scopeinfo), &hashargs, "")
                                .try_as_basic_value()
                                .unwrap_left();

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

                            let keys = self.builder.build_load(
                                self.builder
                                    .build_struct_gep(
                                        fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                                        MAP_KEYS,
                                        &(id.to_string() + ".keys.ptr"),
                                    )
                                    .unwrap(),
                                "keys",
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
                            let whilebody = self.context.append_basic_block(fv, "whilebody");
                            let afterwhile = self.context.append_basic_block(fv, "afterwhile");

                            self.builder.build_unconditional_branch(whilecond);
                            self.builder.position_at_end(whilecond);

                            let state = unsafe {
                                self.builder.build_gep(
                                    states.into_pointer_value(),
                                    &[self.builder.build_load(idx, "").into_int_value()],
                                    "",
                                )
                            };

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
                                    self.builder.build_load(state, "state_idx").into_int_value(),
                                    self.context.i64_type().const_int(STATE_FREE, false),
                                    "is_not_state_free",
                                ),
                                whilebody,
                                afterwhile,
                            );
                            self.builder.position_at_end(whilebody);

                            let noearlyescape =
                                self.context.append_basic_block(fv, "noearlyescape");
                            self.builder.build_conditional_branch(
                                self.builder.build_int_compare(
                                    IntPredicate::EQ,
                                    self.builder.build_load(state, "state_idx").into_int_value(),
                                    self.context.i64_type().const_int(STATE_TOMB, false),
                                    "is_state_equal_tomb",
                                ),
                                afterwhile,
                                noearlyescape,
                            );
                            self.builder.position_at_end(noearlyescape);

                            //if
                            let ifbody = self.context.append_basic_block(fv, "ifbody");
                            let afterif = self.context.append_basic_block(fv, "afterif");

                            self.builder.build_conditional_branch(
                                self.builder.build_int_compare(
                                    IntPredicate::EQ,
                                    self.builder.build_load(key, "key_idx").into_int_value(),
                                    fv.get_nth_param(KEY_PARAM).unwrap().into_int_value(),
                                    "is_key_equal",
                                ),
                                ifbody,
                                afterif,
                            );
                            self.builder.position_at_end(ifbody);

                            self.builder.build_store(
                                unsafe {
                                    self.builder.build_gep(
                                        states.into_pointer_value(),
                                        &[self.builder.build_load(idx, "").into_int_value()],
                                        "",
                                    )
                                },
                                self.context.i64_type().const_int(STATE_TOMB, false),
                            );
                            self.builder.build_store(
                                tombsptr,
                                self.builder.build_int_add(
                                    tombs.into_int_value(),
                                    self.context.i64_type().const_int(1, false),
                                    "tombsincr",
                                ),
                            );
                            self.builder.build_store(
                                sizeptr,
                                self.builder.build_int_sub(
                                    size.into_int_value(),
                                    self.context.i64_type().const_int(1, false),
                                    "sizedecr",
                                ),
                            );

                            self.builder.build_return(None);
                            self.builder.position_at_end(afterif);

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
                            self.emit_printf_call(&"KEY NOT IN MAP\n", &[]);
                        }
                        self.builder.build_return(None);
                        self.builder.position_at_end(call_block);
                        fv
                    };
                    self.builder.build_call(fv, &allargs, "");
                    self.context.custom_width_int_type(0).const_zero().into()
                }
                functions::GET_MAYBE => {
                    let fname = format!("{}_get_maybe", &maptype);
                    let fv = if let Some(fv) = self.module.get_function(&fname) {
                        fv
                    } else {
                        const MAP_PARAM: u32 = 0;
                        const KEY_PARAM: u32 = 1;
                        let returntype = Type::Map(Box::new(Type::Unit), v.clone());
                        let param_types = if Type::Unit.ne(&k) {
                            vec![llvmmaptype.into(), llvmkeytype.into()]
                        } else {
                            vec![llvmmaptype.into()]
                        };
                        let fv = self.module.add_function(
                            &fname,
                            self.llvmfunctiontype(
                                &returntype,
                                scopeinfo.clone(),
                                &param_types,
                                false,
                            ),
                            None,
                        );
                        let call_block = self.builder.get_insert_block().unwrap();
                        self.builder
                            .position_at_end(self.context.append_basic_block(fv, "entry"));
                        /*
                        getMaybe(map, k) {
                            i = hash(k) % map.capacity
                            returnval = new <void,V>
                            IF K == UNIT {
                                if map.size == 1 {
                                    returnval.insert(map.values[0])
                                }
                                return returval
                            }
                            while map.state[i] != FREE {
                                if map.state[i] == TAKEN && map.keys[i] == k {
                                    returnval.insert(map.values[i])
                                    break
                                }
                                i = (i + 1) % map.capacity
                            }
                            return returnval
                        }
                        */
                        let returnvalptr = self.builder.build_alloca(
                            self.llvmtype(&returntype, scopeinfo.clone()),
                            "returnvalptr",
                        );
                        self.builder.build_store(
                            returnvalptr,
                            self.builder
                                .build_call(self.mapcreate(&returntype, scopeinfo.clone()), &[], "")
                                .try_as_basic_value()
                                .unwrap_left(),
                        );
                        let returnval = self.builder.build_load(returnvalptr, "returnval");

                        if Type::Unit.eq(&k) {
                            let sizeptr = self
                                .builder
                                .build_struct_gep(
                                    fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                                    MAP_SIZE,
                                    &(id.to_string() + ".size.ptr"),
                                )
                                .unwrap();
                            let size = self.builder.build_load(sizeptr, "size");

                            let ifbody = self.context.append_basic_block(fv, "ifbody");
                            let afterif = self.context.append_basic_block(fv, "afterif");
                            self.builder.build_conditional_branch(
                                self.builder.build_int_compare(
                                    IntPredicate::EQ,
                                    size.into_int_value(),
                                    self.context.i64_type().const_int(1, false),
                                    "",
                                ),
                                ifbody,
                                afterif,
                            );
                            self.builder.position_at_end(ifbody);

                            let insertargs = if Type::Unit.ne(&v) {
                                let value = self.builder.build_load(
                                    unsafe {
                                        self.builder.build_gep(
                                            self.builder
                                                .build_load(
                                                    self.builder
                                                        .build_struct_gep(
                                                            fv.get_nth_param(MAP_PARAM)
                                                                .unwrap()
                                                                .into_pointer_value(),
                                                            MAP_VALUES,
                                                            &(id.to_string() + ".values.ptr"),
                                                        )
                                                        .unwrap(),
                                                    "values",
                                                )
                                                .into_pointer_value(),
                                            &[self.context.i64_type().const_zero()],
                                            "value_0ptr",
                                        )
                                    },
                                    "value_0",
                                );
                                vec![returnval.into(), value.into()]
                            } else {
                                vec![returnval.into()]
                            };
                            self.builder.build_call(
                                self.mapinsert(&returntype, scopeinfo.clone()),
                                &insertargs,
                                "",
                            );

                            self.builder.build_unconditional_branch(afterif);
                            self.builder.position_at_end(afterif)
                        } else {
                            let hash = self
                                .builder
                                .build_call(
                                    self.hash(&k, scopeinfo.clone()),
                                    &[fv.get_nth_param(KEY_PARAM).unwrap().into()],
                                    "",
                                )
                                .try_as_basic_value()
                                .unwrap_left();

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

                            let keys = self.builder.build_load(
                                self.builder
                                    .build_struct_gep(
                                        fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                                        MAP_KEYS,
                                        &(id.to_string() + ".keys.ptr"),
                                    )
                                    .unwrap(),
                                "keys",
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
                            let whilebody = self.context.append_basic_block(fv, "whilebody");
                            let afterwhile = self.context.append_basic_block(fv, "afterwhile");

                            self.builder.build_unconditional_branch(whilecond);
                            self.builder.position_at_end(whilecond);

                            let state = unsafe {
                                self.builder.build_gep(
                                    states.into_pointer_value(),
                                    &[self.builder.build_load(idx, "").into_int_value()],
                                    "",
                                )
                            };

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
                                    self.builder.build_load(state, "state_idx").into_int_value(),
                                    self.context.i64_type().const_int(STATE_FREE, false),
                                    "is_not_state_free",
                                ),
                                whilebody,
                                afterwhile,
                            );
                            self.builder.position_at_end(whilebody);

                            //if
                            let ifbody = self.context.append_basic_block(fv, "ifbody");
                            let afterif = self.context.append_basic_block(fv, "afterif");

                            self.builder.build_conditional_branch(
                                self.builder.build_and(
                                    self.builder.build_int_compare(
                                        IntPredicate::EQ,
                                        self.builder
                                            .build_load(state, "state_idx")
                                            .into_int_value(),
                                        self.context.i64_type().const_int(STATE_TAKEN, false),
                                        "is_state_taken",
                                    ),
                                    self.builder.build_int_compare(
                                        IntPredicate::EQ,
                                        self.builder.build_load(key, "key_idx").into_int_value(),
                                        fv.get_nth_param(KEY_PARAM).unwrap().into_int_value(),
                                        "is_key_equal",
                                    ),
                                    "ifcond",
                                ),
                                ifbody,
                                afterif,
                            );
                            self.builder.position_at_end(ifbody);
                            let insertargs = if Type::Unit.ne(&v) {
                                let value = self.builder.build_load(
                                    unsafe {
                                        self.builder.build_gep(
                                            self.builder
                                                .build_load(
                                                    self.builder
                                                        .build_struct_gep(
                                                            fv.get_nth_param(MAP_PARAM)
                                                                .unwrap()
                                                                .into_pointer_value(),
                                                            MAP_VALUES,
                                                            &(id.to_string() + ".values.ptr"),
                                                        )
                                                        .unwrap(),
                                                    "values",
                                                )
                                                .into_pointer_value(),
                                            &[self.builder.build_load(idx, "").into_int_value()],
                                            "",
                                        )
                                    },
                                    "",
                                );
                                vec![returnval.into(), value.into()]
                            } else {
                                vec![returnval.into()]
                            };
                            self.builder.build_call(
                                self.mapinsert(&returntype, scopeinfo.clone()),
                                &insertargs,
                                "",
                            );

                            self.builder.build_unconditional_branch(afterwhile);
                            self.builder.position_at_end(afterif);

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
                        }
                        self.builder.build_return(Some(&returnval));
                        self.builder.position_at_end(call_block);
                        fv
                    };
                    self.builder
                        .build_call(fv, &allargs, "")
                        .try_as_basic_value()
                        .unwrap_left()
                }
                _ => {
                    panic!("unreachable")
                }
            }
        } else if let Some((_, Type::StructMap(maptype), i, _)) = var {
            let smt = typecheck::find_structmaptype(maptype, scopeinfo.clone()).expect("exists");
            let maptype = Type::StructMap(maptype);
            let _llvmmaptype = self.llvmtype(&maptype, scopeinfo.clone());
            let mapptr = *self.vars.get(&i).unwrap();
            let map = self.builder.build_load(mapptr, id).into_pointer_value();
            let mut allargs: Vec<BasicMetadataValueEnum<'ctx>> = vec![map.into()];
            let mut idx = None;
            allargs.extend(args.iter().filter_map(|expr| {
                if let Expression::Value(Value::Identifier(id, _), _) = expr {
                    if let Some((p, _)) = smt.1.iter().enumerate().find(|(_, (s, _))| s.eq(id)) {
                        idx = Some(p as u64);
                        return None;
                    }
                }
                return Some(BasicMetadataValueEnum::from(self.emit_expression(
                    expr,
                    scopeinfo.clone(),
                    fv,
                )));
            }));

            match *id2 {
                functions::SIZE => {
                    let size = self
                        .builder
                        .build_struct_gep(map, STRUCT_MAP_SIZE, &(id.to_string() + ".size"))
                        .unwrap();
                    self.builder.build_load(size, "")
                }
                functions::CAPACITY => self
                    .context
                    .i64_type()
                    .const_int(smt.1.len() as u64, false)
                    .into(),
                functions::TOMBS => self.context.i64_type().const_zero().into(),
                functions::CLEAR => {
                    todo!()
                }
                functions::INSERT => {
                    self.builder.build_call(
                        self.mapstructinsert(&maptype, scopeinfo.clone(), idx.unwrap()),
                        &allargs,
                        "",
                    );
                    self.context.custom_width_int_type(0).const_zero().into()
                }
                functions::REMOVE => {
                    self.builder.build_call(
                        self.mapstructremove(&maptype, scopeinfo.clone(), idx.unwrap()),
                        &allargs,
                        "",
                    );
                    self.context.custom_width_int_type(0).const_zero().into()
                }
                functions::GET => {
                    let index = idx.unwrap();
                    let fname = format!("{}_get_{index}", &maptype);
                    let fv = if let Some(fv) = self.module.get_function(&fname) {
                        fv
                    } else {
                        let v = smt.1.get(index as usize).unwrap().1.clone();
                        let params: Vec<BasicMetadataTypeEnum> =
                            vec![self.llvmtype(&maptype, scopeinfo.clone()).into()];
                        /*
                        fn mapstructget<K>(){
                            return map.values[i]
                        }
                        */
                        let fv = self.module.add_function(
                            &fname,
                            self.llvmfunctiontype(&v, scopeinfo.clone(), &params, false),
                            None,
                        );
                        let call_block = self.builder.get_insert_block().unwrap();
                        self.builder
                            .position_at_end(self.context.append_basic_block(fv, "entry"));
                        self.builder.build_return(Some(
                            &self.builder.build_load(
                                self.builder
                                    .build_struct_gep(
                                        fv.get_first_param().unwrap().into_pointer_value(),
                                        2 + index as u32,
                                        "",
                                    )
                                    .unwrap(),
                                "",
                            ),
                        ));
                        self.builder.position_at_end(call_block);
                        fv
                    };
                    self.builder
                        .build_call(fv, &allargs, "")
                        .try_as_basic_value()
                        .unwrap_left()
                }
                functions::GET_MAYBE => {
                    let index = idx.unwrap();
                    let fname = format!("{}_get_maybe_{index}", &maptype);
                    let fv = if let Some(fv) = self.module.get_function(&fname) {
                        fv
                    } else {
                        let v = smt.1.get(index as usize).unwrap().1.clone();
                        let returntype = Type::Map(Box::new(Type::Unit), Box::new(v.clone()));
                        let params: Vec<BasicMetadataTypeEnum> =
                            vec![self.llvmtype(&maptype, scopeinfo.clone()).into()];
                        /*
                        fn mapstructgetmaybe<K>(){
                            new <void,V> r
                            if map.states[i] == taken {
                                r.insert(map.values[i])
                            }
                            return r
                        }
                        */
                        let fv = self.module.add_function(
                            &fname,
                            self.llvmfunctiontype(&returntype, scopeinfo.clone(), &params, false),
                            None,
                        );
                        let call_block = self.builder.get_insert_block().unwrap();
                        self.builder
                            .position_at_end(self.context.append_basic_block(fv, "entry"));

                        let returnvalptr = self.builder.build_alloca(
                            self.llvmtype(&returntype, scopeinfo.clone()),
                            "returnvalptr",
                        );

                        self.builder.build_store(
                            returnvalptr,
                            self.builder
                                .build_call(self.mapcreate(&returntype, scopeinfo.clone()), &[], "")
                                .try_as_basic_value()
                                .unwrap_left(),
                        );
                        let returnval = self.builder.build_load(returnvalptr, "returnval");

                        let ifbody = self.context.append_basic_block(fv, "ifbody");
                        let afterif = self.context.append_basic_block(fv, "afterif");

                        let flags = self
                            .builder
                            .build_load(
                                self.builder
                                    .build_struct_gep(
                                        fv.get_nth_param(0).unwrap().into_pointer_value(),
                                        STRUCT_MAP_FLAGS,
                                        "",
                                    )
                                    .unwrap(),
                                "map.states",
                            )
                            .into_pointer_value();
                        let flagi = unsafe {
                            self.builder.build_gep(
                                flags,
                                &[self.context.i64_type().const_int(index, false)],
                                "map.states_i",
                            )
                        };
                        self.builder.build_conditional_branch(
                            self.builder.build_int_compare(
                                IntPredicate::EQ,
                                self.builder.build_load(flagi, "").into_int_value(),
                                self.context.bool_type().const_all_ones(),
                                "is_taken",
                            ),
                            ifbody,
                            afterif,
                        );
                        self.builder.position_at_end(ifbody);
                        let insertargs = if Type::Unit.ne(&v) {
                            let value = self.builder.build_load(
                                self.builder
                                    .build_struct_gep(
                                        fv.get_nth_param(0).unwrap().into_pointer_value(),
                                        2 + index as u32,
                                        &(id.to_string() + ".values.ptr"),
                                    )
                                    .unwrap(),
                                "values",
                            );
                            vec![returnval.into(), value.into()]
                        } else {
                            vec![returnval.into()]
                        };
                        self.builder.build_call(
                            self.mapinsert(&returntype, scopeinfo.clone()),
                            &insertargs,
                            "",
                        );
                        self.builder.build_unconditional_branch(afterif);
                        self.builder.position_at_end(afterif);

                        self.builder.build_return(Some(&returnval));
                        self.builder.position_at_end(call_block);
                        fv
                    };
                    self.builder
                        .build_call(fv, &allargs, "")
                        .try_as_basic_value()
                        .unwrap_left()
                }
                _ => {
                    todo!()
                }
            }
        } else {
            panic!("should exists")
        }
    }

    fn mapstructinsert(
        &mut self,
        maptype: &Type<'b>,
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
        index: u64,
    ) -> FunctionValue {
        let fname = format!("{}_insert_{index}", &maptype);
        if let Some(fv) = self.module.get_function(&fname) {
            fv
        } else if let Type::StructMap(smt) = maptype {
            let smt = find_structmaptype(smt, scopeinfo.clone()).expect("exist bc typecheck");
            let v = smt.1.get(index as usize).unwrap().1.clone();
            let params: Vec<BasicMetadataTypeEnum> = if v == Type::Unit {
                vec![self.llvmtype(maptype, scopeinfo.clone()).into()]
            } else {
                vec![
                    self.llvmtype(maptype, scopeinfo.clone()).into(),
                    self.llvmtype(&v, scopeinfo.clone()).into(),
                ]
            };
            const MAP_PARAM: u32 = 0;
            const VALUE_PARAM: u32 = 1;
            /*
            fn mapstructinsert<K>(v){
                if map.states[i] != TAKEN {
                    map.size = map.size + 1
                }
                map.states[i] = TAKEN
                IF V NOT UNIT{
                    map.values[i] = v
                }
            }
            */
            let fv = self.module.add_function(
                &fname,
                self.llvmfunctiontype(&Type::Unit, scopeinfo.clone(), &params, false),
                None,
            );
            let call_block = self.builder.get_insert_block().unwrap();
            self.builder
                .position_at_end(self.context.append_basic_block(fv, "entry"));

            let ifbody = self.context.append_basic_block(fv, "ifbody");
            let afterif = self.context.append_basic_block(fv, "afterif");

            let flags = self
                .builder
                .build_load(
                    self.builder
                        .build_struct_gep(
                            fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                            STRUCT_MAP_FLAGS,
                            "",
                        )
                        .unwrap(),
                    "map.states",
                )
                .into_pointer_value();
            let flagi = unsafe {
                self.builder.build_gep(
                    flags,
                    &[self.context.i64_type().const_int(index, false)],
                    "map.states_i",
                )
            };
            self.builder.build_conditional_branch(
                self.builder.build_int_compare(
                    IntPredicate::NE,
                    self.builder.build_load(flagi, "").into_int_value(),
                    self.context.bool_type().const_all_ones(),
                    "is_taken",
                ),
                ifbody,
                afterif,
            );
            self.builder.position_at_end(ifbody);
            let size = self
                .builder
                .build_struct_gep(
                    fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                    STRUCT_MAP_SIZE,
                    "map.size",
                )
                .unwrap();
            self.builder.build_store(
                size,
                self.builder.build_int_add(
                    self.builder.build_load(size, "").into_int_value(),
                    self.context.i64_type().const_int(1, false),
                    "",
                ),
            );
            self.builder.build_unconditional_branch(afterif);
            self.builder.position_at_end(afterif);
            self.builder
                .build_store(flagi, self.context.bool_type().const_all_ones());
            if v.ne(&Type::Unit) {
                self.builder.build_store(
                    self.builder
                        .build_struct_gep(
                            fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                            2 + index as u32,
                            "",
                        )
                        .unwrap(),
                    fv.get_nth_param(VALUE_PARAM).unwrap(),
                );
            }

            self.builder.build_return(None);
            self.builder.position_at_end(call_block);
            fv
        } else {
            panic!()
        }
    }

    fn mapinsert(
        &mut self,
        maptype: &Type<'b>,
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
    ) -> FunctionValue {
        let fname = format!("{}_insert", &maptype);
        if let Some(fv) = self.module.get_function(&fname) {
            fv
        } else if let Type::Map(k, v) = maptype {
            let id = "map";
            let mut params: Vec<BasicMetadataTypeEnum> =
                vec![self.llvmtype(maptype, scopeinfo.clone()).into()];
            params.extend(
                functions::get_map_args(k, v, functions::INSERT)
                    .unwrap()
                    .iter()
                    .map(|t| {
                        std::convert::Into::<BasicMetadataTypeEnum>::into(
                            self.llvmtype(t, scopeinfo.clone()),
                        )
                    }),
            );
            const MAP_PARAM: u32 = 0;
            const KEY_PARAM: u32 = 1;
            let value_param: u32 = (params.len() - 1) as u32;

            let fv = self.module.add_function(
                &fname,
                self.llvmfunctiontype(&Type::Unit, scopeinfo.clone(), &params, false),
                None,
            );
            let call_block = self.builder.get_insert_block().unwrap();
            self.builder
                .position_at_end(self.context.append_basic_block(fv, "entry"));

            /*
            insert(map, k, v) {
                IF K NOT UNIT {
                    if (map.size + map.tombs + 1) > 0.75 * map.capacity {
                        rebuild(map)
                    }
                }
                i = hash(k) % map.capacity
                IF K NOT UNIT {
                    while map.state[i] == TAKEN && map.keys[i] != k {
                        i = (i + 1) % map.capacity
                    }
                }

                if map.states[i] == TOMB {
                    map.tombs = map.tombs - 1
                    map.size = map.size + 1
                }else if map.states[i] != TAKEN {
                    map.size = map.size + 1
                }
                map.states[i] = TAKEN
                IF K NOT UNIT {
                    map.keys[i] = k
                }
                IF V NOT UNIT{
                    map.values[i] = v
                }
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

            let tombsptr = self
                .builder
                .build_struct_gep(
                    fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                    MAP_TOMBS,
                    &(id.to_string() + ".tombs.ptr"),
                )
                .unwrap();
            let tombs = self.builder.build_load(tombsptr, "tombs");

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
            if Type::Unit.ne(k) {
                let rehashblock = self.context.append_basic_block(fv, "rehash");
                let afterhash = self.context.append_basic_block(fv, "afterhash");
                self.builder.build_conditional_branch(
                    self.builder.build_int_compare(
                        inkwell::IntPredicate::UGE,
                        self.builder.build_int_mul(
                            self.builder.build_int_add(
                                size.into_int_value(),
                                tombs.into_int_value(),
                                "",
                            ),
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
                self.builder.build_call(
                    self.rehash(maptype, scopeinfo.clone()),
                    &[fv.get_nth_param(MAP_PARAM).unwrap().into()],
                    "",
                );
                self.builder.build_unconditional_branch(afterhash);

                self.builder.position_at_end(afterhash);
            }
            let hashargs = if Type::Unit.ne(k) {
                vec![fv.get_nth_param(KEY_PARAM).unwrap().into()]
            } else {
                vec![]
            };
            let hash = self
                .builder
                .build_call(self.hash(k, scopeinfo.clone()), &hashargs, "")
                .try_as_basic_value()
                .unwrap_left();

            let idx = self.builder.build_alloca(self.context.i64_type(), "idx");
            self.builder.build_store(
                idx,
                self.builder.build_int_unsigned_rem(
                    hash.into_int_value(),
                    capacity.into_int_value(),
                    "",
                ),
            );
            if Type::Unit.ne(k) {
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
                            MAP_KEYS,
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
            }
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

            let ifbody = self.context.append_basic_block(fv, "ifbody");
            let afterif = self.context.append_basic_block(fv, "afterif");
            let elseifbody = self.context.append_basic_block(fv, "elseifbody");
            let afterelseif = self.context.append_basic_block(fv, "afterelseif");

            let stateidx = self.builder.build_load(state, "state_idx").into_int_value();

            self.builder.build_conditional_branch(
                self.builder.build_int_compare(
                    IntPredicate::EQ,
                    stateidx,
                    self.context.i64_type().const_int(STATE_TOMB, false),
                    "is_state_tomb",
                ),
                ifbody,
                afterif,
            );
            self.builder.position_at_end(ifbody);
            self.builder.build_store(
                tombsptr,
                self.builder.build_int_sub(
                    tombs.into_int_value(),
                    self.context.i64_type().const_int(1, false),
                    "tombsdecr",
                ),
            );
            self.builder.build_store(
                sizeptr,
                self.builder.build_int_add(
                    size.into_int_value(),
                    self.context.i64_type().const_int(1, false),
                    "sizeinc",
                ),
            );
            self.builder.build_unconditional_branch(afterelseif);

            self.builder.position_at_end(afterif);

            self.builder.build_conditional_branch(
                self.builder.build_int_compare(
                    IntPredicate::NE,
                    stateidx,
                    self.context.i64_type().const_int(STATE_TAKEN, false),
                    "is_not_state_taken",
                ),
                elseifbody,
                afterelseif,
            );
            self.builder.position_at_end(elseifbody);

            self.builder.build_store(
                sizeptr,
                self.builder.build_int_add(
                    size.into_int_value(),
                    self.context.i64_type().const_int(1, false),
                    "sizeinc",
                ),
            );
            self.builder.build_unconditional_branch(afterelseif);
            self.builder.position_at_end(afterelseif);

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
            if Type::Unit.ne(k) {
                self.builder.build_store(
                    unsafe {
                        self.builder.build_gep(
                            self.builder
                                .build_load(
                                    self.builder
                                        .build_struct_gep(
                                            fv.get_nth_param(MAP_PARAM)
                                                .unwrap()
                                                .into_pointer_value(),
                                            MAP_KEYS,
                                            &(id.to_string() + ".keys.ptr"),
                                        )
                                        .unwrap(),
                                    "keys",
                                )
                                .into_pointer_value(),
                            &[self.builder.build_load(idx, "").into_int_value()],
                            "",
                        )
                    },
                    fv.get_nth_param(KEY_PARAM).unwrap(),
                );
            }

            if Type::Unit.ne(v) {
                self.builder.build_store(
                    unsafe {
                        self.builder.build_gep(
                            self.builder
                                .build_load(
                                    self.builder
                                        .build_struct_gep(
                                            fv.get_nth_param(MAP_PARAM)
                                                .unwrap()
                                                .into_pointer_value(),
                                            MAP_VALUES,
                                            &(id.to_string() + ".value.ptr"),
                                        )
                                        .unwrap(),
                                    "value",
                                )
                                .into_pointer_value(),
                            &[self.builder.build_load(idx, "").into_int_value()],
                            "",
                        )
                    },
                    fv.get_nth_param(value_param).unwrap(),
                );
            }
            self.builder.build_return(None);
            self.builder.position_at_end(call_block);
            fv
        } else {
            panic!("{maptype} is not a map")
        }
    }

    fn hash(&mut self, t: &Type<'b>, scopeinfo: Rc<RefCell<ScopeInfo<'b>>>) -> FunctionValue<'ctx> {
        let s = format!("hash_{t}");
        let fv = if let Some(fv) = self.module.get_function(&s) {
            fv
        } else {
            let args = if Type::Unit.ne(t) {
                vec![self.llvmtype(t, scopeinfo.clone()).into()]
            } else {
                vec![]
            };
            let fv = self.module.add_function(
                &s,
                self.llvmfunctiontype(&Type::Int, scopeinfo.clone(), &args, false),
                None,
            );
            let call_block = self.builder.get_insert_block();
            self.builder
                .position_at_end(self.context.append_basic_block(fv, "entry"));
            match t {
                Type::Map(_, _) => todo!(),
                Type::Unit => {
                    self.builder.build_return(Some(
                        &self.llvmtype(&Type::Int, scopeinfo.clone()).const_zero(),
                    ));
                }
                _ => {
                    self.builder.build_return(Some(&self.builder.build_bitcast(
                        fv.get_nth_param(0).unwrap(),
                        self.llvmtype(&Type::Int, scopeinfo),
                        "",
                    )));
                }
            }

            if let Some(bb) = call_block {
                self.builder.position_at_end(bb);
            }
            fv
        };
        fv
    }

    //needs key type to not be unit type
    fn rehash(
        &mut self,
        t: &Type<'b>,
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
    ) -> FunctionValue<'ctx> {
        /*
        fn rehash(map) {
            newcapacity = map.size * 2 + 16
            newkeys = malloc newcapacity
            newvalues = malloc newcapacity
            newstates = calloc newcapacity
            for i in 0 .. map.capacity {
                if map.states[i] = TAKEN {
                    k = map.keys[i]
                    v = map.values[i]
                    newi = hash(k) % newcapacity
                    while newstates[newi] == TAKEN{
                        newi = (newi + 1) % newcapacity
                    }
                    newkeys[newi] = K
                    newvalues[newi] = map.values[i]
                    newstates[newi] = TAKEN
                }
            }
            free map.keys
            map.keys = newkeys
            free map.values
            map.values = newvalues
            free map.states
            map.states = newstates
            map.tombs = 0
            map.capacity = newcapacity
        }
         */
        if let Type::Map(k, v) = t {
            let hashfunction = self.hash(k, scopeinfo.clone());
            let s = format!("rehash_{t}");
            let llvmk = self.llvmtype(k, scopeinfo.clone());
            let llvmv = self.llvmtype(v, scopeinfo.clone());
            let fv = if let Some(fv) = self.module.get_function(&s) {
                fv
            } else {
                let args = vec![self.llvmtype(t, scopeinfo.clone()).into()];
                let fv = self.module.add_function(
                    &s,
                    self.llvmfunctiontype(&Type::Unit, scopeinfo.clone(), &args, false),
                    None,
                );
                let call_block = self.builder.get_insert_block();
                self.builder
                    .position_at_end(self.context.append_basic_block(fv, "entry"));

                let map = fv.get_first_param().unwrap().into_pointer_value();
                let oldcap = self
                    .builder
                    .build_load(
                        self.builder
                            .build_struct_gep(map, MAP_CAPACITY, "map.size")
                            .unwrap(),
                        "oldcapacity",
                    )
                    .into_int_value();
                let mapstatesptr = self
                    .builder
                    .build_struct_gep(map, MAP_STATES, "map.states.ptr")
                    .unwrap();
                let mapstates = self
                    .builder
                    .build_load(mapstatesptr, "map.states")
                    .into_pointer_value();

                let mapkeysptr = self
                    .builder
                    .build_struct_gep(map, MAP_KEYS, "map.keys.ptr")
                    .unwrap();
                let mapkeys = self
                    .builder
                    .build_load(mapkeysptr, "map.keys")
                    .into_pointer_value();

                let mapvaluesptr = self
                    .builder
                    .build_struct_gep(map, MAP_VALUES, "map.values.ptr")
                    .unwrap();
                let mapvalues = self
                    .builder
                    .build_load(mapvaluesptr, "map.values")
                    .into_pointer_value();

                let newcap = self.builder.build_int_add(
                    self.builder.build_int_mul(
                        self.builder
                            .build_load(
                                self.builder
                                    .build_struct_gep(map, MAP_SIZE, "map.size")
                                    .unwrap(),
                                "",
                            )
                            .into_int_value(),
                        self.context.i64_type().const_int(2, false),
                        "",
                    ),
                    self.context.i64_type().const_int(16, false),
                    "",
                );

                self.emit_printf_call(&"REHASHING %d\n", &[newcap.into()]);

                let newkeys = self
                    .builder
                    .build_array_malloc(llvmk, newcap, "newkeys")
                    .unwrap();
                let newvalues = self
                    .builder
                    .build_array_malloc(llvmv, newcap, "newvalues")
                    .unwrap();
                let newstates = self.emit_calloc(
                    self.context.i64_type(),
                    self.builder
                        .build_int_cast(newcap, self.context.i32_type(), "")
                        .into(),
                );

                let iptr = self.builder.build_alloca(self.context.i64_type(), "iptr");
                let newiptr = self
                    .builder
                    .build_alloca(self.context.i64_type(), "newiptr");
                self.builder
                    .build_store(iptr, self.context.i64_type().const_zero());

                let forinc = self.context.append_basic_block(fv, "forinc");
                let forcond = self.context.append_basic_block(fv, "forcond");
                let ifcond = self.context.append_basic_block(fv, "ifcond");
                let ifbody = self.context.append_basic_block(fv, "ifbody");
                let whilecond = self.context.append_basic_block(fv, "whilecond");
                let whilebody = self.context.append_basic_block(fv, "whilebody");
                let afterwhile = self.context.append_basic_block(fv, "afterwhile");
                let afterif = self.context.append_basic_block(fv, "afterif");
                let afterfor = self.context.append_basic_block(fv, "afterfor");

                self.builder.build_unconditional_branch(forcond);
                self.builder.position_at_end(forinc);
                self.builder.build_store(
                    iptr,
                    self.builder.build_int_add(
                        self.builder.build_load(iptr, "i").into_int_value(),
                        self.context.i64_type().const_int(1, false),
                        "iinc",
                    ),
                );
                self.builder.build_unconditional_branch(forcond);
                self.builder.position_at_end(forcond);
                let ival = self.builder.build_load(iptr, "i").into_int_value();
                self.builder.build_conditional_branch(
                    self.builder.build_int_compare(
                        IntPredicate::ULT,
                        ival,
                        oldcap,
                        "i_smaller_than_old_capacity",
                    ),
                    ifcond,
                    afterfor,
                );
                self.builder.position_at_end(ifcond);
                self.builder.build_conditional_branch(
                    self.builder.build_int_compare(
                        IntPredicate::EQ,
                        self.builder
                            .build_load(
                                unsafe { self.builder.build_gep(mapstates, &[ival], "") },
                                "map.states_i",
                            )
                            .into_int_value(),
                        self.context.i64_type().const_int(STATE_TAKEN, false),
                        "is_state_taken",
                    ),
                    ifbody,
                    afterif,
                );
                self.builder.position_at_end(ifbody);

                let key = self.builder.build_load(
                    unsafe { self.builder.build_gep(mapkeys, &[ival], "") },
                    "key",
                );
                let value = self.builder.build_load(
                    unsafe { self.builder.build_gep(mapvalues, &[ival], "") },
                    "value",
                );
                self.builder.build_store(
                    newiptr,
                    self.builder.build_int_unsigned_rem(
                        self.builder
                            .build_call(hashfunction, &[key.into()], "hash")
                            .try_as_basic_value()
                            .unwrap_left()
                            .into_int_value(),
                        newcap,
                        "newi",
                    ),
                );
                self.builder.build_unconditional_branch(whilecond);
                self.builder.position_at_end(whilecond);

                let newival = self.builder.build_load(newiptr, "newival").into_int_value();

                self.builder.build_conditional_branch(
                    self.builder.build_int_compare(
                        IntPredicate::EQ,
                        self.builder
                            .build_load(
                                unsafe { self.builder.build_gep(newstates, &[newival], "") },
                                "newstates_i",
                            )
                            .into_int_value(),
                        self.context.i64_type().const_int(STATE_TAKEN, false),
                        "is_state_taken",
                    ),
                    whilebody,
                    afterwhile,
                );

                self.builder.position_at_end(whilebody);
                self.builder.build_store(
                    newiptr,
                    self.builder.build_int_add(
                        newival,
                        self.context.i64_type().const_int(1, false),
                        "newiinc",
                    ),
                );
                self.builder.build_unconditional_branch(afterwhile);

                self.builder.position_at_end(afterwhile);

                self.builder.build_store(
                    unsafe { self.builder.build_gep(newkeys, &[newival], "newkeys_i") },
                    key,
                );
                self.builder.build_store(
                    unsafe { self.builder.build_gep(newvalues, &[newival], "newvalues_i") },
                    value,
                );
                self.builder.build_store(
                    unsafe { self.builder.build_gep(newstates, &[newival], "newstates_i") },
                    self.context.i64_type().const_int(STATE_TAKEN, false),
                );
                self.builder.build_unconditional_branch(afterif);
                self.builder.position_at_end(afterif);
                self.builder.build_unconditional_branch(forinc);
                self.builder.position_at_end(afterfor);

                self.builder.build_free(mapkeys);
                self.builder.build_store(mapkeysptr, newkeys);

                self.builder.build_free(mapvalues);
                self.builder.build_store(mapvaluesptr, newvalues);

                self.builder.build_free(mapstates);
                self.builder.build_store(mapstatesptr, newstates);

                self.builder.build_store(
                    self.builder
                        .build_struct_gep(map, MAP_TOMBS, "tombs")
                        .unwrap(),
                    self.context.i64_type().const_zero(),
                );

                self.builder.build_store(
                    self.builder
                        .build_struct_gep(map, MAP_CAPACITY, "capacity")
                        .unwrap(),
                    newcap,
                );

                self.builder.build_return(None);

                if let Some(bb) = call_block {
                    self.builder.position_at_end(bb);
                }
                fv
            };
            fv
        } else {
            panic!("needs to be map type")
        }
    }

    fn emit_calloc<T>(&self, t: T, n: BasicMetadataValueEnum<'ctx>) -> PointerValue
    where
        T: BasicType<'ctx>,
    {
        self.builder
            .build_bitcast(
                self.builder
                    .build_call(
                        self.module.get_function(CALLOC).unwrap(),
                        &[
                            n,
                            self.builder
                                .build_bitcast(t.size_of().unwrap(), self.context.i32_type(), "")
                                .into(),
                        ],
                        "calloc",
                    )
                    .try_as_basic_value()
                    .unwrap_left(),
                t.ptr_type(AddressSpace::default()),
                "",
            )
            .into_pointer_value()
    }

    fn structmapcreate(
        &mut self,
        maptype: &Type<'b>,
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
    ) -> FunctionValue {
        if let Type::StructMap(id) = maptype {
            let fname = format!("create_{maptype}");
            if let Some(fv) = self.module.get_function(&fname) {
                fv
            } else {
                let smt = typecheck::find_structmaptype(id, scopeinfo.clone()).unwrap();
                let fv = self.module.add_function(
                    &fname,
                    self.llvmfunctiontype(maptype, scopeinfo.clone(), &[], false),
                    None,
                );
                let call_block = self.builder.get_insert_block().unwrap();
                let llvmmaptype = self.llvmstruct(maptype, scopeinfo.clone());
                self.builder
                    .position_at_end(self.context.append_basic_block(fv, "entry"));
                let map = self.builder.build_malloc(llvmmaptype, "map").unwrap();
                let size = self
                    .builder
                    .build_struct_gep(map, STRUCT_MAP_SIZE, "map.size")
                    .unwrap();
                self.builder
                    .build_store(size, self.context.i64_type().const_int(0, false));
                let booltype = self.llvmtype(&Type::Bool, scopeinfo.clone());
                self.builder.build_store(
                    self.builder
                        .build_struct_gep(map, STRUCT_MAP_FLAGS, "")
                        .unwrap(),
                    self.emit_calloc(
                        booltype,
                        self.context
                            .i32_type()
                            .const_int(smt.1.len() as u64, false)
                            .into(),
                    ),
                );
                let mapptr = self
                    .builder
                    .build_alloca(self.llvmtype(maptype, scopeinfo.clone()), "map");
                self.builder.build_store(mapptr, map);
                self.builder.build_return(Some(&map.as_basic_value_enum()));

                self.builder.position_at_end(call_block);
                fv
            }
        } else {
            panic!("wrong type");
        }
    }

    fn mapstructremove(
        &mut self,
        maptype: &Type<'b>,
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
        index: u64,
    ) -> FunctionValue {
        let fname = format!("{}_remove_{index}", &maptype);
        if let Some(fv) = self.module.get_function(&fname) {
            fv
        } else if let Type::StructMap(_) = maptype {
            let params: Vec<BasicMetadataTypeEnum> =
                vec![self.llvmtype(maptype, scopeinfo.clone()).into()];
            const MAP_PARAM: u32 = 0;
            /*
            fn mapstructremove<K>(v){
                if map.states[i] == TAKEN {
                    map.size = map.size - 1
                }
                map.states[i] = FREE
            }
            */
            let fv = self.module.add_function(
                &fname,
                self.llvmfunctiontype(&Type::Unit, scopeinfo.clone(), &params, false),
                None,
            );
            let call_block = self.builder.get_insert_block().unwrap();
            self.builder
                .position_at_end(self.context.append_basic_block(fv, "entry"));

            let ifbody = self.context.append_basic_block(fv, "ifbody");
            let afterif = self.context.append_basic_block(fv, "afterif");

            let flags = self
                .builder
                .build_load(
                    self.builder
                        .build_struct_gep(
                            fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                            STRUCT_MAP_FLAGS,
                            "",
                        )
                        .unwrap(),
                    "map.states",
                )
                .into_pointer_value();
            let flagi = unsafe {
                self.builder.build_gep(
                    flags,
                    &[self.context.i64_type().const_int(index, false)],
                    "map.states_i",
                )
            };
            self.builder.build_conditional_branch(
                self.builder.build_int_compare(
                    IntPredicate::EQ,
                    self.builder.build_load(flagi, "").into_int_value(),
                    self.context.bool_type().const_all_ones(),
                    "is_taken",
                ),
                ifbody,
                afterif,
            );
            self.builder.position_at_end(ifbody);
            let size = self
                .builder
                .build_struct_gep(
                    fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                    STRUCT_MAP_SIZE,
                    "map.size",
                )
                .unwrap();
            self.builder.build_store(
                size,
                self.builder.build_int_sub(
                    self.builder.build_load(size, "").into_int_value(),
                    self.context.i64_type().const_int(1, false),
                    "",
                ),
            );
            self.builder.build_unconditional_branch(afterif);
            self.builder.position_at_end(afterif);
            self.builder
                .build_store(flagi, self.context.bool_type().const_zero());

            self.builder.build_return(None);
            self.builder.position_at_end(call_block);
            fv
        } else {
            panic!()
        }
    }
}
