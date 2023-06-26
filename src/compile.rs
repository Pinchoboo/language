use std::{
    cell::RefCell,
    collections::HashMap,
    iter::once_with,
    path::Path,
    process::{exit, Command},
    rc::Rc,
};

use inkwell::{
    builder::Builder,
    context::Context,
    execution_engine::{ExecutionEngine, UnsafeFunctionPointer},
    memory_buffer::MemoryBuffer,
    module::{Linkage, Module},
    targets::{InitializationConfig, Target, TargetTriple},
    types::{
        BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType, IntType, PointerType,
        StructType,
    },
    values::{
        ArrayValue, BasicMetadataValueEnum, BasicValue, BasicValueEnum, CallSiteValue,
        FunctionValue, GlobalValue, IntValue, PointerValue,
    },
    AddressSpace, IntPredicate, OptimizationLevel,
};

use crate::{
    functions::{self},
    parser::{BinOp, Block, Expression, Program, Statement, Type, Value},
    perfect,
    typecheck::{self, find_structmaptype, find_variable, ScopeInfo},
};
const PRINTF: &str = "printf";
const MEMSET: &str = "memset";
const CALLOC: &str = "calloc";
const MALLOC: &str = "malloc";

pub struct Compiler<'ctx, 'a> {
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    module: &'a Module<'ctx>,
    opt_module: Option<Module<'ctx>>,
    vars: HashMap<i32, PointerValue<'ctx>>,
    strings: Rc<RefCell<HashMap<String, PointerValue<'ctx>>>>,
    mapstructs: HashMap<String, StructType<'ctx>>,
    structbodies: Vec<(StructType<'ctx>, Vec<BasicTypeEnum<'ctx>>)>,
    ee: Option<ExecutionEngine<'ctx>>,
    #[cfg(feature = "heapsize")]
    space: GlobalValue<'ctx>,
}

pub fn compile<'ctx, 'a>(
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    module: &'a Module<'ctx>,
    program: Program,
) -> Compiler<'ctx, 'a> {
    let mut c = Compiler {
        context,
        module,
        opt_module: None,
        builder,
        vars: HashMap::new(),
        strings: Rc::new(RefCell::new(HashMap::new())),
        mapstructs: HashMap::new(),
        structbodies: Vec::new(),
        ee: None,
        #[cfg(feature = "heapsize")]
        space: {
            let s = module.add_global(context.i64_type(), None, "ALLOC_DEBUG");
            s.set_initializer(&context.i64_type().const_zero());
            s
        },
    };
    c.compile(program);
    c
}

pub const CONST_MAP_SIZE: u32 = 0;
pub const CONST_MAP_KEYS: u32 = 1;
pub const CONST_MAP_VALUES: u32 = 2;
pub const CONST_MAP_ARGS_LEN: u32 = 3;
pub const CONST_MAP_ARGS: u32 = 4;

pub const STRUCT_MAP_SIZE: u32 = 0;
pub const STRUCT_MAP_FLAGS: u32 = 1;

pub const MAP_CAPACITY: u32 = 0;
pub const MAP_SIZE: u32 = 1;
pub const MAP_TOMBS: u32 = 2;
pub const MAP_STATES: u32 = 3;
pub const MAP_KEYS: u32 = 4;

fn map_values(k: &Type) -> u32 {
    if Type::Unit.eq(k) {
        4
    } else {
        5
    }
}

pub const STATE_FREE: u64 = 0;
pub const STATE_TAKEN: u64 = 1;
pub const STATE_TOMB: u64 = 2;

const ROT: &str = "llvm.fshr.i64";

impl<'ctx, 'a, 'b> Compiler<'ctx, 'a> {
    fn statetype(&self) -> IntType<'ctx> {
        self.context.custom_width_int_type(2)
    }

    fn llvmstruct(&mut self, t: &Type<'b>, si: Rc<RefCell<ScopeInfo<'b>>>) -> StructType<'ctx> {
        match t {
            Type::Map(k, v) => {
                let struct_name = format!("{t}");
                let capacity = Some(self.context.i64_type().as_basic_type_enum());
                let size = Some(self.context.i64_type().as_basic_type_enum());
                let tombs = Some(self.context.i64_type().as_basic_type_enum());
                let keys = if Type::Unit.eq(k) {
                    None
                } else {
                    Some(
                        self.llvmtype(k, si.clone())
                            .ptr_type(AddressSpace::default())
                            .as_basic_type_enum(),
                    )
                };
                let states = Some(
                    self.statetype()
                        .ptr_type(AddressSpace::default())
                        .as_basic_type_enum(),
                );

                let vals = if Type::Unit.eq(v) {
                    None
                } else {
                    Some(
                        self.llvmtype(v, si)
                            .ptr_type(AddressSpace::default())
                            .as_basic_type_enum(),
                    )
                };
                let field_types: Vec<BasicTypeEnum> = [capacity, size, tombs, states, keys, vals]
                    .into_iter()
                    .flatten()
                    .collect();
                *self.mapstructs.entry(format!("{t}")).or_insert({
                    let st = self.context.opaque_struct_type(&struct_name);
                    st.set_body(field_types.as_slice(), false);
                    st
                })
            }
            Type::PerfectMap(k, v) => {
                let struct_name = format!("{t}");
                let size = self.context.i64_type();
                let keys = self
                    .llvmtype(k, si.clone())
                    .ptr_type(AddressSpace::default());
                let vals = self.llvmtype(v, si).ptr_type(AddressSpace::default());
                let argslen = self.context.i32_type();
                let args = self.context.i32_type().ptr_type(AddressSpace::default());

                *self.mapstructs.entry(format!("{t}")).or_insert({
                    let st = self.context.opaque_struct_type(&struct_name);
                    st.set_body(
                        &[
                            size.into(),
                            keys.into(),
                            vals.into(),
                            argslen.into(),
                            args.into(),
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

                if let std::collections::hash_map::Entry::Vacant(e) =
                    self.mapstructs.entry(format!("{t}"))
                {
                    let st = self.context.opaque_struct_type(&struct_name);
                    e.insert(st);
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

                *self.mapstructs.get(&format!("{t}")).unwrap()
            }
            _ => {
                assert!(matches!(t, Type::Map { .. }));
                panic!()
            }
        }
    }

    #[cfg(feature = "heapsize")]
    fn add_alloc(&self, v: IntValue) {
        self.builder.build_store(
            self.space.as_pointer_value(),
            self.builder.build_int_add(
                v,
                self.builder
                    .build_load(self.space.as_pointer_value(), "")
                    .into_int_value(),
                "",
            ),
        );
    }

    #[cfg(feature = "heapsize")]
    fn remove_alloc(&self, v: IntValue) {
        self.builder.build_store(
            self.space.as_pointer_value(),
            self.builder.build_int_sub(
                self.builder
                    .build_load(self.space.as_pointer_value(), "")
                    .into_int_value(),
                v,
                "",
            ),
        );
    }

    fn emit_get_alloc(&self) -> CallSiteValue<'ctx> {
        self.builder.build_call(
            self.module.get_function(functions::HEAP_SIZE).unwrap(),
            &[],
            "",
        )
    }

    fn build_malloc<T>(&mut self, ty: T) -> Result<PointerValue<'ctx>, &'static str>
    where
        T: BasicType<'ctx>,
    {
        #[cfg(feature = "heapsize")]
        {
            self.add_alloc(ty.size_of().unwrap())
        }
        self.builder.build_malloc(ty, "")
    }

    fn build_array_malloc<T>(
        &mut self,
        ty: T,
        size: IntValue<'ctx>,
    ) -> Result<PointerValue<'ctx>, &'static str>
    where
        T: BasicType<'ctx>,
    {
        #[cfg(feature = "heapsize")]
        {
            self.add_alloc(
                self.builder.build_int_mul(
                    ty.size_of().unwrap(),
                    self.builder
                        .build_int_cast(size, self.context.i64_type(), ""),
                    "",
                ),
            )
        }
        self.builder.build_array_malloc(ty, size, "")
    }
    fn build_calloc<T>(&self, t: T, n: BasicMetadataValueEnum<'ctx>) -> PointerValue
    where
        T: BasicType<'ctx>,
    {
        #[cfg(feature = "heapsize")]
        {
            self.add_alloc(
                self.builder.build_int_mul(
                    self.builder
                        .build_int_cast(n.into_int_value(), self.context.i64_type(), ""),
                    t.size_of().unwrap(),
                    "",
                ),
            )
        }
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

    fn llvmtype(&mut self, t: &Type<'b>, si: Rc<RefCell<ScopeInfo<'b>>>) -> BasicTypeEnum<'ctx> {
        match t {
            Type::Int => self.context.i64_type().as_basic_type_enum(),
            Type::Float => self.context.i64_type().as_basic_type_enum(),
            Type::Bool => self.context.bool_type().as_basic_type_enum(),
            Type::Char => self.context.i8_type().as_basic_type_enum(),
            Type::Unit => self.context.custom_width_int_type(0).as_basic_type_enum(),
            Type::Map(_, _) | Type::StructMap(_) | Type::PerfectMap(_, _) => self
                .llvmstruct(t, si)
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum(),
        }
    }

    fn llvmconstarray(
        &mut self,
        t: &Type<'b>,
        si: Rc<RefCell<ScopeInfo<'b>>>,
        values: &[BasicValueEnum<'ctx>],
    ) -> ArrayValue<'ctx> {
        match t {
            Type::Int => self.context.i64_type().const_array(
                &values
                    .iter()
                    .map(|v| v.into_int_value())
                    .collect::<Vec<_>>(),
            ),
            Type::Float => self.context.i64_type().const_array(
                &values
                    .iter()
                    .map(|v| {
                        self.builder
                            .build_bitcast(*v, self.context.i64_type(), "")
                            .into_int_value()
                    })
                    .collect::<Vec<_>>(),
            ),
            Type::Bool => self.context.bool_type().const_array(
                &values
                    .iter()
                    .map(|v| v.into_int_value())
                    .collect::<Vec<_>>(),
            ),
            Type::Char => self.context.i8_type().const_array(
                &values
                    .iter()
                    .map(|v| v.into_int_value())
                    .collect::<Vec<_>>(),
            ),
            Type::Unit => self.context.custom_width_int_type(0).const_array(
                &values
                    .iter()
                    .map(|v| v.into_int_value())
                    .collect::<Vec<_>>(),
            ),
            Type::Map(_, _) | Type::StructMap(_) | Type::PerfectMap(_, _) => self
                .llvmstruct(t, si)
                .ptr_type(AddressSpace::default())
                .const_array(
                    &values
                        .iter()
                        .map(|v| v.into_pointer_value())
                        .collect::<Vec<_>>(),
                ),
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
            Type::Char => self.context.i8_type().fn_type(param_types, is_var_args),
            Type::Unit => self.context.void_type().fn_type(param_types, is_var_args),
            Type::Map(_, _) | Type::StructMap(_) | Type::PerfectMap(_, _) => self
                .llvmstruct(t, si)
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum()
                .fn_type(param_types, is_var_args),
        }
    }

    fn compile(&mut self, program: Program<'b>) {
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
            self.module.add_function(
                MALLOC,
                self.context
                    .i8_type()
                    .ptr_type(AddressSpace::default())
                    .fn_type(&[self.context.i64_type().into()], false),
                Some(Linkage::External),
            );
            self.module.add_function(
                ROT,
                self.context.i64_type().fn_type(
                    &[
                        self.context.i64_type().into(),
                        self.context.i64_type().into(),
                        self.context.i64_type().into(),
                    ],
                    false,
                ),
                Some(Linkage::External),
            );
            self.builder
                .position_at_end(self.context.append_basic_block(
                    self.module.add_function(
                        functions::HEAP_SIZE,
                        self.context.i64_type().fn_type(&[], false),
                        None,
                    ),
                    "entry",
                ));
            #[cfg(feature = "heapsize")]
            {
                self.builder.build_return(Some(
                    &self.builder.build_load(self.space.as_pointer_value(), ""),
                ));
            }
            #[cfg(not(feature = "heapsize"))]
            {
                self.builder
                    .build_return(Some(&self.context.i64_type().const_zero()));
            }
        }

        for fm in program.findmaps {
            let ptr = self.emit_global_map(program.scopeinfo.clone(), &fm);
            self.vars.insert(fm.nid, ptr);
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
            self.module
                .set_triple(&TargetTriple::create("x86_64-pc-linux-gnu"));
            let _result = self.module.print_to_file("./out/program.ll");

            //check module
            let err = Command::new("opt-12")
                .arg("-verify")
                .arg("./out/program.ll")
                .arg("-O3")
                .arg("-S")
                .arg("-o")
                .arg("./out/program.opt.ll")
                .output()
                .unwrap()
                .stderr;
            if !err.is_empty() {
                println!("{}", std::str::from_utf8(&err).unwrap());
                exit(1)
            } else {
                println!("LLVM-IR is valid")
            }
            /*
            if let Err(e) = self.module.verify() {
                println!("{}", e.to_string());
                return;
            }
            */

            //save executable
            Target::initialize_x86(&InitializationConfig::default());

            /*let _result = target_machine.write_to_file(
                &module,
                FileType::Assembly,
                Path::new("./out/main.asm"),
            );*/

            let err = Command::new("clang")
                .arg("-no-pie")
                .arg("./out/program.ll")
                .arg("-o")
                .arg("./out/program")
                .arg("-g")
                .arg("-O3")
                //                .arg("-fsanitize=address")
                .arg("-Weverything")
                .arg("-Wextra")
                .arg("-Wall")
                .output()
                .unwrap()
                .stderr;

            self.opt_module = Some(
                self.context
                    .create_module_from_ir(
                        MemoryBuffer::create_from_file(Path::new("./out/program.opt.ll")).unwrap(),
                    )
                    .unwrap(),
            );

            if !err.is_empty() {
                println!("{}", std::str::from_utf8(&err).unwrap());
                exit(1)
            } else {
                println!("LLVM-IR compiled succesfully")
            }
        }
        if self.ee.is_none() {
            self.ee = Some(
                self.opt_module
                    .as_ref()
                    .unwrap()
                    .create_jit_execution_engine(OptimizationLevel::Aggressive)
                    .unwrap(),
            );
        };
    }

    pub fn execute(&self) -> i32 {
        unsafe { self.get_function::<unsafe extern "C" fn() -> i32>("main")() }
    }
    fn debug(&self, s: &str, args: impl AsRef<[BasicMetadataValueEnum<'ctx>]>) {
        if cfg!(feature = "debugmpl") {
            self.emit_printf_call(&s, args.as_ref());
        }
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

    pub fn get_function<F: UnsafeFunctionPointer>(&self, fname: &str) -> F {
        if let Some(_ee) = &self.ee {
            let maybe_fn = unsafe { self.ee.as_ref().unwrap().get_function::<F>(fname) };
            return match maybe_fn {
                Ok(f) => unsafe { f.as_raw() },
                Err(err) => {
                    panic!("{:?}", err);
                }
            };
        }
        unreachable!()
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
            crate::parser::StatementType::Assignment(_, "_", expr, _) => {
                self.emit_expression(expr, scopeinfo.clone(), fv, true);
            }
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
                let value = self.emit_expression(expr, scopeinfo.clone(), fv, false);
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
                    Some((_, Type::Map(k, v), _, _)) => {
                        let mapptr = self.vars.get(i).unwrap();
                        let map = self.builder.build_load(*mapptr, "").into_pointer_value();

                        let states = self
                            .builder
                            .build_struct_gep(map, MAP_STATES, "states_ptr")
                            .unwrap();

                        #[cfg(feature = "heapsize")]
                        {
                            self.remove_alloc(
                                self.builder.build_int_mul(
                                    self.statetype().size_of(),
                                    self.builder
                                        .build_load(
                                            self.builder
                                                .build_struct_gep(map, MAP_CAPACITY, "capacity")
                                                .unwrap(),
                                            "",
                                        )
                                        .into_int_value(),
                                    "",
                                ),
                            )
                        }
                        self.builder.build_free(
                            self.builder
                                .build_load(states, "states")
                                .into_pointer_value(),
                        );
                        if Type::Unit.ne(&k) {
                            let keys = self
                                .builder
                                .build_struct_gep(map, MAP_KEYS, "keys_ptr")
                                .unwrap();
                            #[cfg(feature = "heapsize")]
                            {
                                let keysize =
                                    self.llvmtype(&k, scopeinfo.clone()).size_of().unwrap();

                                self.remove_alloc(
                                    self.builder.build_int_mul(
                                        keysize,
                                        self.builder
                                            .build_load(
                                                self.builder
                                                    .build_struct_gep(map, MAP_CAPACITY, "capacity")
                                                    .unwrap(),
                                                "",
                                            )
                                            .into_int_value(),
                                        "",
                                    ),
                                )
                            }
                            self.builder.build_free(
                                self.builder.build_load(keys, "keys").into_pointer_value(),
                            );
                        }

                        if Type::Unit.ne(&v) {
                            let values = self
                                .builder
                                .build_struct_gep(map, map_values(&k), "values_ptr")
                                .unwrap();
                            #[cfg(feature = "heapsize")]
                            {
                                let valuesize =
                                    self.llvmtype(&v, scopeinfo.clone()).size_of().unwrap();
                                self.remove_alloc(
                                    self.builder.build_int_mul(
                                        valuesize,
                                        self.builder
                                            .build_load(
                                                self.builder
                                                    .build_struct_gep(map, MAP_CAPACITY, "capacity")
                                                    .unwrap(),
                                                "",
                                            )
                                            .into_int_value(),
                                        "",
                                    ),
                                )
                            }
                            self.builder.build_free(
                                self.builder
                                    .build_load(values, "values")
                                    .into_pointer_value(),
                            );
                        }
                        #[cfg(feature = "heapsize")]
                        {
                            let mapsize = self
                                .llvmstruct(&Type::Map(k.clone(), v.clone()), scopeinfo.clone())
                                .size_of()
                                .unwrap();
                            self.remove_alloc(mapsize)
                        }
                        self.builder.build_free(map);
                    }
                    Some((_, Type::StructMap(s), _, _)) => {
                        let fsmt =
                            typecheck::find_structmaptype(s, scopeinfo.clone()).expect("exists");
                        let mapptr = self.vars.get(i).unwrap();
                        let map = self.builder.build_load(*mapptr, "").into_pointer_value();
                        let flags = self
                            .builder
                            .build_load(
                                self.builder
                                    .build_struct_gep(map, STRUCT_MAP_FLAGS, "flags_ptr")
                                    .unwrap(),
                                "",
                            )
                            .into_pointer_value();
                        #[cfg(feature = "heapsize")]
                        {
                            self.remove_alloc(
                                self.builder.build_int_mul(
                                    self.context.bool_type().size_of(),
                                    self.context
                                        .i64_type()
                                        .const_int(fsmt.1.len() as u64, false),
                                    "flag_size",
                                ),
                            );
                        }
                        self.builder.build_free(flags);

                        #[cfg(feature = "heapsize")]
                        {
                            let mapsize = self
                                .llvmstruct(&Type::StructMap(s), scopeinfo.clone())
                                .size_of()
                                .unwrap();
                            self.remove_alloc(mapsize)
                        }
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
                    let cond = self.emit_expression(cond, scopeinfo.clone(), fv, false);
                    self.builder.build_conditional_branch(
                        cond.into_int_value(),
                        *thenlable,
                        *afterthenlable,
                    );
                    self.builder.position_at_end(*thenlable);
                    self.emit_block(block, fv);
                    if self
                        .builder
                        .get_insert_block()
                        .unwrap()
                        .get_terminator()
                        .is_none()
                    {
                        self.builder.build_unconditional_branch(afterelselable);
                    }
                    self.builder.position_at_end(*afterthenlable);
                }
                self.builder
                    .get_insert_block()
                    .unwrap()
                    .set_name("elseblock");
                self.emit_block(elseblock, fv);
                if self
                    .builder
                    .get_insert_block()
                    .unwrap()
                    .get_terminator()
                    .is_none()
                {
                    self.builder.build_unconditional_branch(afterelselable);
                }
                self.builder.position_at_end(afterelselable);
            }
            crate::parser::StatementType::While((cond, block)) => {
                let condlable = self.context.append_basic_block(fv, "whilecond");
                let whilelable = self.context.append_basic_block(fv, "while");
                let afterwhilelable = self.context.append_basic_block(fv, "afterwhile");
                self.builder.build_unconditional_branch(condlable);
                self.builder.position_at_end(condlable);
                self.builder.build_conditional_branch(
                    self.emit_expression(cond, scopeinfo, fv, false)
                        .into_int_value(),
                    whilelable,
                    afterwhilelable,
                );
                self.builder.position_at_end(whilelable);
                self.emit_block(block, fv);

                if self
                    .builder
                    .get_insert_block()
                    .unwrap()
                    .get_terminator()
                    .is_none()
                {
                    self.builder.build_unconditional_branch(condlable);
                }
                self.builder.position_at_end(afterwhilelable)
            }
            crate::parser::StatementType::For(keyid, valid, map, block, Some(maptype)) => {
                let map = self
                    .emit_value(map, scopeinfo.clone(), fv)
                    .into_pointer_value();
                if let Type::Map(k, v) = maptype {
                    //self.emit_printf_call(&"FOR:\n", &[]);
                    let idx = self.builder.build_alloca(self.context.i64_type(), "idx");
                    self.builder
                        .build_store(idx, self.context.i64_type().const_zero());

                    let capacity = self
                        .builder
                        .build_load(
                            self.builder
                                .build_struct_gep(map, MAP_CAPACITY, "capacity")
                                .unwrap(),
                            "",
                        )
                        .into_int_value();
                    let states = self
                        .builder
                        .build_load(
                            self.builder
                                .build_struct_gep(map, MAP_STATES, "map.states.ptr")
                                .unwrap(),
                            "states",
                        )
                        .into_pointer_value();
                    let kd =
                        typecheck::find_variable(keyid, block.scopeinfo.clone()).expect("exist");
                    let vd =
                        typecheck::find_variable(valid, block.scopeinfo.clone()).expect("exist");
                    let kpointer = if kd.1.ne(&Type::Unit) {
                        let p = self
                            .builder
                            .build_alloca(self.llvmtype(&k, scopeinfo.clone()), "kpointer");
                        self.vars.insert(kd.2, p);
                        Some(p)
                    } else {
                        None
                    };
                    let valueptr = if vd.1.ne(&Type::Unit) {
                        let p = self
                            .builder
                            .build_alloca(self.llvmtype(&v, scopeinfo.clone()), "vpointer");
                        self.vars.insert(vd.2, p);
                        Some(p)
                    } else {
                        None
                    };

                    let whilecond = self.context.append_basic_block(fv, "whilecond");
                    let whilebody = self.context.append_basic_block(fv, "whilebody");
                    let afterwhile = self.context.append_basic_block(fv, "afterwhile");
                    self.builder.build_unconditional_branch(whilecond);
                    self.builder.position_at_end(whilecond);
                    let idxval = self.builder.build_load(idx, "").into_int_value();
                    //self.emit_printf_call(&"idx:%d\n", &[idxval.into()]);
                    self.builder.build_conditional_branch(
                        self.builder
                            .build_int_compare(IntPredicate::ULT, idxval, capacity, ""),
                        whilebody,
                        afterwhile,
                    );
                    self.builder.position_at_end(whilebody);
                    let validentry = self.context.append_basic_block(fv, "validentry");
                    let aftervalid = self.context.append_basic_block(fv, "aftervalid");

                    let stateidx = self.builder.build_load(
                        unsafe { self.builder.build_gep(states, &[idxval], "") },
                        "state_idx",
                    );

                    self.builder.build_conditional_branch(
                        self.builder.build_int_compare(
                            IntPredicate::EQ,
                            stateidx.into_int_value(),
                            self.statetype().const_int(STATE_TAKEN, false),
                            "is_taken",
                        ),
                        validentry,
                        aftervalid,
                    );
                    self.builder.position_at_end(validentry);

                    if kd.1.ne(&Type::Unit) {
                        self.builder.build_store(
                            kpointer.unwrap(),
                            self.builder.build_load(
                                unsafe {
                                    self.builder.build_gep(
                                        self.builder
                                            .build_load(
                                                self.builder
                                                    .build_struct_gep(map, MAP_KEYS, "map.keys.ptr")
                                                    .unwrap(),
                                                "keys",
                                            )
                                            .into_pointer_value(),
                                        &[idxval],
                                        "",
                                    )
                                },
                                "keys_i",
                            ),
                        );
                    }

                    let vd =
                        typecheck::find_variable(valid, block.scopeinfo.clone()).expect("exist");
                    if vd.1.ne(&Type::Unit) {
                        self.builder.build_store(
                            valueptr.unwrap(),
                            self.builder.build_load(
                                unsafe {
                                    self.builder.build_gep(
                                        self.builder
                                            .build_load(
                                                self.builder
                                                    .build_struct_gep(
                                                        map,
                                                        map_values(&kd.1),
                                                        "map.values.ptr",
                                                    )
                                                    .unwrap(),
                                                "values",
                                            )
                                            .into_pointer_value(),
                                        &[idxval],
                                        "",
                                    )
                                },
                                "value_i",
                            ),
                        );
                    }

                    self.emit_block(block, fv);

                    self.builder.build_unconditional_branch(aftervalid);
                    self.builder.position_at_end(aftervalid);
                    self.builder.build_store(
                        idx,
                        self.builder.build_int_add(
                            idxval,
                            self.context.i64_type().const_int(1, false),
                            "",
                        ),
                    );
                    self.builder.build_unconditional_branch(whilecond);
                    self.builder.position_at_end(afterwhile);
                } else if let Type::PerfectMap(k, v) = maptype {
                    let idx = self.builder.build_alloca(self.context.i64_type(), "idx");
                    self.builder
                        .build_store(idx, self.context.i64_type().const_zero());

                    let size = self
                        .builder
                        .build_load(
                            self.builder
                                .build_struct_gep(map, CONST_MAP_SIZE, "size")
                                .unwrap(),
                            "",
                        )
                        .into_int_value();

                    let whilecond = self.context.append_basic_block(fv, "whilecond");
                    let whilebody = self.context.append_basic_block(fv, "whilebody");
                    let afterwhile = self.context.append_basic_block(fv, "afterwhile");
                    self.builder.build_unconditional_branch(whilecond);
                    self.builder.position_at_end(whilecond);
                    let idxval = self.builder.build_load(idx, "").into_int_value();
                    //self.emit_printf_call(&"idx:%d\n", &[idxval.into()]);
                    self.builder.build_conditional_branch(
                        self.builder
                            .build_int_compare(IntPredicate::ULT, idxval, size, ""),
                        whilebody,
                        afterwhile,
                    );
                    self.builder.position_at_end(whilebody);

                    let kd =
                        typecheck::find_variable(keyid, block.scopeinfo.clone()).expect("exist");
                    if kd.1.ne(&Type::Unit) {
                        let kpointer = {
                            let p = self
                                .builder
                                .build_alloca(self.llvmtype(&k, scopeinfo.clone()), "kpointer");
                            self.vars.insert(kd.2, p);
                            p
                        };
                        self.builder.build_store(
                            kpointer,
                            self.builder.build_load(
                                unsafe {
                                    self.builder.build_gep(
                                        self.builder
                                            .build_load(
                                                self.builder
                                                    .build_struct_gep(
                                                        map,
                                                        CONST_MAP_KEYS,
                                                        "map.keys.ptr",
                                                    )
                                                    .unwrap(),
                                                "keys",
                                            )
                                            .into_pointer_value(),
                                        &[idxval],
                                        "",
                                    )
                                },
                                "keys_i",
                            ),
                        );
                    }

                    let vd =
                        typecheck::find_variable(valid, block.scopeinfo.clone()).expect("exist");
                    if vd.1.ne(&Type::Unit) {
                        let vpointer = {
                            let p = self
                                .builder
                                .build_alloca(self.llvmtype(&v, scopeinfo.clone()), "vpointer");
                            self.vars.insert(vd.2, p);
                            p
                        };
                        self.builder.build_store(
                            vpointer,
                            self.builder.build_load(
                                unsafe {
                                    self.builder.build_gep(
                                        self.builder
                                            .build_load(
                                                self.builder
                                                    .build_struct_gep(
                                                        map,
                                                        CONST_MAP_VALUES,
                                                        "map.values.ptr",
                                                    )
                                                    .unwrap(),
                                                "values",
                                            )
                                            .into_pointer_value(),
                                        &[idxval],
                                        "",
                                    )
                                },
                                "value_i",
                            ),
                        );
                    }

                    self.emit_block(block, fv);

                    self.builder.build_store(
                        idx,
                        self.builder.build_int_add(
                            idxval,
                            self.context.i64_type().const_int(1, false),
                            "",
                        ),
                    );
                    self.builder.build_unconditional_branch(whilecond);
                    self.builder.position_at_end(afterwhile);
                } else {
                    unreachable!();
                }
            }
            crate::parser::StatementType::Call(id, args, Some(i)) => {
                self.emit_call(id, args, i, scopeinfo, fv);
            }
            crate::parser::StatementType::Return(None) => {
                self.builder.build_return(None);
            }
            crate::parser::StatementType::Return(Some(e)) => {
                self.builder
                    .build_return(Some(&self.emit_expression(e, scopeinfo, fv, false)));
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
                let initial_capacity: u32 = if Type::Unit.eq(k) {
                    1
                } else if Type::Bool.eq(k) {
                    4
                } else {
                    16
                };
                let fv = self.module.add_function(
                    &fname,
                    self.llvmfunctiontype(maptype, scopeinfo.clone(), &[], false),
                    None,
                );
                let call_block = self.builder.get_insert_block().unwrap();
                self.builder
                    .position_at_end(self.context.append_basic_block(fv, "entry"));
                let map = {
                    let t = self.llvmstruct(maptype, scopeinfo.clone());
                    self.build_malloc(t).unwrap()
                };

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
                            {
                                let t = self
                                    .llvmtype(k, scopeinfo.clone())
                                    .array_type(initial_capacity);
                                self.build_malloc(t).unwrap()
                            },
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
                let states_alloc = {
                    let t = self.statetype().array_type(initial_capacity);
                    self.build_malloc(t).unwrap()
                };
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
                                self.statetype()
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
                        self.statetype().ptr_type(AddressSpace::default()),
                        "states_ptr",
                    ),
                );

                if !Type::Unit.eq(v) {
                    let values = self
                        .builder
                        .build_struct_gep(map, map_values(&k), "map.values")
                        .unwrap();
                    self.builder.build_store(
                        values,
                        self.builder.build_bitcast(
                            {
                                let t = self
                                    .llvmtype(v, scopeinfo.clone())
                                    .array_type(initial_capacity);
                                self.build_malloc(t).unwrap()
                            },
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
        discardvalue: bool,
    ) -> BasicValueEnum<'ctx> {
        match expr {
            Expression::Binary(l, b, r, Some(_)) => {
                let lv = self.emit_expression(l, scopeinfo.clone(), fv, discardvalue);
                let rv = self.emit_expression(r, scopeinfo.clone(), fv, discardvalue);
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
                    (Type::Int, BinOp::Divide, Type::Int) => {
                        BasicValueEnum::IntValue(self.builder.build_int_signed_div(
                            lv.into_int_value(),
                            rv.into_int_value(),
                            "",
                        ))
                    }
                    (Type::Int, BinOp::Modulo, Type::Int) => {
                        BasicValueEnum::IntValue(self.builder.build_int_unsigned_rem(
                            lv.into_int_value(),
                            rv.into_int_value(),
                            "",
                        ))
                    }

                    (Type::Float, BinOp::Add, Type::Float) => self.builder.build_bitcast(
                        self.builder.build_float_add(
                            self.builder
                                .build_bitcast(lv, self.context.f64_type(), "")
                                .into_float_value(),
                            self.builder
                                .build_bitcast(rv, self.context.f64_type(), "")
                                .into_float_value(),
                            "",
                        ),
                        self.context.i64_type(),
                        "",
                    ),
                    (Type::Float, BinOp::Subtract, Type::Float) => self.builder.build_bitcast(
                        self.builder.build_float_sub(
                            self.builder
                                .build_bitcast(lv, self.context.f64_type(), "")
                                .into_float_value(),
                            self.builder
                                .build_bitcast(rv, self.context.f64_type(), "")
                                .into_float_value(),
                            "",
                        ),
                        self.context.i64_type(),
                        "",
                    ),
                    (Type::Float, BinOp::Multiply, Type::Float) => self.builder.build_bitcast(
                        self.builder.build_float_mul(
                            self.builder
                                .build_bitcast(lv, self.context.f64_type(), "")
                                .into_float_value(),
                            self.builder
                                .build_bitcast(rv, self.context.f64_type(), "")
                                .into_float_value(),
                            "",
                        ),
                        self.context.i64_type(),
                        "",
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
                    (Type::Int, BinOp::NotEqual, Type::Int) => {
                        BasicValueEnum::IntValue(self.builder.build_int_compare(
                            inkwell::IntPredicate::NE,
                            lv.into_int_value(),
                            rv.into_int_value(),
                            "",
                        ))
                    }
                    _ => {
                        panic!(
                            "should be exhaustive, missing{:?}",
                            (l.get_type(), b, r.get_type())
                        )
                    }
                }
            }

            Expression::Unary(_, _, Some(_)) => todo!(),
            Expression::Value(v, Some(_)) => {
                if discardvalue {
                    match v {
                        Value::Call(id, args, Some(i)) => {
                            self.emit_call(id, args, i, scopeinfo, fv);
                        }
                        Value::MapCall(id, id2, exprs, Some(i)) => {
                            self.emit_map_call(id, id2, exprs, i, scopeinfo, fv);
                        }
                        _ => {}
                    }
                    self.context.custom_width_int_type(0).const_zero().into()
                } else {
                    self.emit_value(v, scopeinfo, fv)
                }
            }
            _ => {
                panic!("expected type info")
            }
        }
    }
    fn emit_const(
        &mut self,
        val: &Value,
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
    ) -> BasicValueEnum<'ctx> {
        match val {
            Value::Int(n) => BasicValueEnum::IntValue(
                self.context
                    .i64_type()
                    .const_int((*n).try_into().unwrap(), false),
            ),
            Value::Float(n) => BasicValueEnum::FloatValue(self.context.f64_type().const_float(*n)),
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
            Value::String(str) => self.emit_str(scopeinfo, str).as_basic_value_enum(),
            _ => panic!("unreachable"),
        }
    }
    fn emit_value(
        &mut self,
        val: &Value,
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
        fv: FunctionValue<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        match val {
            Value::Int(n) => BasicValueEnum::IntValue(
                self.context
                    .i64_type()
                    .const_int((*n).try_into().unwrap(), false),
            ),
            Value::Float(n) => self.builder.build_bitcast(
                self.context.f64_type().const_float(*n),
                self.context.i64_type(),
                "",
            ),
            Value::Char(c) => BasicValueEnum::IntValue(
                self.context
                    .i8_type()
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
            Value::String(str) => self.emit_str(scopeinfo, str).as_basic_value_enum(),
            _ => panic!("unreachable"),
        }
    }
    fn emit_str(&mut self, scopeinfo: Rc<RefCell<ScopeInfo<'b>>>, str: &str) -> PointerValue<'ctx> {
        let ty = self.llvmstruct(
            &Type::PerfectMap(Box::new(Type::Int), Box::new(Type::Char)),
            scopeinfo.clone(),
        );
        let str = str.replace("\\n", "\n");
        let len = str.len();

        let keysptr = {
            let gv = self.module.add_global(
                self.context.i64_type().array_type(len as u32),
                Some(AddressSpace::default()),
                "g.keys",
            );
            gv.set_linkage(Linkage::Internal);
            let vals = self.context.i64_type().const_array(
                &(0..len)
                    .map(|i| self.context.i64_type().const_int(i as u64, false))
                    .collect::<Vec<_>>(),
            );
            gv.set_initializer(&vals.as_basic_value_enum());
            self.builder.build_bitcast(
                gv.as_pointer_value(),
                self.context.i64_type().ptr_type(AddressSpace::default()),
                "",
            )
        };
        let strptr = {
            let gv = self.module.add_global(
                self.context.i8_type().array_type(len as u32),
                Some(AddressSpace::default()),
                "g.values",
            );
            gv.set_linkage(Linkage::Internal);
            let vals = self.context.const_string(str.as_ref(), false);
            gv.set_initializer(&vals.as_basic_value_enum());
            self.builder.build_bitcast(
                gv.as_pointer_value(),
                self.context.i8_type().ptr_type(AddressSpace::default()),
                "",
            )
        };

        let gv = self
            .module
            .add_global(ty, Some(AddressSpace::default()), "g");
        gv.set_linkage(Linkage::Internal);

        let size = self.context.i64_type().const_int(len as u64, false);

        let argslen = self.context.i32_type().const_int(1, false).into();
        let args = {
            let gv = self.module.add_global(
                self.context.i32_type().array_type(1),
                Some(AddressSpace::default()),
                "g.args",
            );
            gv.set_linkage(Linkage::Internal);
            let vals = vec![self.context.i32_type().const_zero().into()];
            let vals = self.llvmconstarray(&Type::Int, scopeinfo.clone(), &vals);
            gv.set_initializer(&vals.as_basic_value_enum());
            self.builder.build_bitcast(
                gv.as_pointer_value(),
                self.context.i32_type().ptr_type(AddressSpace::default()),
                "",
            )
        };
        gv.set_initializer(
            &self
                .context
                .const_struct(&[size.into(), keysptr, strptr, argslen, args], false),
        );
        gv.as_pointer_value()
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
                BasicMetadataValueEnum::from(self.emit_expression(
                    expr,
                    scopeinfo.clone(),
                    fv,
                    false,
                ))
            })
            .collect();
        if *i == -1 {
            match *id {
                functions::PRINT_INT => self.emit_printf_call(&"%ld", &args),
                functions::PRINT_BOOL => self.emit_printf_call(&{ "%d" }, &args),
                functions::PRINT_LN => self.emit_printf_call(&{ "\n" }, &args),
                functions::PRINT_CHAR => self.emit_printf_call(&{ "%c" }, &args),
                functions::PRINT_FLOAT => self.emit_printf_call(
                    &{ "%f" },
                    &args
                        .iter()
                        .map(|f| {
                            self.builder
                                .build_bitcast(f.into_int_value(), self.context.f64_type(), "")
                                .into()
                        })
                        .collect::<Vec<_>>(),
                ),
                functions::HEAP_SIZE => self.emit_get_alloc(),
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
                    BasicMetadataValueEnum::from(self.emit_expression(
                        expr,
                        scopeinfo.clone(),
                        fv,
                        false,
                    ))
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
                functions::GET => self
                    .builder
                    .build_call(
                        self.map_get(&maptype, &v, &k, llvmmaptype, llvmkeytype, scopeinfo),
                        &allargs,
                        "",
                    )
                    .try_as_basic_value()
                    .unwrap_left(),
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
                        let initial_capacity: u32 = if Type::Unit.eq(&k) {
                            1
                        } else if Type::Bool.eq(&k) {
                            4
                        } else {
                            16
                        };
                        let fv = self.module.add_function(
                            &fname,
                            self.llvmfunctiontype(
                                &Type::Unit,
                                scopeinfo.clone(),
                                &[llvmmaptype.into()],
                                false,
                            ),
                            None,
                        );
                        let call_location = self.builder.get_insert_block().unwrap();
                        self.builder
                            .position_at_end(self.context.append_basic_block(fv, "entry"));

                        let map = fv.get_nth_param(0).unwrap().into_pointer_value();
                        let oldcapacity = self
                            .builder
                            .build_load(
                                self.builder
                                    .build_struct_gep(map, MAP_CAPACITY, "capacity")
                                    .unwrap(),
                                "",
                            )
                            .into_int_value();
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
                            #[cfg(feature = "heapsize")]
                            {
                                let keysize =
                                    self.llvmtype(&k, scopeinfo.clone()).size_of().unwrap();
                                self.remove_alloc(self.builder.build_int_mul(
                                    keysize,
                                    oldcapacity,
                                    "",
                                ))
                            }
                            self.builder.build_free(keys.into_pointer_value());
                            self.builder.build_store(
                                keyptr,
                                self.build_array_malloc(
                                    llvmkeytype,
                                    self.context
                                        .i32_type()
                                        .const_int(initial_capacity.into(), false),
                                )
                                .unwrap(),
                            );
                        }
                        if Type::Unit.ne(&v) {
                            let valuesptr = self
                                .builder
                                .build_struct_gep(map, map_values(&k), "values.ptr")
                                .unwrap();
                            let values = self.builder.build_load(valuesptr, "values");
                            #[cfg(feature = "heapsize")]
                            {
                                let valuesize =
                                    self.llvmtype(&v, scopeinfo.clone()).size_of().unwrap();
                                self.remove_alloc(self.builder.build_int_mul(
                                    valuesize,
                                    oldcapacity,
                                    "",
                                ))
                            }
                            self.builder.build_free(values.into_pointer_value());
                            self.builder.build_store(
                                valuesptr,
                                self.build_array_malloc(
                                    llvmvaluetype,
                                    self.context
                                        .i32_type()
                                        .const_int(initial_capacity.into(), false),
                                )
                                .unwrap(),
                            );
                        }
                        let statessptr = self
                            .builder
                            .build_struct_gep(map, MAP_STATES, "states.ptr")
                            .unwrap();
                        let states = self.builder.build_load(statessptr, "states");
                        #[cfg(feature = "heapsize")]
                        {
                            let statesize = self.statetype().size_of();
                            self.remove_alloc(self.builder.build_int_mul(
                                statesize,
                                oldcapacity,
                                "",
                            ))
                        }
                        self.builder.build_free(states.into_pointer_value());
                        self.builder.build_store(
                            statessptr,
                            self.build_calloc(
                                self.statetype(),
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
                                return true
                            }
                            return false
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
                                return true
                            }
                            i = (i + 1) % map.capacity
                        }
                        return false
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
                                &Type::Bool,
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
                                self.statetype().const_int(STATE_TOMB, false),
                            );
                            self.builder
                                .build_return(Some(&self.context.bool_type().const_all_ones()));
                            self.builder.position_at_end(afterif)
                        } else {
                            let hashargs = if Type::Unit.ne(&k) {
                                vec![fv.get_nth_param(KEY_PARAM).unwrap().into()]
                            } else {
                                vec![]
                            };
                            let hash = self
                                .builder
                                .build_call(self.hash(&k, scopeinfo.clone()), &hashargs, "")
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
                                    self.statetype().const_int(STATE_FREE, false),
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
                                    self.statetype().const_int(STATE_TOMB, false),
                                    "is_state_equal_tomb",
                                ),
                                afterwhile,
                                noearlyescape,
                            );
                            self.builder.position_at_end(noearlyescape);

                            //if
                            let ifbody = self.context.append_basic_block(fv, "ifbody");
                            let afterif = self.context.append_basic_block(fv, "afterif");

                            let keyidx = self.builder.build_load(key, "key_idx").into_int_value();
                            self.builder.build_conditional_branch(
                                self.builder
                                    .build_call(
                                        self.equal(&k, scopeinfo.clone()),
                                        &[
                                            keyidx.into(),
                                            fv.get_nth_param(KEY_PARAM).unwrap().into(),
                                        ],
                                        "is_key_equal",
                                    )
                                    .try_as_basic_value()
                                    .unwrap_left()
                                    .into_int_value(),
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
                                self.statetype().const_int(STATE_TOMB, false),
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

                            self.builder
                                .build_return(Some(&self.context.bool_type().const_all_ones()));
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
                        self.builder
                            .build_return(Some(&self.context.bool_type().const_zero()));
                        self.builder.position_at_end(call_block);
                        fv
                    };
                    self.builder
                        .build_call(fv, &allargs, "")
                        .try_as_basic_value()
                        .unwrap_left()
                }
                functions::GET_MAYBE => self
                    .builder
                    .build_call(
                        self.map_get_maybe(&maptype, &v, &k, llvmmaptype, llvmkeytype, scopeinfo),
                        &allargs,
                        "",
                    )
                    .try_as_basic_value()
                    .unwrap_left(),
                _ => {
                    panic!("unreachable")
                }
            }
        } else if let Some((_, Type::PerfectMap(k, v), i, _)) = var {
            let llvmkeytype = self.llvmtype(&k, scopeinfo.clone());
            let _llvmvaluetype = self.llvmtype(&v, scopeinfo.clone());
            let maptype = Type::PerfectMap(k.clone(), v.clone());
            let llvmmaptype = self.llvmtype(&maptype, scopeinfo.clone());
            let mapptr = *self.vars.get(&i).unwrap();
            let map = self.builder.build_load(mapptr, id).into_pointer_value();
            let mut allargs: Vec<BasicMetadataValueEnum<'ctx>> = vec![map.into()];
            let args: Vec<BasicMetadataValueEnum<'ctx>> = args
                .iter()
                .map(|expr| {
                    BasicMetadataValueEnum::from(self.emit_expression(
                        expr,
                        scopeinfo.clone(),
                        fv,
                        false,
                    ))
                })
                .collect();
            allargs.extend_from_slice(&args);
            match *id2 {
                functions::SIZE | functions::CAPACITY => {
                    let size = self
                        .builder
                        .build_struct_gep(map, CONST_MAP_SIZE, &(id.to_string() + ".size"))
                        .unwrap();
                    self.builder.build_load(size, "")
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
                        getConst(map, k) {
                            IF V == UNIT {
                                return
                            }
                            IF K == UNIT {
                                return map.values[0]
                            }
                            return = map.values[hash_perfect(k) % map.size]
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
                                                        CONST_MAP_VALUES,
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
                            let map = fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value();
                            let hash = self
                                .builder
                                .build_call(
                                    self.hash_perfect(&k, scopeinfo.clone()),
                                    &[
                                        self.builder
                                            .build_load(
                                                self.builder
                                                    .build_struct_gep(
                                                        map,
                                                        CONST_MAP_ARGS_LEN,
                                                        &(id.to_string() + ".argslen.ptr"),
                                                    )
                                                    .unwrap(),
                                                "argslen",
                                            )
                                            .into(),
                                        self.builder
                                            .build_load(
                                                self.builder
                                                    .build_struct_gep(
                                                        map,
                                                        CONST_MAP_ARGS,
                                                        &(id.to_string() + ".args.ptr"),
                                                    )
                                                    .unwrap(),
                                                "args",
                                            )
                                            .into(),
                                        fv.get_nth_param(KEY_PARAM).unwrap().into(),
                                    ],
                                    "",
                                )
                                .try_as_basic_value()
                                .unwrap_left();
                            let size = self.builder.build_load(
                                self.builder
                                    .build_struct_gep(
                                        map,
                                        CONST_MAP_SIZE,
                                        &(id.to_string() + ".size.ptr"),
                                    )
                                    .unwrap(),
                                "size",
                            );

                            let idx = self.builder.build_int_unsigned_rem(
                                hash.into_int_value(),
                                size.into_int_value(),
                                "",
                            );
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
                                                        CONST_MAP_VALUES,
                                                        &(id.to_string() + ".values.ptr"),
                                                    )
                                                    .unwrap(),
                                                "values",
                                            )
                                            .into_pointer_value(),
                                        &[idx],
                                        "",
                                    )
                                },
                                "",
                            )));
                        }
                        self.builder.position_at_end(call_block);
                        fv
                    };
                    self.builder
                        .build_call(fv, &allargs, "")
                        .try_as_basic_value()
                        .unwrap_left()
                }
                functions::GET_MAYBE => self
                    .builder
                    .build_call(
                        self.const_map_get_maybe(
                            &maptype,
                            &v,
                            &k,
                            llvmmaptype,
                            llvmkeytype,
                            scopeinfo,
                        ),
                        &allargs,
                        "",
                    )
                    .try_as_basic_value()
                    .unwrap_left(),
                _ => {
                    panic!()
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
                    false,
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
                            IF V == VOID {
                                return
                            }
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
                        if Type::Unit.eq(&v) {
                            self.builder.build_return(None);
                        } else {
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
                        }
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

                        let states = self
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
                        let statesi = unsafe {
                            self.builder.build_gep(
                                states,
                                &[self.context.i64_type().const_int(index, false)],
                                "map.states_i",
                            )
                        };
                        self.builder.build_conditional_branch(
                            self.builder.build_int_compare(
                                IntPredicate::EQ,
                                self.builder.build_load(statesi, "").into_int_value(),
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
        let fname = if !matches!(maptype, Type::Map(k, _v) if Type::Float.eq(k) || Type::Int.eq(k) )
        {
            format!("{}_insert", &maptype)
        } else {
            match maptype {
                Type::Map(_, v) => format!("{}_insert", &Type::Map(Box::new(Type::Int), v.clone())),
                _ => unreachable!(),
            }
        };
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
            if Type::Float.eq(k) {
                self.debug(
                    "INSERT KEY:%f\n",
                    [fv.get_nth_param(KEY_PARAM).unwrap().into()],
                );
            } else {
                self.debug(
                    "INSERT KEY:%lu\n",
                    [fv.get_nth_param(KEY_PARAM).unwrap().into()],
                );
            }
             */
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

            let capacity_before_rehash = self.builder.build_load(
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
                            capacity_before_rehash.into_int_value(),
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
                        self.statetype().const_int(STATE_TAKEN, false),
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
                let keyidx = self.builder.build_load(key, "keys_idx");
                self.builder.build_conditional_branch(
                    self.builder
                        .build_call(
                            self.equal(k, scopeinfo.clone()),
                            &[keyidx.into(), fv.get_nth_param(KEY_PARAM).unwrap().into()],
                            "is_key_equal",
                        )
                        .try_as_basic_value()
                        .unwrap_left()
                        .into_int_value(),
                    afterwhile,
                    whilebody,
                );
                self.builder.position_at_end(whilebody);
                self.builder.build_store(
                    idx,
                    self.builder.build_int_unsigned_rem(
                        self.builder.build_int_add(
                            self.builder.build_load(idx, "").into_int_value(),
                            self.context.i64_type().const_int(1, false),
                            "",
                        ),
                        capacity.into_int_value(),
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
                    self.statetype().const_int(STATE_TOMB, false),
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
                    self.statetype().const_int(STATE_TAKEN, false),
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
                self.statetype().const_int(STATE_TAKEN, false),
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
                                            map_values(&k),
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
                Type::Map(k, v) => {
                    /*
                    int h = capacity
                    int idx = 0
                    while idx < map.capacity {
                        if map.state[idx] == TAKEN {
                            h = h + hash(map.keys[idx]) + hash(map.values[idx])
                           }
                        idx = idx + 1
                    }
                    return hash

                    */

                    let map = fv.get_first_param().unwrap().into_pointer_value();
                    let capacity = self
                        .builder
                        .build_load(
                            self.builder
                                .build_struct_gep(map, MAP_CAPACITY, "map.capacity.ptr")
                                .unwrap(),
                            "capacity",
                        )
                        .into_int_value();
                    let h = self.builder.build_alloca(self.context.i64_type(), "h");
                    self.builder.build_store(h, capacity);
                    let idx = self.builder.build_alloca(self.context.i64_type(), "idx");
                    self.builder
                        .build_store(idx, self.context.i64_type().const_zero());

                    let mapstates = self
                        .builder
                        .build_load(
                            self.builder
                                .build_struct_gep(map, MAP_STATES, "map.states.ptr")
                                .unwrap(),
                            "map.states",
                        )
                        .into_pointer_value();
                    let mapkeys = self
                        .builder
                        .build_load(
                            self.builder
                                .build_struct_gep(map, MAP_KEYS, "map.keys.ptr")
                                .unwrap(),
                            "map.keys",
                        )
                        .into_pointer_value();
                    let mapvalues = self
                        .builder
                        .build_load(
                            self.builder
                                .build_struct_gep(map, map_values(&k), "map.values.ptr")
                                .unwrap(),
                            "map.values",
                        )
                        .into_pointer_value();

                    let whilecond = self.context.append_basic_block(fv, "whilecond");
                    let whilebody = self.context.append_basic_block(fv, "whilebody");
                    let afterwhile = self.context.append_basic_block(fv, "afterwhile");
                    self.builder.build_unconditional_branch(whilecond);
                    self.builder.position_at_end(whilecond);
                    let idxval = self.builder.build_load(idx, "").into_int_value();
                    self.builder.build_conditional_branch(
                        self.builder
                            .build_int_compare(IntPredicate::ULT, idxval, capacity, ""),
                        whilebody,
                        afterwhile,
                    );
                    let ifbody = self.context.append_basic_block(fv, "ifbody");
                    let afterif = self.context.append_basic_block(fv, "afterif");
                    self.builder.position_at_end(whilebody);
                    self.builder.build_conditional_branch(
                        self.builder.build_int_compare(
                            IntPredicate::EQ,
                            self.builder
                                .build_load(
                                    unsafe { self.builder.build_gep(mapstates, &[idxval], "") },
                                    "map.states_i",
                                )
                                .into_int_value(),
                            self.statetype().const_int(STATE_TAKEN, false),
                            "is_state_taken",
                        ),
                        ifbody,
                        afterif,
                    );
                    self.builder.position_at_end(ifbody);
                    let vh = self
                        .builder
                        .build_call(
                            self.hash(v, scopeinfo.clone()),
                            &{
                                if Type::Unit.eq(v) {
                                    vec![]
                                } else {
                                    vec![self
                                        .builder
                                        .build_load(
                                            unsafe {
                                                self.builder.build_gep(mapvalues, &[idxval], "")
                                            },
                                            "map.values_i",
                                        )
                                        .into()]
                                }
                            },
                            "value_i_hash",
                        )
                        .try_as_basic_value()
                        .unwrap_left();
                    let kh = self
                        .builder
                        .build_call(
                            self.hash(k, scopeinfo.clone()),
                            &{
                                if Type::Unit.eq(k) {
                                    vec![]
                                } else {
                                    vec![self
                                        .builder
                                        .build_load(
                                            unsafe {
                                                self.builder.build_gep(mapkeys, &[idxval], "")
                                            },
                                            "map.keys_i",
                                        )
                                        .into()]
                                }
                            },
                            "key_i_hash",
                        )
                        .try_as_basic_value()
                        .unwrap_left();
                    self.builder.build_store(
                        h,
                        self.builder.build_int_add(
                            self.builder.build_load(h, "").into_int_value(),
                            self.builder.build_int_add(
                                vh.into_int_value(),
                                kh.into_int_value(),
                                "",
                            ),
                            "",
                        ),
                    );
                    self.builder.build_unconditional_branch(afterif);
                    self.builder.position_at_end(afterif);
                    self.builder.build_store(
                        idx,
                        self.builder.build_int_add(
                            idxval,
                            self.context.i64_type().const_int(1, false),
                            "",
                        ),
                    );
                    self.builder.build_unconditional_branch(whilecond);
                    self.builder.position_at_end(afterwhile);
                    self.builder
                        .build_return(Some(&self.builder.build_load(h, "")));
                }
                Type::StructMap(_t) => {
                    /*
                    hashStructMap(map){
                        int h = 0
                        int idx = 0
                        while idx < map.size {
                            if map.state[idx] == TAKEN {
                                h = h + hash(map.values[idx])
                            }
                            idx = idx + 1
                        }
                        return hash
                    }
                     */
                    todo!()
                }
                Type::PerfectMap(k, v) => {
                    /*
                    int h = map.size
                    int idx = 0
                    while idx < map.size {
                        h = h ^ (hash(map.values[idx]) rot by hash(map.keys[idx]))
                        idx = idx + 1
                    }
                    return hash

                    */
                    let map = fv.get_first_param().unwrap().into_pointer_value();
                    let size = self
                        .builder
                        .build_load(
                            self.builder
                                .build_struct_gep(map, CONST_MAP_SIZE, "map.size.ptr")
                                .unwrap(),
                            "size",
                        )
                        .into_int_value();
                    let h = self.builder.build_alloca(self.context.i64_type(), "h");
                    self.builder.build_store(h, size);
                    let idx = self.builder.build_alloca(self.context.i64_type(), "idx");
                    self.builder
                        .build_store(idx, self.context.i64_type().const_zero());

                    let mapkeys = self
                        .builder
                        .build_load(
                            self.builder
                                .build_struct_gep(map, CONST_MAP_KEYS, "map.keys.ptr")
                                .unwrap(),
                            "map.keys",
                        )
                        .into_pointer_value();
                    let mapvalues = self
                        .builder
                        .build_load(
                            self.builder
                                .build_struct_gep(map, CONST_MAP_VALUES, "map.values.ptr")
                                .unwrap(),
                            "map.values",
                        )
                        .into_pointer_value();

                    let whilecond = self.context.append_basic_block(fv, "whilecond");
                    let whilebody = self.context.append_basic_block(fv, "whilebody");
                    let afterwhile = self.context.append_basic_block(fv, "afterwhile");
                    self.builder.build_unconditional_branch(whilecond);
                    self.builder.position_at_end(whilecond);
                    let idxval = self.builder.build_load(idx, "").into_int_value();
                    self.builder.build_conditional_branch(
                        self.builder
                            .build_int_compare(IntPredicate::ULT, idxval, size, ""),
                        whilebody,
                        afterwhile,
                    );
                    self.builder.position_at_end(whilebody);
                    let vh = self
                        .builder
                        .build_call(
                            self.hash(v, scopeinfo.clone()),
                            &{
                                if Type::Unit.eq(v) {
                                    vec![]
                                } else {
                                    vec![self
                                        .builder
                                        .build_load(
                                            unsafe {
                                                self.builder.build_gep(mapvalues, &[idxval], "")
                                            },
                                            "map.values_i",
                                        )
                                        .into()]
                                }
                            },
                            "value_i_hash",
                        )
                        .try_as_basic_value()
                        .unwrap_left();
                    let kh = self
                        .builder
                        .build_call(
                            self.hash(k, scopeinfo.clone()),
                            &{
                                if Type::Unit.eq(k) {
                                    vec![]
                                } else {
                                    vec![self
                                        .builder
                                        .build_load(
                                            unsafe {
                                                self.builder.build_gep(mapkeys, &[idxval], "")
                                            },
                                            "map.keys_i",
                                        )
                                        .into()]
                                }
                            },
                            "key_i_hash",
                        )
                        .try_as_basic_value()
                        .unwrap_left();

                    //h = h ^ (hash(map.values[idx]) rot by hash(map.keys[idx]))
                    //vh kh
                    self.builder.build_store(
                        h,
                        self.builder.build_xor(
                            self.builder.build_load(h, "").into_int_value(),
                            self.builder
                                .build_call(
                                    self.module.get_function(ROT).unwrap(),
                                    &[vh.into(), vh.into(), kh.into()],
                                    "",
                                )
                                .try_as_basic_value()
                                .unwrap_left()
                                .into_int_value(),
                            "",
                        ),
                    );
                    self.builder.build_store(
                        idx,
                        self.builder.build_int_add(
                            idxval,
                            self.context.i64_type().const_int(1, false),
                            "",
                        ),
                    );
                    self.builder.build_unconditional_branch(whilecond);
                    self.builder.position_at_end(afterwhile);
                    self.builder
                        .build_return(Some(&self.builder.build_load(h, "")));
                }
                Type::Unit => {
                    self.builder.build_return(Some(
                        &self.llvmtype(&Type::Int, scopeinfo.clone()).const_zero(),
                    ));
                }
                Type::Float => {
                    self.builder.build_return(Some(&self.builder.build_bitcast(
                        fv.get_nth_param(0).unwrap(),
                        self.llvmtype(&Type::Int, scopeinfo),
                        "",
                    )));
                }
                _ => {
                    self.builder.build_return(Some(&self.builder.build_int_cast(
                        fv.get_nth_param(0).unwrap().into_int_value(),
                        self.llvmtype(&Type::Int, scopeinfo).into_int_type(),
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

    //precondition needs key type to not be unit type
    fn rehash(
        &mut self,
        t: &Type<'b>,
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
    ) -> FunctionValue<'ctx> {
        /*
        fn rehash(map) {
            newcapacity = map.size * 3 + 16
            newkeys = malloc newcapacity
            IF V != VOID{
                newvalues = malloc newcapacity
            }
            newstates = calloc newcapacity
            for i in 0 .. map.capacity {
                if map.states[i] = TAKEN {
                    k = map.keys[i]
                    IF V != VOID{
                        v = map.values[i]
                    }

                    newi = hash(k) % newcapacity
                    while newstates[newi] == TAKEN{
                        newi = (newi + 1) % newcapacity
                    }
                    newkeys[newi] = K
                    IF V != VOID{
                        newvalues[newi] = map.values[i]
                    }
                    newstates[newi] = TAKEN
                }
            }
            free map.keys
            map.keys = newkeys
            free map.values
            IF V != VOID{
                free map.values
                map.values = newvalues
            }
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
                        self.context.i64_type().const_int(3, false),
                        "",
                    ),
                    self.context.i64_type().const_int(16, false),
                    "",
                );

                self.debug(
                    "REHASHING with capacity %lu -> %lu\n",
                    [oldcap.into(), newcap.into()],
                );
                self.debug(
                    "\tmalloc(%lu) \n",
                    [self
                        .builder
                        .build_int_mul(llvmk.size_of().unwrap(), newcap, "")
                        .into()],
                );
                let newkeys = self.build_array_malloc(llvmk, newcap).unwrap();
                let newkeys = self
                    .builder
                    .build_bitcast(newkeys, llvmk.ptr_type(AddressSpace::default()), "")
                    .into_pointer_value();

                self.debug("\tkeys alocated\n", []);

                let newvalues = if Type::Unit.ne(v) {
                    Some(self.build_array_malloc(llvmv, newcap).unwrap())
                } else {
                    None
                };
                self.debug("\tvalues alocated\n", []);
                let newstates = self.build_calloc(
                    self.statetype(),
                    self.builder
                        .build_int_cast(newcap, self.context.i32_type(), "")
                        .into(),
                );
                self.debug("\tstates alocated\n", []);

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
                        self.statetype().const_int(STATE_TAKEN, false),
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
                        self.statetype().const_int(STATE_TAKEN, false),
                        "is_state_taken",
                    ),
                    whilebody,
                    afterwhile,
                );

                self.builder.position_at_end(whilebody);
                self.builder.build_store(
                    newiptr,
                    self.builder.build_int_unsigned_rem(
                        self.builder.build_int_add(
                            newival,
                            self.context.i64_type().const_int(1, false),
                            "newiinc",
                        ),
                        newcap,
                        "",
                    ),
                );
                self.builder.build_unconditional_branch(whilecond);

                self.builder.position_at_end(afterwhile);

                self.builder.build_store(
                    unsafe { self.builder.build_gep(newkeys, &[newival], "newkeys_i") },
                    key,
                );
                if Type::Unit.ne(v) {
                    let mapvaluesptr = self
                        .builder
                        .build_struct_gep(map, map_values(&k), "map.values.ptr")
                        .unwrap();
                    let mapvalues = self
                        .builder
                        .build_load(mapvaluesptr, "map.values")
                        .into_pointer_value();
                    let value = self.builder.build_load(
                        unsafe { self.builder.build_gep(mapvalues, &[ival], "") },
                        "value",
                    );
                    self.builder.build_store(
                        unsafe {
                            self.builder
                                .build_gep(newvalues.unwrap(), &[newival], "newvalues_i")
                        },
                        value,
                    );
                }

                self.builder.build_store(
                    unsafe { self.builder.build_gep(newstates, &[newival], "newstates_i") },
                    self.statetype().const_int(STATE_TAKEN, false),
                );
                //self.debug("\tKEY:%lu IDX:%lu -> IDX:%lu\n", [key.into(), ival.into(), newival.into()]);

                self.builder.build_unconditional_branch(afterif);
                self.builder.position_at_end(afterif);
                self.builder.build_unconditional_branch(forinc);
                self.builder.position_at_end(afterfor);
                #[cfg(feature = "heapsize")]
                {
                    self.remove_alloc(self.builder.build_int_mul(
                        llvmk.size_of().unwrap(),
                        oldcap,
                        "",
                    ))
                }
                self.builder.build_free(mapkeys);
                self.builder.build_store(mapkeysptr, newkeys);
                if Type::Unit.ne(v) {
                    let mapvaluesptr = self
                        .builder
                        .build_struct_gep(map, map_values(k), "map.values.ptr")
                        .unwrap();
                    let mapvalues = self
                        .builder
                        .build_load(mapvaluesptr, "map.values")
                        .into_pointer_value();
                    #[cfg(feature = "heapsize")]
                    {
                        self.remove_alloc(self.builder.build_int_mul(
                            llvmv.size_of().unwrap(),
                            oldcap,
                            "",
                        ))
                    }
                    self.builder.build_free(mapvalues);
                    self.builder.build_store(mapvaluesptr, newvalues.unwrap());
                }
                #[cfg(feature = "heapsize")]
                {
                    self.remove_alloc(self.builder.build_int_mul(
                        self.statetype().size_of(),
                        oldcap,
                        "",
                    ))
                }
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
                let map = self.build_malloc(llvmmaptype).unwrap();
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
                    self.build_calloc(
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
                    map.states[i] = FREE
                    return true
                }
                return false

            }
            */
            let fv = self.module.add_function(
                &fname,
                self.llvmfunctiontype(&Type::Bool, scopeinfo.clone(), &params, false),
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
            self.builder
                .build_store(flagi, self.context.bool_type().const_zero());
            self.builder
                .build_return(Some(&self.context.bool_type().const_all_ones()));
            self.builder.position_at_end(afterif);

            self.builder
                .build_return(Some(&self.context.bool_type().const_zero()));
            self.builder.position_at_end(call_block);
            fv
        } else {
            panic!()
        }
    }

    fn equal(&mut self, t: &Type<'b>, scopeinfo: Rc<RefCell<ScopeInfo<'b>>>) -> FunctionValue {
        let s = format!("equal_{t}");
        let fv = if let Some(fv) = self.module.get_function(&s) {
            fv
        } else {
            let args = if Type::Unit.ne(t) {
                vec![
                    self.llvmtype(t, scopeinfo.clone()).into(),
                    self.llvmtype(t, scopeinfo.clone()).into(),
                ]
            } else {
                vec![]
            };
            let fv = self.module.add_function(
                &s,
                self.llvmfunctiontype(&Type::Bool, scopeinfo.clone(), &args, false),
                None,
            );
            let call_block = self.builder.get_insert_block();
            self.builder
                .position_at_end(self.context.append_basic_block(fv, "entry"));
            match t {
                Type::Unit => {
                    self.builder
                        .build_return(Some(&self.context.bool_type().const_all_ones()));
                }
                Type::Int | Type::Bool | Type::Char | Type::Float => {
                    self.builder
                        .build_return(Some(&self.builder.build_int_compare(
                            IntPredicate::EQ,
                            fv.get_nth_param(0).unwrap().into_int_value(),
                            fv.get_nth_param(1).unwrap().into_int_value(),
                            "eq",
                        )));
                }
                Type::Map(k, v) => {
                    /*
                        mapequal(a,b){
                            if a.size() != b.size() {
                                return false
                            }
                            while idx < a.size() {
                                if a.states[idx] == taken{
                                    {void -> V } r = b.getMaybe(k)
                                    if r.size() == 0 {
                                        return false
                                    }
                                    if r.get() != v {
                                        return false
                                    }
                                }
                                idx += 1
                            }

                            return true
                        }
                    */
                    let a = fv.get_nth_param(0).unwrap().into_pointer_value();
                    let b = fv.get_nth_param(1).unwrap().into_pointer_value();

                    let ifbody = self.context.append_basic_block(fv, "ifbody");
                    let afterif = self.context.append_basic_block(fv, "afterif");
                    self.builder.build_conditional_branch(
                        self.builder.build_int_compare(
                            IntPredicate::NE,
                            self.builder
                                .build_load(
                                    self.builder.build_struct_gep(a, MAP_SIZE, "size").unwrap(),
                                    "",
                                )
                                .into_int_value(),
                            self.builder
                                .build_load(
                                    self.builder.build_struct_gep(b, MAP_SIZE, "size").unwrap(),
                                    "",
                                )
                                .into_int_value(),
                            "",
                        ),
                        ifbody,
                        afterif,
                    );
                    self.builder.position_at_end(ifbody);
                    //self.emit_printf_call(&"NOT EQUAL\n", &[]);
                    self.builder
                        .build_return(Some(&self.context.bool_type().const_zero()));
                    self.builder.position_at_end(afterif);
                    //self.emit_printf_call(&"PASS SIZE CHECK\n", &[]);
                    let idx = self.builder.build_alloca(self.context.i64_type(), "idx");
                    self.builder
                        .build_store(idx, self.context.i64_type().const_zero());

                    let a_capacity = self
                        .builder
                        .build_load(
                            self.builder
                                .build_struct_gep(a, MAP_CAPACITY, "capacity")
                                .unwrap(),
                            "",
                        )
                        .into_int_value();
                    let states = self
                        .builder
                        .build_load(
                            self.builder
                                .build_struct_gep(a, MAP_STATES, "map.states.ptr")
                                .unwrap(),
                            "states",
                        )
                        .into_pointer_value();

                    let whilecond = self.context.append_basic_block(fv, "whilecond");
                    let whilebody = self.context.append_basic_block(fv, "whilebody");
                    let afterwhile = self.context.append_basic_block(fv, "afterwhile");
                    self.builder.build_unconditional_branch(whilecond);
                    self.builder.position_at_end(whilecond);
                    let idxval = self.builder.build_load(idx, "").into_int_value();
                    //self.emit_printf_call(&"idx:%d\n", &[idxval.into()]);
                    self.builder.build_conditional_branch(
                        self.builder
                            .build_int_compare(IntPredicate::ULT, idxval, a_capacity, ""),
                        whilebody,
                        afterwhile,
                    );
                    self.builder.position_at_end(whilebody);
                    let validentry = self.context.append_basic_block(fv, "validentry");
                    let afterifa = self.context.append_basic_block(fv, "afterifa");
                    let afterifb = self.context.append_basic_block(fv, "afterifb");
                    let aftervalid = self.context.append_basic_block(fv, "aftervalid");

                    let stateidx = self.builder.build_load(
                        unsafe { self.builder.build_gep(states, &[idxval], "") },
                        "state_idx",
                    );

                    self.builder.build_conditional_branch(
                        self.builder.build_int_compare(
                            IntPredicate::EQ,
                            stateidx.into_int_value(),
                            self.statetype().const_int(STATE_TAKEN, false),
                            "is_taken",
                        ),
                        validentry,
                        aftervalid,
                    );
                    self.builder.position_at_end(validentry);
                    //self.emit_printf_call(&"is valid\n", &[]);

                    let llvmmaptype =
                        self.llvmtype(&Type::Map(k.clone(), v.clone()), scopeinfo.clone());
                    let llvmkeytype = self.llvmtype(k, scopeinfo.clone());
                    let getmaybeargs = if Type::Unit.eq(k) {
                        vec![b.into()]
                    } else {
                        let keyidx = self.builder.build_load(
                            unsafe {
                                self.builder.build_gep(
                                    self.builder
                                        .build_load(
                                            self.builder
                                                .build_struct_gep(a, MAP_KEYS, "map.keys.ptr")
                                                .unwrap(),
                                            "keys",
                                        )
                                        .into_pointer_value(),
                                    &[idxval],
                                    "",
                                )
                            },
                            "key_idx",
                        );
                        vec![b.into(), keyidx.into()]
                    };

                    let r = self
                        .builder
                        .build_call(
                            self.map_get_maybe(
                                &Type::Map(Box::new(Type::Unit), v.clone()),
                                v,
                                k,
                                llvmmaptype,
                                llvmkeytype,
                                scopeinfo.clone(),
                            ),
                            &getmaybeargs,
                            "r",
                        )
                        .try_as_basic_value()
                        .unwrap_left()
                        .into_pointer_value();

                    let rsize = self
                        .builder
                        .build_load(
                            self.builder
                                .build_struct_gep(r, MAP_SIZE, "r.size.ptr")
                                .unwrap(),
                            "r.size",
                        )
                        .into_int_value();
                    //self.emit_printf_call(&"key match: %d \n", &[rsize.into()]);
                    self.builder.build_conditional_branch(
                        self.builder.build_int_compare(
                            IntPredicate::EQ,
                            rsize,
                            self.context.i64_type().const_zero(),
                            "",
                        ),
                        ifbody,
                        afterifa,
                    );
                    self.builder.position_at_end(afterifa);

                    let mapvoidtoval = self.llvmtype(
                        &Type::Map(Box::new(Type::Unit), v.clone()),
                        scopeinfo.clone(),
                    );

                    //self.emit_printf_call(&"key val: %d \n", &[rget.into()]);
                    if Type::Unit.ne(v) {
                        let rget = self
                            .builder
                            .build_call(
                                self.map_get(
                                    &Type::Map(Box::new(Type::Unit), v.clone()),
                                    v,
                                    &Type::Unit,
                                    mapvoidtoval,
                                    self.context.custom_width_int_type(0).into(),
                                    scopeinfo.clone(),
                                ),
                                &[r.into()],
                                "",
                            )
                            .try_as_basic_value()
                            .unwrap_left();
                        let valueidx = self.builder.build_load(
                            unsafe {
                                self.builder.build_gep(
                                    self.builder
                                        .build_load(
                                            self.builder
                                                .build_struct_gep(
                                                    a,
                                                    map_values(&k),
                                                    "map.values.ptr",
                                                )
                                                .unwrap(),
                                            "values",
                                        )
                                        .into_pointer_value(),
                                    &[idxval],
                                    "",
                                )
                            },
                            "value_idx",
                        );
                        self.builder.build_conditional_branch(
                            self.builder
                                .build_call(
                                    self.equal(&v, scopeinfo.clone()),
                                    &[rget.into(), valueidx.into()],
                                    "",
                                )
                                .try_as_basic_value()
                                .unwrap_left()
                                .into_int_value(),
                            afterifb,
                            ifbody,
                        );
                    } else {
                        self.builder.build_unconditional_branch(afterifb);
                    }

                    self.builder.position_at_end(afterifb);
                    self.builder.build_unconditional_branch(aftervalid);
                    self.builder.position_at_end(aftervalid);
                    self.builder.build_store(
                        idx,
                        self.builder.build_int_add(
                            idxval,
                            self.context.i64_type().const_int(1, false),
                            "",
                        ),
                    );
                    self.builder.build_unconditional_branch(whilecond);
                    self.builder.position_at_end(afterwhile);
                    self.builder
                        .build_return(Some(&self.context.bool_type().const_all_ones()));
                }
                Type::PerfectMap(k, v) => {
                    /*
                        constmapequal(a,b){
                            if a.size() != b.size() {
                                return false
                            }
                            while idx < a.size() {
                                    {void -> V } r = b.getMaybe(k)
                                    if r.size() == 0 {
                                        return false
                                    }
                                    if r.get() != v {
                                        return false
                                    }
                                idx += 1
                            }

                            return true
                        }
                    */
                    let maptype = Type::PerfectMap(k.clone(), v.clone());
                    let llvmmaptype = self.llvmtype(&maptype, scopeinfo.clone());
                    let llvmkeytype = self.llvmtype(k, scopeinfo.clone());

                    let a = fv.get_nth_param(0).unwrap().into_pointer_value();
                    let b = fv.get_nth_param(1).unwrap().into_pointer_value();

                    let ifbody = self.context.append_basic_block(fv, "ifbody");
                    let afterif = self.context.append_basic_block(fv, "afterif");
                    self.builder.build_conditional_branch(
                        self.builder.build_int_compare(
                            IntPredicate::NE,
                            self.builder
                                .build_load(
                                    self.builder
                                        .build_struct_gep(a, CONST_MAP_SIZE, "size")
                                        .unwrap(),
                                    "",
                                )
                                .into_int_value(),
                            self.builder
                                .build_load(
                                    self.builder
                                        .build_struct_gep(b, CONST_MAP_SIZE, "size")
                                        .unwrap(),
                                    "",
                                )
                                .into_int_value(),
                            "",
                        ),
                        ifbody,
                        afterif,
                    );
                    self.builder.position_at_end(ifbody);
                    //self.emit_printf_call(&"NOT EQUAL\n", &[]);
                    self.builder
                        .build_return(Some(&self.context.bool_type().const_zero()));
                    self.builder.position_at_end(afterif);
                    //self.emit_printf_call(&"PASS SIZE CHECK\n", &[]);
                    let idx = self.builder.build_alloca(self.context.i64_type(), "idx");
                    self.builder
                        .build_store(idx, self.context.i64_type().const_zero());

                    let a_size = self
                        .builder
                        .build_load(
                            self.builder
                                .build_struct_gep(a, CONST_MAP_SIZE, "size")
                                .unwrap(),
                            "",
                        )
                        .into_int_value();

                    let whilecond = self.context.append_basic_block(fv, "whilecond");
                    let whilebody = self.context.append_basic_block(fv, "whilebody");
                    let afterwhile = self.context.append_basic_block(fv, "afterwhile");
                    self.builder.build_unconditional_branch(whilecond);
                    self.builder.position_at_end(whilecond);
                    let idxval = self.builder.build_load(idx, "").into_int_value();
                    //self.emit_printf_call(&"idx:%d\n", &[idxval.into()]);
                    self.builder.build_conditional_branch(
                        self.builder
                            .build_int_compare(IntPredicate::ULT, idxval, a_size, ""),
                        whilebody,
                        afterwhile,
                    );
                    self.builder.position_at_end(whilebody);
                    let afterifa = self.context.append_basic_block(fv, "afterifa");
                    let afterifb = self.context.append_basic_block(fv, "afterifb");

                    let getmaybeargs = if Type::Unit.eq(k) {
                        vec![b.into()]
                    } else {
                        let keyidx = self.builder.build_load(
                            unsafe {
                                self.builder.build_gep(
                                    self.builder
                                        .build_load(
                                            self.builder
                                                .build_struct_gep(a, CONST_MAP_KEYS, "map.keys.ptr")
                                                .unwrap(),
                                            "keys",
                                        )
                                        .into_pointer_value(),
                                    &[idxval],
                                    "",
                                )
                            },
                            "key_idx",
                        );
                        vec![b.into(), keyidx.into()]
                    };
                    let r = self
                        .builder
                        .build_call(
                            self.const_map_get_maybe(
                                &maptype,
                                &v,
                                &k,
                                llvmmaptype,
                                llvmkeytype,
                                scopeinfo.clone(),
                            ),
                            &getmaybeargs,
                            "r",
                        )
                        .try_as_basic_value()
                        .unwrap_left()
                        .into_pointer_value();

                    let rsize = self
                        .builder
                        .build_load(
                            self.builder
                                .build_struct_gep(r, MAP_SIZE, "r.size.ptr")
                                .unwrap(),
                            "r.size",
                        )
                        .into_int_value();
                    //self.emit_printf_call(&"key match: %d \n", &[rsize.into()]);
                    self.builder.build_conditional_branch(
                        self.builder.build_int_compare(
                            IntPredicate::EQ,
                            rsize,
                            self.context.i64_type().const_zero(),
                            "",
                        ),
                        ifbody,
                        afterifa,
                    );
                    self.builder.position_at_end(afterifa);

                    let mapvoidtoval = self.llvmtype(
                        &Type::Map(Box::new(Type::Unit), v.clone()),
                        scopeinfo.clone(),
                    );

                    //self.emit_printf_call(&"key val: %d \n", &[rget.into()]);
                    if Type::Unit.ne(v) {
                        let rget = self
                            .builder
                            .build_call(
                                self.map_get(
                                    &Type::Map(Box::new(Type::Unit), v.clone()),
                                    v,
                                    &Type::Unit,
                                    mapvoidtoval,
                                    self.context.custom_width_int_type(0).into(),
                                    scopeinfo.clone(),
                                ),
                                &[r.into()],
                                "",
                            )
                            .try_as_basic_value()
                            .unwrap_left();
                        let valueidx = self.builder.build_load(
                            unsafe {
                                self.builder.build_gep(
                                    self.builder
                                        .build_load(
                                            self.builder
                                                .build_struct_gep(
                                                    a,
                                                    CONST_MAP_VALUES,
                                                    "map.values.ptr",
                                                )
                                                .unwrap(),
                                            "values",
                                        )
                                        .into_pointer_value(),
                                    &[idxval],
                                    "",
                                )
                            },
                            "value_idx",
                        );
                        self.builder.build_conditional_branch(
                            self.builder
                                .build_call(
                                    self.equal(&v, scopeinfo.clone()),
                                    &[rget.into(), valueidx.into()],
                                    "",
                                )
                                .try_as_basic_value()
                                .unwrap_left()
                                .into_int_value(),
                            afterifb,
                            ifbody,
                        );
                    } else {
                        self.builder.build_unconditional_branch(afterifb);
                    }

                    self.builder.position_at_end(afterifb);
                    self.builder.build_store(
                        idx,
                        self.builder.build_int_add(
                            idxval,
                            self.context.i64_type().const_int(1, false),
                            "",
                        ),
                    );
                    self.builder.build_unconditional_branch(whilecond);
                    self.builder.position_at_end(afterwhile);
                    self.builder
                        .build_return(Some(&self.context.bool_type().const_all_ones()));
                }
                Type::StructMap(_t) => todo!(),
            }

            if let Some(bb) = call_block {
                self.builder.position_at_end(bb);
            }
            fv
        };
        fv
    }

    fn map_get(
        &mut self,
        maptype: &Type<'b>,
        v: &Type<'b>,
        k: &Type<'b>,
        llvmmaptype: BasicTypeEnum<'ctx>,
        llvmkeytype: BasicTypeEnum<'ctx>,
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
    ) -> FunctionValue<'ctx> {
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
                                            map_values(&k),
                                            &("map.values.ptr"),
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
                            &("map.capacity.ptr"),
                        )
                        .unwrap(),
                    "capacity",
                );

                let states = self.builder.build_load(
                    self.builder
                        .build_struct_gep(
                            fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                            MAP_STATES,
                            &("map.states.ptr"),
                        )
                        .unwrap(),
                    "states",
                );

                let keys = self.builder.build_load(
                    self.builder
                        .build_struct_gep(
                            fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                            MAP_KEYS,
                            &("map.keys.ptr"),
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
                        self.statetype().const_int(STATE_FREE, false),
                        "is_not_state_free",
                    ),
                    whilebody,
                    afterwhile,
                );
                self.builder.position_at_end(whilebody);

                //if
                let ifbody = self.context.append_basic_block(fv, "ifbody");
                let afterif = self.context.append_basic_block(fv, "afterif");
                let keyidx = self.builder.build_load(key, "key_idx");
                let _cond = self.builder.build_and(
                    self.builder.build_int_compare(
                        IntPredicate::EQ,
                        self.builder.build_load(state, "state_idx").into_int_value(),
                        self.statetype().const_int(STATE_TAKEN, false),
                        "is_state_taken",
                    ),
                    self.builder
                        .build_call(
                            self.equal(&k, scopeinfo.clone()),
                            &[keyidx.into(), fv.get_nth_param(KEY_PARAM).unwrap().into()],
                            "is_key_equal",
                        )
                        .try_as_basic_value()
                        .unwrap_left()
                        .into_int_value(),
                    "ifcond",
                );
                self.builder.build_conditional_branch(
                    self.builder.build_and(
                        self.builder.build_int_compare(
                            IntPredicate::EQ,
                            self.builder.build_load(state, "state_idx").into_int_value(),
                            self.statetype().const_int(STATE_TAKEN, false),
                            "is_state_taken",
                        ),
                        self.builder
                            .build_call(
                                self.equal(&k, scopeinfo.clone()),
                                &[keyidx.into(), fv.get_nth_param(KEY_PARAM).unwrap().into()],
                                "is_key_equal",
                            )
                            .try_as_basic_value()
                            .unwrap_left()
                            .into_int_value(),
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
                                            map_values(&k),
                                            &("map.values.ptr"),
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
                    self.builder.build_int_unsigned_rem(
                        self.builder.build_int_add(
                            self.builder.build_load(idx, "").into_int_value(),
                            self.context.i64_type().const_int(1, false),
                            "",
                        ),
                        capacity.into_int_value(),
                        "",
                    ),
                );
                self.builder.build_unconditional_branch(whilecond);

                self.builder.position_at_end(afterwhile);
                self.builder
                    .build_return(Some(&self.llvmtype(&v, scopeinfo).const_zero()));
            }
            self.builder.position_at_end(call_block);
            fv
        };
        fv
    }

    fn const_map_get_maybe(
        &mut self,
        maptype: &Type<'b>,
        v: &Type<'b>,
        k: &Type<'b>,
        llvmmaptype: BasicTypeEnum<'ctx>,
        llvmkeytype: BasicTypeEnum<'ctx>,
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
    ) -> FunctionValue<'ctx> {
        /*
        getMaybeConst(map, k) {
            returnval = new <void,V>
            IF K == UNIT {
                if map.size == 1 {
                    returnval.insert(map.values[0])
                }
                return returval
            }
            i = perfecthash(k) % map.size
            if map.keys[i] == K {
                returnval.insert(map.values[i])
            }
            return returnval
        }
        */
        let fname = format!("{}_get_maybe", &maptype);
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
            let returntype = Type::Map(Box::new(Type::Unit), Box::new(v.clone()));
            let fv = self.module.add_function(
                &fname,
                self.llvmfunctiontype(&returntype, scopeinfo.clone(), &param_types, false),
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
            let size = self.builder.build_load(
                self.builder
                    .build_struct_gep(
                        fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                        CONST_MAP_SIZE,
                        &("map.size.ptr"),
                    )
                    .unwrap(),
                "size",
            );
            let ifbody = self.context.append_basic_block(fv, "ifbody");
            let afterif = self.context.append_basic_block(fv, "afterif");
            if Type::Unit.eq(&k) {
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
                                                CONST_MAP_VALUES,
                                                &("map.values.ptr"),
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
                self.builder.position_at_end(afterif);
            } else {
                let hash = self
                    .builder
                    .build_call(
                        self.hash_perfect(&k, scopeinfo.clone()),
                        &[
                            self.builder
                                .build_load(
                                    self.builder
                                        .build_struct_gep(
                                            fv.get_nth_param(MAP_PARAM)
                                                .unwrap()
                                                .into_pointer_value(),
                                            CONST_MAP_ARGS_LEN,
                                            "argslen.ptr",
                                        )
                                        .unwrap(),
                                    "argslen",
                                )
                                .into(),
                            self.builder
                                .build_load(
                                    self.builder
                                        .build_struct_gep(
                                            fv.get_nth_param(MAP_PARAM)
                                                .unwrap()
                                                .into_pointer_value(),
                                            CONST_MAP_ARGS,
                                            "args.ptr",
                                        )
                                        .unwrap(),
                                    "args",
                                )
                                .into(),
                            fv.get_nth_param(KEY_PARAM).unwrap().into(),
                        ],
                        "",
                    )
                    .try_as_basic_value()
                    .unwrap_left();

                let idx = self.builder.build_int_unsigned_rem(
                    hash.into_int_value(),
                    size.into_int_value(),
                    "",
                );
                let lhs = self.builder.build_load(
                    unsafe {
                        self.builder.build_gep(
                            self.builder
                                .build_load(
                                    self.builder
                                        .build_struct_gep(
                                            fv.get_nth_param(MAP_PARAM)
                                                .unwrap()
                                                .into_pointer_value(),
                                            CONST_MAP_KEYS,
                                            &("map.keys.ptr"),
                                        )
                                        .unwrap(),
                                    "key",
                                )
                                .into_pointer_value(),
                            &[idx],
                            "",
                        )
                    },
                    "",
                );
                self.builder.build_conditional_branch(
                    self.builder
                        .build_call(
                            self.equal(&k, scopeinfo.clone()),
                            &[lhs.into(), fv.get_nth_param(KEY_PARAM).unwrap().into()],
                            "is_key_equal",
                        )
                        .try_as_basic_value()
                        .unwrap_left()
                        .into_int_value(),
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
                                                CONST_MAP_VALUES,
                                                &("map.values.ptr"),
                                            )
                                            .unwrap(),
                                        "values",
                                    )
                                    .into_pointer_value(),
                                &[idx],
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
            }

            self.builder.build_return(Some(&returnval));
            self.builder.position_at_end(call_block);
            fv
        };
        fv
    }

    fn map_get_maybe(
        &mut self,
        maptype: &Type<'b>,
        v: &Type<'b>,
        k: &Type<'b>,
        llvmmaptype: BasicTypeEnum<'ctx>,
        llvmkeytype: BasicTypeEnum<'ctx>,
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
    ) -> FunctionValue<'ctx> {
        let fname = format!("{}_get_maybe", &maptype);
        let fv = if let Some(fv) = self.module.get_function(&fname) {
            fv
        } else {
            const MAP_PARAM: u32 = 0;
            const KEY_PARAM: u32 = 1;
            let returntype = Type::Map(Box::new(Type::Unit), Box::new(v.clone()));
            let param_types = if Type::Unit.ne(&k) {
                vec![llvmmaptype.into(), llvmkeytype.into()]
            } else {
                vec![llvmmaptype.into()]
            };
            let fv = self.module.add_function(
                &fname,
                self.llvmfunctiontype(&returntype, scopeinfo.clone(), &param_types, false),
                None,
            );
            let call_block = self.builder.get_insert_block().unwrap();
            self.builder
                .position_at_end(self.context.append_basic_block(fv, "entry"));

            //self.debug("GET_MAYBE \tKEY: %lu\n", [fv.get_nth_param(1).unwrap().into()]);
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
                        &("map.size.ptr"),
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
                                                map_values(&k),
                                                &("map.values.ptr"),
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
                //self.emit_printf_call(&" HASH: %lu\n", &[hash.into()]);

                let capacity = self.builder.build_load(
                    self.builder
                        .build_struct_gep(
                            fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                            MAP_CAPACITY,
                            &("map.capacity.ptr"),
                        )
                        .unwrap(),
                    "capacity",
                );

                let states = self.builder.build_load(
                    self.builder
                        .build_struct_gep(
                            fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                            MAP_STATES,
                            &("map.states.ptr"),
                        )
                        .unwrap(),
                    "states",
                );

                let keys = self.builder.build_load(
                    self.builder
                        .build_struct_gep(
                            fv.get_nth_param(MAP_PARAM).unwrap().into_pointer_value(),
                            MAP_KEYS,
                            &("map.keys.ptr"),
                        )
                        .unwrap(),
                    "keys",
                );

                let idx_ptr = self.builder.build_alloca(self.context.i64_type(), "idx");
                self.builder.build_store(
                    idx_ptr,
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

                let idx_val = self.builder.build_load(idx_ptr, "idx_val").into_int_value();
                //self.debug("\tIDX: %lu\n", [idx_val.into()]);
                let state_ptr = unsafe {
                    self.builder
                        .build_gep(states.into_pointer_value(), &[idx_val], "")
                };

                let key_ptr = unsafe {
                    self.builder
                        .build_gep(keys.into_pointer_value(), &[idx_val], "")
                };

                self.builder.build_conditional_branch(
                    self.builder.build_int_compare(
                        IntPredicate::NE,
                        self.builder
                            .build_load(state_ptr, "state_idx")
                            .into_int_value(),
                        self.statetype().const_int(STATE_FREE, false),
                        "is_not_state_free",
                    ),
                    whilebody,
                    afterwhile,
                );
                self.builder.position_at_end(whilebody);

                //if
                let ifbody = self.context.append_basic_block(fv, "ifbody");
                let afterif = self.context.append_basic_block(fv, "afterif");
                let keyidx = self.builder.build_load(key_ptr, "key_idx");
                self.builder.build_conditional_branch(
                    self.builder.build_and(
                        self.builder.build_int_compare(
                            IntPredicate::EQ,
                            self.builder
                                .build_load(state_ptr, "state_idx")
                                .into_int_value(),
                            self.statetype().const_int(STATE_TAKEN, false),
                            "is_state_taken",
                        ),
                        self.builder
                            .build_call(
                                self.equal(&k, scopeinfo.clone()),
                                &[keyidx.into(), fv.get_nth_param(KEY_PARAM).unwrap().into()],
                                "is_key_equal",
                            )
                            .try_as_basic_value()
                            .unwrap_left()
                            .into_int_value(),
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
                                                map_values(&k),
                                                &("map.values.ptr"),
                                            )
                                            .unwrap(),
                                        "values",
                                    )
                                    .into_pointer_value(),
                                &[self.builder.build_load(idx_ptr, "").into_int_value()],
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
                    idx_ptr,
                    self.builder.build_int_unsigned_rem(
                        self.builder.build_int_add(
                            self.builder.build_load(idx_ptr, "").into_int_value(),
                            self.context.i64_type().const_int(1, false),
                            "",
                        ),
                        capacity.into_int_value(),
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
        fv
    }

    fn emit_global_map(
        &mut self,
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
        fm: &crate::parser::PerfectMap<'b>,
    ) -> PointerValue<'ctx> {
        if let Type::PerfectMap(k, v) = &fm.maptype {
            let llvmkeytype = self.llvmtype(&k, scopeinfo.clone());
            let llvmvaluetype = self.llvmtype(&v, scopeinfo.clone());

            let ty = self.llvmstruct(&fm.maptype, scopeinfo.clone());
            let len = fm.entries.len();

            let mut order: Vec<(usize, u64)> = perfect::get_order(&fm.values, &fm.args)
                .into_iter()
                .enumerate()
                .collect();
            order.sort_by_key(|k| k.1);
            let entries: Vec<&(Value, Value)> = order.iter().map(|i| &fm.entries[i.0]).collect();

            let keysptr = {
                let gv = self.module.add_global(
                    llvmkeytype.array_type(len as u32),
                    Some(AddressSpace::default()),
                    "g.keys",
                );
                gv.set_linkage(Linkage::Internal);
                let vals: &Vec<BasicValueEnum<'_>> = &entries
                    .iter()
                    .map(|(c, _)| self.emit_const(c, scopeinfo.clone()))
                    .collect::<Vec<_>>();
                let vals = self.llvmconstarray(k, scopeinfo.clone(), vals);
                gv.set_initializer(&vals.as_basic_value_enum());
                self.builder.build_bitcast(
                    gv.as_pointer_value(),
                    llvmkeytype.ptr_type(AddressSpace::default()),
                    "",
                )
            };
            let strptr = {
                let gv = self.module.add_global(
                    llvmvaluetype.array_type(len as u32),
                    Some(AddressSpace::default()),
                    "g.values",
                );
                gv.set_linkage(Linkage::Internal);
                let vals: &Vec<BasicValueEnum<'_>> = &entries
                    .iter()
                    .map(|(_, c)| self.emit_const(c, scopeinfo.clone()))
                    .collect::<Vec<_>>();
                let vals = self.llvmconstarray(v, scopeinfo.clone(), vals);
                gv.set_initializer(&vals.as_basic_value_enum());
                self.builder.build_bitcast(
                    gv.as_pointer_value(),
                    llvmvaluetype.ptr_type(AddressSpace::default()),
                    "",
                )
            };
            let size = self.context.i64_type().const_int(len as u64, false);
            let argslen = self
                .context
                .i32_type()
                .const_int(fm.args.len() as u64, false)
                .into();
            let args = {
                let gv = self.module.add_global(
                    self.context.i32_type().array_type(fm.args.len() as u32),
                    Some(AddressSpace::default()),
                    "g.args",
                );
                gv.set_linkage(Linkage::Internal);
                let vals: &Vec<BasicValueEnum<'_>> = &fm
                    .args
                    .iter()
                    .map(|c| self.context.i32_type().const_int(*c as u64, false).into())
                    .collect::<Vec<_>>();
                let vals = self.llvmconstarray(&Type::Int, scopeinfo.clone(), vals);

                gv.set_initializer(&vals.as_basic_value_enum());
                self.builder.build_bitcast(
                    gv.as_pointer_value(),
                    self.context.i32_type().ptr_type(AddressSpace::default()),
                    "",
                )
            };

            let gv = self
                .module
                .add_global(ty, Some(AddressSpace::default()), "g");
            gv.set_linkage(Linkage::Internal);

            gv.set_initializer(
                &self
                    .context
                    .const_struct(&[size.into(), keysptr, strptr, argslen, args], false),
            );

            let gv2 = self.module.add_global(
                self.llvmtype(&fm.maptype, scopeinfo.clone()),
                Some(AddressSpace::default()),
                fm.identifier,
            );
            gv2.set_linkage(Linkage::Internal);
            gv2.set_initializer(&gv.as_pointer_value());
            gv2.as_pointer_value()
        } else {
            panic!("should be map")
        }
    }

    fn hash_perfect(
        &mut self,
        t: &Type<'b>,
        scopeinfo: Rc<RefCell<ScopeInfo<'b>>>,
    ) -> FunctionValue<'ctx> {
        const ARGS_LEN_PARAM: u32 = 0;
        const ARGS_PARAM: u32 = 1;
        const KEY_PARAM: u32 = 2;
        let s = format!("hash_perfect_{t}");
        let fv = if let Some(fv) = self.module.get_function(&s) {
            fv
        } else {
            let args = if Type::Unit.ne(t) {
                vec![
                    self.context.i32_type().into(),
                    self.context
                        .i32_type()
                        .ptr_type(AddressSpace::default())
                        .into(),
                    self.llvmtype(t, scopeinfo.clone()).into(),
                ]
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
            let hashargs = if Type::Unit.ne(&t) {
                vec![fv.get_nth_param(KEY_PARAM).unwrap().into()]
            } else {
                vec![]
            };
            let hash = self
                .builder
                .build_call(self.hash(&t, scopeinfo.clone()), &hashargs, "")
                .try_as_basic_value()
                .unwrap_left();

            let result = self.builder.build_alloca(self.context.i64_type(), "result");
            self.builder
                .build_store(result, self.context.i64_type().const_zero());
            let idx = self.builder.build_alloca(self.context.i32_type(), "idx");
            self.builder
                .build_store(idx, self.context.i32_type().const_zero());

            let whilecond = self.context.append_basic_block(fv, "whilecond");
            let whilebody = self.context.append_basic_block(fv, "whilebody");
            let afterwhile = self.context.append_basic_block(fv, "afterwhile");
            self.builder.build_unconditional_branch(whilecond);
            self.builder.position_at_end(whilecond);
            let idxval = self.builder.build_load(idx, "idxval").into_int_value();
            self.builder.build_conditional_branch(
                self.builder.build_int_compare(
                    IntPredicate::ULT,
                    idxval,
                    fv.get_nth_param(ARGS_LEN_PARAM).unwrap().into_int_value(),
                    "",
                ),
                whilebody,
                afterwhile,
            );
            self.builder.position_at_end(whilebody);
            self.builder.build_store(
                result,
                self.builder.build_xor(
                    self.builder.build_load(result, "").into_int_value(),
                    self.builder
                        .build_call(
                            self.module.get_function(ROT).unwrap(),
                            &[
                                hash.into(),
                                hash.into(),
                                self.builder
                                    .build_int_z_extend(
                                        self.builder
                                            .build_load(
                                                unsafe {
                                                    self.builder.build_gep(
                                                        fv.get_nth_param(ARGS_PARAM)
                                                            .unwrap()
                                                            .into_pointer_value(),
                                                        &[idxval],
                                                        "",
                                                    )
                                                },
                                                "",
                                            )
                                            .into_int_value(),
                                        self.context.i64_type(),
                                        "",
                                    )
                                    .into(),
                            ],
                            "rot",
                        )
                        .try_as_basic_value()
                        .unwrap_left()
                        .into_int_value(),
                    "xor",
                ),
            );
            self.builder.build_store(
                idx,
                self.builder
                    .build_int_add(idxval, self.context.i32_type().const_int(1, false), ""),
            );
            self.builder.build_unconditional_branch(whilecond);
            self.builder.position_at_end(afterwhile);
            self.builder
                .build_return(Some(&self.builder.build_load(result, "")));
            if let Some(b) = call_block {
                self.builder.position_at_end(b);
            }
            fv
        };
        fv
    }
}
