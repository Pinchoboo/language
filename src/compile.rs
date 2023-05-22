use std::{
    any::Any, cell::RefCell, collections::HashMap, iter::once_with, path::Path, process::Command,
    rc::Rc,
};

use inkwell::{
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    targets::{
        CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple,
    },
    types::{BasicType, IntType},
    values::{
        BasicMetadataValueEnum, BasicValue, BasicValueEnum, CallSiteValue, FunctionValue, IntValue,
        PointerValue,
    },
    AddressSpace, IntPredicate, OptimizationLevel,
};

use crate::{
    parser::{BinOp, Block, Expression, Function, Program, Statement, Type, Value},
    typecheck::{self, find_function, ScopeInfo},
};

pub struct Compiler<'ctx, 'a> {
    pub context: &'ctx Context,
    pub builder: &'a Builder<'ctx>,
    pub module: &'a Module<'ctx>,
    pub vars: HashMap<i32, PointerValue<'ctx>>,
    strings: Rc<RefCell<HashMap<String, PointerValue<'ctx>>>>,
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
    };
    c.compile(program);
}

impl<'ctx, 'a, 'b: 'ctx> Compiler<'ctx, 'a> {
    pub fn compile(&mut self, program: Program<'b>) {
        //add external functions
        self.module.add_function(
            "printf",
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
        // compile program
        program
            .functions
            .iter()
            .map(|f| {
                let args = f
                    .arguments
                    .iter()
                    .map(|(t, _)| match t {
                        Type::Int => self.context.i64_type().into(),
                        Type::Float => self.context.f64_type().into(),
                        Type::Bool => self.context.bool_type().into(),
                        Type::Char => self.context.i64_type().into(),
                        Type::Unit => todo!(),
                    })
                    .collect::<Vec<_>>();

                let function_value = self.module.add_function(
                    f.identifier,
                    match f.return_type {
                        Type::Int => self.context.i64_type().fn_type(&args, false),
                        Type::Float => self.context.f64_type().fn_type(&args, false),
                        Type::Bool => self.context.bool_type().fn_type(&args, false),
                        Type::Char => self.context.i64_type().fn_type(&args, false),
                        Type::Unit => self.context.void_type().fn_type(&args, false),
                    },
                    None,
                );
                (f, function_value)
            })
            .collect::<Vec<_>>()
            .iter()
            .for_each(|(f, function_value)| {
                self.builder
                    .position_at_end(self.context.append_basic_block(*function_value, "entry"));
                for (t, id) in &f.arguments {
                    let (_, _, i, argnum) =
                        typecheck::find_variable(id, f.body.scopeinfo.clone()).unwrap();
                    let varname = format!("{id}_{i}");
                    self.builder.build_store(
                        {
                            let p = self.builder.build_alloca(
                                match t {
                                    Type::Int => self.context.i64_type().as_basic_type_enum(),
                                    Type::Float => self.context.f64_type().as_basic_type_enum(),
                                    Type::Bool => self.context.i64_type().as_basic_type_enum(),
                                    Type::Char => self.context.i64_type().as_basic_type_enum(),
                                    Type::Unit => panic!("unreachable"),
                                },
                                &varname,
                            );
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
        let f = self.module.get_function("printf").unwrap();
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
                        let p = self.builder.build_alloca(self.context.i64_type(), &varname);
                        self.vars.insert(*i, p);
                        p
                    } else {
                        *self.vars.get(i).unwrap()
                    }
                };
                let value = self.emit_expression(expr, scopeinfo, fv);

                self.builder.build_store(pointer, value);
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
                let args: Vec<_> = args
                    .iter()
                    .map(|expr| {
                        BasicMetadataValueEnum::from(self.emit_expression(
                            expr,
                            scopeinfo.clone(),
                            fv,
                        ))
                    })
                    .collect();
                if *i == -1 {
                    match *id {
                        "printInt" => {
                            self.emit_printf_call(&"%d", &args);
                        }
                        "printBool" => {
                            self.emit_printf_call(&{ "%d" }, &args);
                        }
                        "println" => {
                            self.emit_printf_call(&{ "\n" }, &args);
                        }
                        "printChar" => {
                            self.emit_printf_call(&{ "%c" }, &args);
                        }
                        _ => {
                            panic!("unknown function: {id}")
                        }
                    }
                } else {
                    self.builder
                        .build_call(self.module.get_function(id).unwrap(), &args, "");
                }
            }
            crate::parser::StatementType::Return(e) => {
                self.builder
                    .build_return(Some(&self.emit_expression(e, scopeinfo, fv)));
            }
            _ => {
                dbg!(&statement.statement);
                panic!("unreachable")
            }
        };
    }

    fn emit_expression(
        &self,
        expr: &Expression,
        scopeinfo: Rc<RefCell<ScopeInfo>>,
        fv: FunctionValue<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        match expr {
            Expression::Binary(l, b, r, Some(t)) => {
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

            Expression::Unary(_, _, Some(t)) => todo!(),
            Expression::Value(v, Some(t)) => self.emit_value(v, scopeinfo, fv),
            _ => {
                panic!("expected type info")
            }
        }
    }

    fn emit_value(
        &self,
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
            Value::Call(id, args, Some(i)) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|expr| {
                        BasicMetadataValueEnum::from(self.emit_expression(
                            expr,
                            scopeinfo.clone(),
                            fv,
                        ))
                    })
                    .collect();
                if *i == -1 {
                    match *id {
                        "printInt" => self.emit_printf_call(&"%d", &args),
                        "printBool" => self.emit_printf_call(&{ "%d" }, &args),
                        "println" => self.emit_printf_call(&{ "\n" }, &args),
                        "printChar" => self.emit_printf_call(&{ "%c" }, &args),
                        _ => {
                            panic!("unknown function: {id}")
                        }
                    }
                } else {
                    self.builder
                        .build_call(self.module.get_function(id).unwrap(), &args, "")
                }
                .try_as_basic_value()
                .unwrap_left()
            }
            Value::Identifier(id, Some(_)) => {
                let foundvar = typecheck::find_variable(id, scopeinfo).unwrap();
                self.builder.build_load(*self.vars.get(&foundvar.2).unwrap(), "")
            }
            _ => panic!("unreachable"),
        }
    }
}
