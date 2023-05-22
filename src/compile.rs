use std::{
    cell::RefCell, collections::HashMap, iter::once_with, path::Path, process::Command, rc::Rc,
};

use inkwell::{
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    targets::{
        CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple,
    },
    types::IntType,
    values::{BasicMetadataValueEnum, BasicValueEnum, FunctionValue, IntValue, PointerValue},
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
        //main type signature
        let i64_type = self.context.i64_type();
        let function_type =
            i64_type.fn_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);
        let main_value = self.module.add_function("main", function_type, None);
        let basic_block = self.context.append_basic_block(main_value, "entry");
        self.builder.position_at_end(basic_block);

        //add program
        let main = program
            .functions
            .iter()
            .find(|f| f.identifier.eq("main"))
            .expect("main function to exist");
        self.emit_block(&main.body, &main_value);

        self.builder
            .build_return(Some(&self.context.i64_type().const_int(0, false)));

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

    fn emit_printf_call(&self, string: &&str, args: &[BasicMetadataValueEnum<'a>]) -> IntType {
        let mut printfargs = vec![self.emit_global_string(string, ".str").into()];
        printfargs.extend_from_slice(args);
        let f = self.module.get_function("printf").unwrap();
        self.builder.build_call(f, &printfargs, "");
        self.context.i32_type()
    }

    fn emit_global_string(&self, string: &&str, name: &str) -> PointerValue {
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
    fn emit_block(&mut self, body: &Block, fv: &FunctionValue) {
        for s in &body.statements {
            self.emit_statement(s, fv, body.scopeinfo.clone());
        }
    }

    fn emit_statement(
        &mut self,
        statement: &Statement,
        fv: &FunctionValue,
        scopeinfo: Rc<RefCell<ScopeInfo>>,
    ) {
        match &statement.statement {
            crate::parser::StatementType::Assignment(t, id, expr, Some(i)) => {
                let varname = format!("{id}_{i}");
                let pointer = {
                    if t.is_some() {
                        let p = self.builder.build_alloca(self.context.i32_type(), &varname);
                        self.vars.insert(*i, p);
                        p
                    } else {
                        *self.vars.get(i).unwrap()
                    }
                };
                let value = self.emit_expression(expr, scopeinfo);

                self.builder.build_store(pointer, value);
            }
            crate::parser::StatementType::If(ifpart, ifelsepart, elseblock) => {
                let condblocks: Vec<_> = once_with(|| ifpart)
                    .chain(ifelsepart.iter())
                    .zip(0..)
                    .map(|((_, _), i)| {
                        (
                            self.context.append_basic_block(*fv, &format!("if{i}")),
                            self.context.append_basic_block(*fv, &format!("if{i}_end")),
                        )
                    })
                    .collect();
                let afterelselable = self.context.append_basic_block(*fv, "else_end");
                for ((cond, block), (thenlable, afterthenlable)) in once_with(|| ifpart)
                    .chain(ifelsepart.iter())
                    .zip(condblocks.iter())
                {
                    let cond = self.emit_expression(cond, scopeinfo.clone());
                    self.builder.build_conditional_branch(
                        cond.into_int_value(),
                        *thenlable,
                        *afterthenlable,
                    );
                    self.builder.position_at_end(*thenlable);
                    self.emit_block(block, fv);
                    self.builder.build_unconditional_branch(afterelselable);
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
                let condlable = self.context.append_basic_block(*fv, "whilecond");
                let whilelable = self.context.append_basic_block(*fv, "while");
                let afterwhilelable = self.context.append_basic_block(*fv, "afterwhile");
                self.builder.build_unconditional_branch(condlable);
                self.builder.position_at_end(condlable);
                self.builder.build_conditional_branch(
                    self.emit_expression(cond, scopeinfo).into_int_value(),
                    whilelable,
                    afterwhilelable,
                );
                self.builder.position_at_end(whilelable);
                self.emit_block(block, fv);
                self.builder.build_unconditional_branch(condlable);
                self.builder.position_at_end(afterwhilelable)
            }
            crate::parser::StatementType::Call(id, args, Some(i)) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|expr| {
                        BasicMetadataValueEnum::from(self.emit_expression(expr, scopeinfo.clone()))
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
                    let funcname = format!("{id}_{i}");
                    self.builder.build_call(
                        self.module.get_function(&funcname).unwrap(),
                        &args,
                        "",
                    );
                }
            }
            crate::parser::StatementType::Return(_) => todo!(),
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
    ) -> BasicValueEnum {
        match expr {
            Expression::Binary(l, b, r, Some(t)) => {
                let lv = self.emit_expression(l, scopeinfo.clone());
                let rv = self.emit_expression(r, scopeinfo.clone());
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
            Expression::Value(v, Some(t)) => self.emit_value(v, scopeinfo),
            _ => {
                panic!("expected type info")
            }
        }
    }

    fn emit_value(&self, val: &Value, scopeinfo: Rc<RefCell<ScopeInfo>>) -> BasicValueEnum {
        match val {
            Value::Number(n) => BasicValueEnum::IntValue(
                self.context
                    .i32_type()
                    .const_int((*n).try_into().unwrap(), false),
            ),
            Value::Char(c) => BasicValueEnum::IntValue(
                self.context
                    .i32_type()
                    .const_int((*c as u32).try_into().unwrap(), false),
            ),
            Value::Bool(b) => BasicValueEnum::IntValue(
                self.context
                    .bool_type()
                    .const_int(if *b { 1 } else { 0 }, false),
            ),
            Value::Call(_, _, _) => panic!(),
            Value::Identifier(id, Some(i)) => {
                match typecheck::find_variable(id, scopeinfo).unwrap() {
                    (_, Type::Int, i) => self.builder.build_load(*self.vars.get(&i).unwrap(), ""),
                    (_, Type::Bool, i) => self.builder.build_load(*self.vars.get(&i).unwrap(), ""),
                    (_, Type::Char, i) => self.builder.build_load(*self.vars.get(&i).unwrap(), ""),
                    (_, Type::Float, i) => self.builder.build_load(*self.vars.get(&i).unwrap(), ""),
                    (_, Type::Unit, _) => {
                        todo!()
                    }
                }
            }
            _ => panic!("unreachable"),
        }
    }
}
