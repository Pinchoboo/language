use std::{cell::RefCell, collections::HashMap, path::Path, process::Command, rc::Rc};

use inkwell::{
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    targets::{
        CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple,
    },
    types::IntType,
    values::{BasicMetadataValueEnum, IntValue, PointerValue, BasicValueEnum},
    AddressSpace, OptimizationLevel,
};

use crate::{
    parser::{Block, Expression, Function, Program, Statement, Type, Value},
    typecheck::{self, ScopeInfo},
};

pub struct Compiler<'ctx, 'a> {
    pub context: &'ctx Context,
    pub builder: &'a Builder<'ctx>,
    pub module: &'a Module<'ctx>,
    pub vars: HashMap<i32, PointerValue<'ctx>>,
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
    };
    c.compile(program);
}

impl<'ctx, 'a, 'b:'ctx> Compiler<'ctx, 'a> {
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
        let function = self.module.add_function("main", function_type, None);
        let basic_block = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(basic_block);

        //add program
        let main = program
            .functions
            .iter()
            .find(|f| f.identifier.eq("main"))
            .expect("main function to exist");
        self.emit_block(&main.body);

        self.builder
            .build_return(Some(&self.context.i64_type().const_int(0, false)));

        //check module
        if let Err(e) = self.module.verify() {
            println!("{}", e.to_string());
            return;
        }

        //save llvm ir
        let _result = self.module.print_to_file("./out/main.ll");

        //save executable
        Target::initialize_x86(&InitializationConfig::default());

        let opt = OptimizationLevel::None;
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

    fn emit_printf_call(&self, string: &&str, args: &[BasicMetadataValueEnum<'ctx>]) -> IntType {
        let mut printfargs = vec![self.emit_global_string(string, ".str").into()];
        printfargs.extend_from_slice(args);
        let f = self.module.get_function("printf").unwrap();
        self.builder.build_call(f, &printfargs, "");
        self.context.i32_type()
    }

    fn emit_global_string(&self, string: &&str, name: &str) -> PointerValue {
        let string = string.to_owned().to_owned() + "\0";
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
    fn emit_block(&mut self, body: &Block) {
        for s in &body.statements {
            self.emit_statement(s, body.scopeinfo.clone());
        }
    }

    fn emit_statement(&mut self, statement: &Statement, scopeinfo: Rc<RefCell<ScopeInfo>>) {
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
            crate::parser::StatementType::If(_, _, _) => todo!(),
            crate::parser::StatementType::While(_) => todo!(),
            crate::parser::StatementType::Call(_, _, _) => todo!(),
            crate::parser::StatementType::Return(_) => todo!(),
            _ => {
                dbg!(&statement.statement);
                panic!("unreachable")
            }
        };
    }

    fn emit_expression(&self, expr: &Expression, scopeinfo: Rc<RefCell<ScopeInfo>>) -> BasicValueEnum {
        match expr {
            Expression::Binary(l, b, r) => {
            let l = self.emit_expression(l, scopeinfo.clone());
            let r = self.emit_expression(r, scopeinfo.clone());
            
            //int addition todo others
            BasicValueEnum::IntValue(self.builder.build_int_add(
                l.into_int_value(),
                r.into_int_value(),
                "",
            ))},
            
            Expression::Unary(_, _) => todo!(),
            Expression::Value(v) => self.emit_value(v, scopeinfo),
        }
    }

    fn emit_value(&self, val: &Value, scopeinfo: Rc<RefCell<ScopeInfo>>) -> BasicValueEnum {
        match val {
            Value::Number(n) => BasicValueEnum::IntValue(self
                .context
                .i32_type()
                .const_int((*n).try_into().unwrap(), false)),
            Value::Bool(b) => BasicValueEnum::IntValue(self
                .context
                .bool_type()
                .const_int(if *b { 1 } else { 0 }, false)),
            Value::Call(_, _, _) => panic!(),
            Value::Identifier(id, Some(i)) => {
                match typecheck::find_variable(id, scopeinfo).unwrap() {
                    (_, Type::Int, i) => {self.builder.build_load(*self.vars.get(&i).unwrap(), "")}
                    (_, Type::Bool, _) => {todo!()}
                    (_, Type::Char, _) => {todo!()}
                    (_, Type::Float, _) => {todo!()}
                    (_, Type::Unit, _) => {todo!()}
                }
            }
            _ => panic!("unreachable"),
        }
    }
}
