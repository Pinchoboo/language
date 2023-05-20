use std::{path::Path, process::Command};

use inkwell::{
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    targets::{
        CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple,
    },
    types::IntType,
    values::{PointerValue, BasicMetadataValueEnum},
    AddressSpace, OptimizationLevel,
};
use lazy_static::lazy_static;

use crate::parser::{Function, Program, Value};

pub struct Compiler<'a, 'ctx> {
    pub context: &'ctx Context,
    pub builder: &'a Builder<'ctx>,
    pub module: &'a Module<'ctx>,
}

pub fn compile(program: Program) {
    let context = Context::create();
    let module = context.create_module("module");
    let builder = context.create_builder();

    let c = Compiler {
        context: &context,
        module: &module,
        builder: &builder,
    };
    c.compile(program);
}

impl<'a, 'ctx> Compiler<'a, 'ctx> {
    pub fn compile(&self, program: Program) {
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

        self.emit_printf_call(&"hello world\n", &[]);
        self.emit_printf_call(&"hello world2\n", &[]);
        
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

        let opt = OptimizationLevel::Default;
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
}
