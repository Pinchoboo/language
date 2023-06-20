use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::{process::exit};

use inkwell::context::{Context};
use parser::Program;

extern crate pest;
#[macro_use]
extern crate pest_derive;

mod compile;
mod functions;
mod parser;
mod perfect;
mod typecheck;
mod benchmark;

fn main() {
	env::set_var("RUST_BACKTRACE", "1");
    let args: Vec<String> = env::args().collect();
    let path: &str = args.get(1).map(|s| (s.as_str())).unwrap_or("./main.mpl");
    let fp = parser::FileParser::new(path).unwrap();
    let mut ast = fp.parse().expect("expect no parsing problems");
	check(&mut ast);
    let context = Context::create();
    let builder = &mut context.create_builder();
    let module = &mut context.create_module("module");
    let compiler = compile::compile(&context, builder, module, ast);
	exit(compiler.execute());
}

fn check(ast : &mut Program){
	File::create("./out/parsed.ast")
        .expect("no problems opening/creating file")
        .write_all(format!("{:#?}", ast).as_bytes())
        .expect("no problems writing to the file");
    typecheck::typecheck(ast);
    for m in &mut ast.findmaps {
        perfect::find_hash_function(m)
    }
    File::create("./out/checked.ast")
        .expect("no problems opening/creating file")
        .write_all(format!("{:#?}", ast).as_bytes())
        .expect("no problems writing to the file");
}