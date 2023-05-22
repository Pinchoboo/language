use std::fs::File;
use std::io::prelude::*;

extern crate pest;
#[macro_use]
extern crate pest_derive;

mod parser;
mod typecheck;
mod compile;

fn main() {
    let fp = parser::FileParser::new("./main.lang").unwrap();
    let mut ast = fp.parse().expect("expect no parsing problems");
	typecheck::typecheck(&mut ast);
    File::create("./out/main.lang.ast")
        .expect("no problems opening/creating file")
        .write_all(format!("{:#?}", ast).as_bytes())
        .expect("no problems writing to the file");
    let _ = compile::compile(ast);
}
