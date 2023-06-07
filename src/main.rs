use std::env;
use std::fs::File;
use std::io::prelude::*;

extern crate pest;
#[macro_use]
extern crate pest_derive;

mod parser;
mod functions;
mod typecheck;
mod compile;


fn main() {
	env::set_var("RUST_BACKTRACE", "1");
    let fp = parser::FileParser::new("./main.mpl").unwrap();
    let mut ast = fp.parse().expect("expect no parsing problems");
	File::create("./out/main.parsed.ast")
        .expect("no problems opening/creating file")
        .write_all(format!("{:#?}", ast).as_bytes())
        .expect("no problems writing to the file");
	typecheck::typecheck(&mut ast);
    File::create("./out/main.checked.ast")
        .expect("no problems opening/creating file")
        .write_all(format!("{:#?}", ast).as_bytes())
        .expect("no problems writing to the file");
    compile::compile(ast);
}
