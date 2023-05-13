use std::fs::File;
use std::io::prelude::*;

extern crate pest;
#[macro_use]
extern crate pest_derive;

mod parser;
mod typecheck;

fn main() {
    let path = "./main.lang";
    let fp = parser::FileParser::new(path).unwrap();
    let ast = fp.parse().expect("no parsing problems");
    File::create(path.to_owned() + ".ast")
        .expect("no problems opening/creating file")
        .write_all(format!("{:#?}", ast).as_bytes())
        .expect("no problems writing to the file");
}
