use std::fs::File;
use std::io::prelude::*;

extern crate pest;
#[macro_use]
extern crate pest_derive;

mod parser;
mod typecheck;

fn main() {
    let path = "./main.lang";
    let mut file = File::open(path).expect("file to exist");
    let mut contents = String::new();
    file.read_to_string(&mut contents)
        .expect("no problems reading the file");
    let ast = parser::parse_program(&contents).expect("no parsing problems");
    File::create(path.to_owned() + ".ast")
        .expect("no problems opening/creating file")
        .write_all(format!("{:#?}", ast).as_bytes())
        .expect("no problems writing to the file");
}
