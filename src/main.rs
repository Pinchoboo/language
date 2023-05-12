extern crate pest;
#[macro_use]
extern crate pest_derive;

mod parser;

fn main() {
    match parser::parse_program("fn main(){
		if true{}else if false{}else{}
		int ident = 1+2 
		while true{}
		selfdefined(-1,true)
	}") {
        Ok(p) => {dbg!(p);},
        Err(e) => {dbg!(e);},
    };
}
