extern crate pest;
#[macro_use]
extern crate pest_derive;

mod parser;
mod typecheck;

fn main() {
    match parser::parse_program("fn int main(){
		int a = 1 * 2 + 2 * 3
	}") {
        Ok(p) => {dbg!(p);},
        Err(e) => {dbg!(e);},
    };
}
