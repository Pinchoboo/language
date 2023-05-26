use crate::parser::Type;

pub const PRINT_INT: &str = "printInt";
pub const PRINT_BOOL: &str = "printBool";
pub const PRINTLN: &str = "println";
pub const PRINT_CHAR: &str = "printChar";

lazy_static::lazy_static! {
	pub static ref PREDEFINED_FUNCTIONS: Vec<(&'static str, Vec<Type>, Type)> = {
        vec![
        	(PRINT_INT,vec![Type::Int],Type::Unit),
			(PRINT_BOOL,vec![Type::Bool],Type::Unit),
			(PRINTLN,vec![],Type::Unit),
			(PRINT_CHAR,vec![Type::Char],Type::Unit),
		]
    };
}