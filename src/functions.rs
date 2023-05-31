use crate::parser::Type;

pub const PRINT_INT: &str = "printInt";
pub const PRINT_BOOL: &str = "printBool";
pub const PRINTLN: &str = "println";
pub const PRINT_CHAR: &str = "printChar";

pub const SIZE: &str = "size";
pub const CLEAR: &str = "clear";
pub const GET: &str = "get";
pub const INSERT: &str = "insert";
pub const REMOVE: &str = "remove";

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

pub fn valid_map_function(k: Type, v: Type, args: &Vec<Type>, id: &str) -> Result<Type, String> {
    match id {
        SIZE | CLEAR => {
            if args.is_empty() {
                Ok(if id == SIZE { Type::Int } else { Type::Unit })
            } else {
                Err(format!("{id} does not take arguments"))
            }
        }
        GET => {
            if args.len() == 1 && args[0] == k {
                Ok(v)
            } else {
                Err(format!("{GET} takes {k} as argument "))
            }
        }
        INSERT => {
            if args.len() == 2 && args[0] == k && args[1] == v {
                Ok(Type::Unit)
            } else {
                Err(format!("{INSERT} takes [{k}, {v}] as arguments "))
            }
        }
		REMOVE => {
            if args.len() == 1 && args[0] == k {
                Ok(Type::Unit)
            } else {
                Err(format!("{REMOVE} takes {k} as argument "))
            }
        }
        _ => Err(format!("unknown map function: {id}")),
    }
}
