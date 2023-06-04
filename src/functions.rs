use crate::parser::Type;
use once_cell::sync::Lazy;

pub const PRINT_INT: &str = "printInt";
pub const PRINT_BOOL: &str = "printBool";
pub const PRINT_LN: &str = "printLn";
pub const PRINT_CHAR: &str = "printChar";

pub const SIZE: &str = "size";
pub const CAPACITY: &str = "capacity";
pub const TOMBS: &str = "tombs";
pub const CLEAR: &str = "clear";
pub const GET: &str = "get";
pub const GET_MAYBE: &str = "getMaybe";
pub const INSERT: &str = "insert";
pub const REMOVE: &str = "remove";

pub static PREDEFINED_FUNCTIONS: Lazy<Vec<(&'static str, Vec<Type<'static>>, Type<'static>)>> =
    Lazy::new(|| {
        vec![
            (PRINT_INT, vec![Type::Int], Type::Unit),
            (PRINT_BOOL, vec![Type::Bool], Type::Unit),
            (PRINT_LN, vec![], Type::Unit),
            (PRINT_CHAR, vec![Type::Char], Type::Unit),
        ]
    });

pub fn valid_map_function<'a>(
    k: Type<'a>,
    v: Type<'a>,
    args: &Vec<Type>,
    id: &str,
) -> Result<Type<'a>, String> {
    let correctargs = get_map_args(&k, &v, id)?.eq(args);
    match id {
        SIZE | CAPACITY | TOMBS | CLEAR => {
            if correctargs {
                Ok(if id == CLEAR { Type::Unit } else { Type::Int })
            } else {
                Err(format!("{id} does not take arguments"))
            }
        }
        GET => {
            if correctargs {
                Ok(v)
            } else {
                Err(format!("{GET} takes {k} as argument "))
            }
        }
        INSERT => {
            if correctargs {
                Ok(Type::Unit)
            } else {
                Err(format!("{INSERT} takes [{k}, {v}] as arguments "))
            }
        }
        REMOVE => {
            if correctargs {
                Ok(Type::Unit)
            } else {
                Err(format!("{REMOVE} takes {k} as argument "))
            }
        }
        GET_MAYBE => {
            if correctargs {
                Ok(Type::Map(Box::new(Type::Unit), Box::new(v)))
            } else {
                Err(format!("{GET} takes {k} as argument "))
            }
        }
        _ => Err(format!("unknown map function: {id}")),
    }
}

pub fn get_map_args<'a, 'b>(
    k: &'b Type<'a>,
    v: &'b Type<'a>,
    id: &'b str,
) -> Result<Vec<Type<'a>>, String> {
    let k = k.clone();
    let v = v.clone();
    match id {
        SIZE | CAPACITY | TOMBS | CLEAR => Ok(vec![]),
        GET | GET_MAYBE | REMOVE => {
            if k == Type::Unit {
                Ok(vec![])
            } else {
                Ok(vec![k])
            }
        }
        INSERT => {
            if k == Type::Unit && v == Type::Unit {
                Ok(vec![])
            } else if k == Type::Unit {
                Ok(vec![v])
            } else if v == Type::Unit {
                Ok(vec![k])
            } else {
                Ok(vec![k, v])
            }
        }
        _ => Err(format!("unknown map function: {id}")),
    }
}
