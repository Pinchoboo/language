

use crate::{
    parser::Type,
};
use once_cell::sync::Lazy;

pub const PRINT_INT: &str = "printInt";
pub const PRINT_BOOL: &str = "printBool";
pub const PRINT_LN: &str = "printLn";
pub const PRINT_CHAR: &str = "printChar";
pub const PRINT_FLOAT: &str = "printFloat";

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
			(PRINT_FLOAT, vec![Type::Float], Type::Unit),
        ]
    });

pub fn valid_map_function<'a>(
    k: Type<'a>,
    v: Type<'a>,
    args: &Vec<Type>,
    id: &str,
	is_const: bool
) -> Result<Type<'a>, String> {
	if is_const {
		match id {
			TOMBS | CLEAR | INSERT | REMOVE => {
				return Err(format!("invalid function {id} for const map"))
			}
			_ =>{}
		}
	}
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
                Ok(Type::Bool)
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

pub fn valid_map_struct_function<'a>(
    id: &str,
    args: Vec<Result<Type<'a>, Type<'a>>>,
) -> Result<Type<'a>, String> {
    match id {
        SIZE | CAPACITY | TOMBS | CLEAR => {
            if args.is_empty() {
                Ok(if id == CLEAR { Type::Unit } else { Type::Int })
            } else {
                Err(format!("{id} does not take arguments"))
            }
        }
        GET => {
            if args.len() == 1 {
                if let Err(r) = &args[0] {
                    return Ok(r.clone());
                }
            }
            Err(format!("{GET} takes single key as argument "))
        }
        INSERT => {
            if args.len() == 2 {
                if let Err(v1) = &args[0] {
                    if let Ok(v2) = &args[1] {
                        if v1 == v2 {
                            return Ok(Type::Unit);
                        }
                    }
                }
            }
            Err(format!("{INSERT} takes key and value as arguments "))
        }
        REMOVE => {
            if args.len() == 1 && args[0].is_err() {
                return Ok(Type::Bool);
            }
            
            Err(format!("{REMOVE} takes single key as argument "))
        }
        GET_MAYBE => {
			if args.len() == 1 {
                if let Err(r) = &args[0] {
                    return Ok(Type::Map(Box::new(Type::Unit), Box::new(r.clone())));
                }
            }
            Err(format!("{GET} takes single key as argument "))
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
