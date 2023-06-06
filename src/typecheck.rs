use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

use derivative::Derivative;

use crate::{
    functions::{self, PREDEFINED_FUNCTIONS},
    parser::{BinOp, Block, Expression, Identifier, Program, Type, UnOp, Value},
};
use once_cell::sync::Lazy;

static UNARY_TABLE: Lazy<HashMap<(UnOp, Type), Type>> = Lazy::new(|| {
    let mut m = HashMap::new();
    m.insert((UnOp::Invert, Type::Bool), Type::Bool);
    m.insert((UnOp::Invert, Type::Int), Type::Int);
    m.insert((UnOp::Negate, Type::Int), Type::Int);
    m
});
static BINARY_TABLE: Lazy<HashMap<(Type, BinOp, Type), Type>> = Lazy::new(|| {
    let mut m = HashMap::new();
    m.insert((Type::Bool, BinOp::And, Type::Bool), Type::Bool);
    m.insert((Type::Bool, BinOp::Or, Type::Bool), Type::Bool);
    m.insert((Type::Bool, BinOp::Xor, Type::Bool), Type::Bool);
    m.insert((Type::Bool, BinOp::Equal, Type::Bool), Type::Bool);
    m.insert((Type::Bool, BinOp::NotEqual, Type::Bool), Type::Bool);

    m.insert((Type::Int, BinOp::Add, Type::Int), Type::Int);
    m.insert((Type::Int, BinOp::And, Type::Int), Type::Int);
    m.insert((Type::Int, BinOp::Divide, Type::Int), Type::Int);
    m.insert((Type::Int, BinOp::Modulo, Type::Int), Type::Int);
    m.insert((Type::Int, BinOp::Multiply, Type::Int), Type::Int);
    m.insert((Type::Int, BinOp::Or, Type::Int), Type::Int);
    m.insert((Type::Int, BinOp::Subtract, Type::Int), Type::Int);
    m.insert((Type::Int, BinOp::Xor, Type::Int), Type::Int);

    m.insert((Type::Int, BinOp::Equal, Type::Int), Type::Bool);
    m.insert((Type::Int, BinOp::NotEqual, Type::Int), Type::Bool);
    m.insert((Type::Int, BinOp::Greater, Type::Int), Type::Bool);
    m.insert((Type::Int, BinOp::GreaterEqual, Type::Int), Type::Bool);
    m.insert((Type::Int, BinOp::Smaller, Type::Int), Type::Bool);
    m.insert((Type::Int, BinOp::SmallerEqual, Type::Int), Type::Bool);

    //todo chars and floats
    m
});

pub struct TypeCheckContext<'a> {
    next_id: i32,
    root: Rc<RefCell<ScopeInfo<'a>>>,
}

#[derive(Derivative, PartialEq, Eq, Default)]
#[derivative(Debug)]
pub struct ScopeInfo<'a> {
    pub variables: Vec<(Identifier<'a>, Type<'a>, i32, Option<i32>)>,
    pub functions: Vec<(Identifier<'a>, Vec<Type<'a>>, Type<'a>, i32)>,
    pub structmaptypes: Vec<(Identifier<'a>, Vec<(Identifier<'a>, Type<'a>)>, i32)>,
    #[derivative(Debug = "ignore")]
    pub previous: Option<Rc<RefCell<ScopeInfo<'a>>>>,
}

pub fn typecheck(ast: &mut Program) {
    let mut tcc = TypeCheckContext {
        next_id: 0,
        root: ast.scopeinfo.clone(),
    };

    //check for single main function
    if !ast.functions.iter().any(|f| f.identifier.eq("main")) {
        panic!("could not find a top level main function")
    }
    //check for duplicate functions
    let mut functions = HashSet::new();
    ast.functions.iter().for_each(|f| {
        if !functions.insert(f.identifier) {
            panic!("duplicatge definition of {} at {:?}", f.identifier, f.pos);
        }
        if PREDEFINED_FUNCTIONS
            .iter()
            .map(|(s, _, _)| *s)
            .any(|s| s.eq(f.identifier))
        {
            panic!(
                "can not redefine predefined function {} at {:?}",
                f.identifier, f.pos
            );
        }
        let id = tcc.next_id;
        tcc.next_id += 1;
        tcc.root.borrow_mut().functions.push((
            f.identifier,
            f.arguments.iter().map(|a| a.0.clone()).collect(),
            f.return_type.clone(),
            id,
        ));
    });
    //add struct map types
    for sm in &ast.structmaps {
        tcc.root.borrow_mut().structmaptypes.push((
            sm.identifier,
            sm.associations.clone(),
            tcc.next_id,
        ));
        tcc.next_id += 1;
    }

    //check blocks
    ast.functions.iter_mut().for_each(|f| {
        for (i, arg) in f.arguments.iter().enumerate() {
            if let Type::StructMap(id) = arg.0 {
                find_structmaptype(id, tcc.root.clone())
                    .unwrap_or_else(|| panic!("map type {id} not defined"));
            }
            f.body.scopeinfo.borrow_mut().variables.push((
                arg.1,
                arg.0.clone(),
                tcc.next_id,
                Some(i as i32),
            ));
            tcc.next_id += 1;
        }
        if !tcc.check_block(&mut f.body, &Some(f.return_type.clone()), tcc.root.clone()) {
            panic!("function {} at {:?} did not return", f.identifier, f.pos);
        }
    });
}

impl<'a> TypeCheckContext<'a> {
    fn check_block(
        &mut self,
        block: &mut Block<'a>,
        returntype: &Option<Type<'a>>,
        previous_scope: Rc<RefCell<ScopeInfo<'a>>>,
    ) -> bool {
        block.scopeinfo.borrow_mut().previous = Some(previous_scope);
        //check blocks
        //check for duplicate variables identifiers
        //check types
        //check for return statements

        let mut hasreturned = false;
        block.statements.iter_mut().for_each(|s| {
            match &mut s.statement {
                crate::parser::StatementType::If((ifexpr, ifblock), ifelse, elseblock) => {
                    let mut willreturn = true;
                    if self.check_expression(ifexpr, block.scopeinfo.clone(), None) != Type::Bool {
                        panic!("if statement needs a bool")
                    }
                    willreturn &= self.check_block(ifblock, returntype, block.scopeinfo.clone());
                    for (ieexpr, ieblock) in ifelse {
                        if self.check_expression(ieexpr, block.scopeinfo.clone(), None)
                            != Type::Bool
                        {
                            panic!()
                        }
                        willreturn &=
                            self.check_block(ieblock, returntype, block.scopeinfo.clone());
                    }
                    willreturn &= self.check_block(elseblock, returntype, block.scopeinfo.clone());
                    hasreturned |= willreturn;
                }
                crate::parser::StatementType::While((whileexpr, whileblock)) => {
                    if self.check_expression(whileexpr, block.scopeinfo.clone(), None) != Type::Bool
                    {
                        panic!()
                    }
                    self.check_block(whileblock, returntype, block.scopeinfo.clone());
                }
                crate::parser::StatementType::Assignment(t, id, expr, o) => {
                    if let Some(Type::StructMap(id)) = t {
                        find_structmaptype(id, block.scopeinfo.clone())
                            .unwrap_or_else(|| panic!("map type {id} not defined"));
                    }

                    if self.check_expression(expr, block.scopeinfo.clone(), None)
                        != if t.is_none() {
                            //if updating a value
                            //todo maybe give new numeric id
                            if let Some(v) = find_variable(id, block.scopeinfo.clone()) {
                                *o = Some(v.2);
                                v.1
                            } else {
                                panic!(" could not find variable '{id}'")
                            }
                        } else {
                            if block
                                .scopeinfo
                                .borrow()
                                .variables
                                .iter()
                                .any(|(vid, _, _, _)| vid.eq(id))
                            {
                                panic!("already a variable '{id}' in this scope")
                            }
                            //if new initialized variable
                            block.scopeinfo.borrow_mut().variables.push((
                                id,
                                t.as_ref().unwrap().clone(),
                                self.next_id,
                                None,
                            ));
                            *o = Some(self.next_id);
                            self.next_id += 1;
                            t.as_ref().unwrap().clone()
                        }
                    {
                        panic!("type of expression {expr:?} does not match type of variable {id}")
                    }
                }
                crate::parser::StatementType::Call(id, exprs, o) => {
                    if let Some(v) = find_function(id, block.scopeinfo.clone()) {
                        if exprs.len() != v.1.len()
                            || !exprs.iter_mut().zip(v.1.iter()).all(|t| {
                                self.check_expression(t.0, block.scopeinfo.clone(), None) == *t.1
                            })
                        {
                            panic!(
                                "arguments dont match, function {id} needs {:?} but {:?} is given",
                                v.1,
                                exprs
                                    .iter_mut()
                                    .map(|e| self.check_expression(
                                        e,
                                        block.scopeinfo.clone(),
                                        None
                                    ))
                                    .collect::<Vec<_>>()
                            );
                        }
                        *o = Some(v.3);
                    } else {
                        panic!("could not find function {id}")
                    }
                }
                crate::parser::StatementType::MapCall(id, id2, exprs, o) => {
                    let fv = find_variable(id, block.scopeinfo.clone());
                    if let Some((_, Type::Map(k, v), n, _)) = fv {
                        *o = Some(n);
                        if let Err(e) = functions::valid_map_function(
                            *k,
                            *v,
                            &exprs
                                .iter_mut()
                                .map(|e| self.check_expression(e, block.scopeinfo.clone(), None))
                                .collect(),
                            id2,
                        ) {
                            panic!("{e}");
                        }
                    } else if let Some((_, Type::StructMap(msc), n, _)) = fv {
                        if let Some(r) = find_structmaptype(msc, block.scopeinfo.clone()) {
                            *o = Some(n);
                            if let Err(e) = functions::valid_map_struct_function(
                                id2,
                                exprs
                                    .iter_mut()
                                    .map(|e| {
                                        if let Expression::Value(Value::Identifier(id, _), _) = e {
                                            if let Some((_, t)) = r.1.iter().find(|(s, _)| s.eq(id))
                                            {
                                                return Err(t.clone());
                                            }
                                        }
                                        Ok(self.check_expression(e, block.scopeinfo.clone(), None))
                                    })
                                    .collect(),
                            ) {
                                panic!("{e}");
                            }
                        } else {
                            panic!("could not find map type {msc}");
                        }
                    } else {
                        panic!("could not find map {id}")
                    }
                }
                crate::parser::StatementType::Return(expr) => {
                    if let Some(rt) = returntype {
                        if self.check_expression(expr, block.scopeinfo.clone(), None) != *rt {
                            panic!("does not return correct type")
                        }
                        hasreturned = true;
                    } else {
                        panic!("can not return from here")
                    }
                }
                crate::parser::StatementType::Creation(t, id, o) => {
                    if block
                        .scopeinfo
                        .borrow()
                        .variables
                        .iter()
                        .any(|(vid, _, _, _)| vid.eq(id))
                    {
                        panic!("already a variable or map '{id}' in this scope")
                    }
                    block.scopeinfo.borrow_mut().variables.push((
                        id,
                        t.clone(),
                        self.next_id,
                        None,
                    ));
                    *o = Some(self.next_id);
                    self.next_id += 1;
                }
                crate::parser::StatementType::Free(id, o) => {
                    let var = find_variable(id, block.scopeinfo.clone());
                    if let Some((_, Type::Map(_, _), n, _)) = var {
                        *o = Some(n);
                    } else if let Some((_, Type::StructMap(_), n, _)) = var {
                        *o = Some(n);
                    }else{
						panic!("could not find map {id}")
					}
                }
            }
        });
        hasreturned
            | returntype.is_none()
            | (returntype.is_some() && *returntype.as_ref().unwrap() == Type::Unit)
    }

    fn check_expression(
        &mut self,
        expr: &mut Expression<'a>,
        scopeinfo: Rc<RefCell<ScopeInfo<'a>>>,
        _msc: Option<&'a str>,
    ) -> Type<'a> {
        match expr {
            Expression::Binary(l, op, r, t) => {
                let k = (
                    self.check_expression(l, scopeinfo.clone(), None),
                    *op,
                    self.check_expression(r, scopeinfo, None),
                );
                *t = BINARY_TABLE.get(&k).cloned();
                if let Some(t) = t {
                    return t.clone();
                }
                panic!("invalid binary")
            }
            Expression::Unary(op, e, t) => {
                let k = (*op, self.check_expression(e, scopeinfo, None));
                *t = UNARY_TABLE.get(&k).cloned();
                if let Some(t) = t {
                    return t.clone();
                }
                panic!("invalid unary")
            }
            Expression::Value(v, t) => {
                *t = Some(self.check_value(v, scopeinfo));
                t.as_ref().unwrap().clone()
            }
        }
    }

    fn check_value(
        &mut self,
        value: &mut Value<'a>,
        scopeinfo: Rc<RefCell<ScopeInfo<'a>>>,
    ) -> Type<'a> {
        match value {
            Value::Number(_) => Type::Int,
            Value::Bool(_) => Type::Bool,
            Value::Char(_) => Type::Char,
            Value::Call(id, exprs, o) => {
                if let Some(f) = find_function(id, scopeinfo.clone()) {
                    if exprs.len() != f.1.len()
                        || !exprs
                            .iter_mut()
                            .zip(f.1.iter())
                            .all(|t| self.check_expression(t.0, scopeinfo.clone(), None) == *t.1)
                    {
                        panic!(
                            "arguments dont match, function {id} needs {:?} but {:?} is given",
                            f.1,
                            exprs
                                .iter_mut()
                                .map(|e| self.check_expression(e, scopeinfo.clone(), None))
                                .collect::<Vec<_>>()
                        );
                    }
                    *o = Some(f.3);
                    f.2
                } else {
                    panic!("could not find function {id}")
                }
            }
            Value::Identifier(id, o) => {
                if let Some(v) = find_variable(id, scopeinfo.clone()) {
                    *o = Some(v.2);
                    v.1
                } else {
                    panic!("could not find variable {id}")
                }
            }
            Value::MapCall(id, id2, exprs, o) => {
                let fv = find_variable(id, scopeinfo.clone());
                if let Some((_, Type::Map(k, v), n, _)) = fv {
                    *o = Some(n);
                    match functions::valid_map_function(
                        *k,
                        *v,
                        &exprs
                            .iter_mut()
                            .map(|e| self.check_expression(e, scopeinfo.clone(), None))
                            .collect(),
                        id2,
                    ) {
                        Ok(t) => t,
                        Err(e) => panic!("{e}"),
                    }
                } else if let Some((_, Type::StructMap(id3), n, _)) = fv {
                    if let Some(r) = find_structmaptype(id3, scopeinfo.clone()) {
                        *o = Some(n);
                        match functions::valid_map_struct_function(
                            id2,
                            exprs
                                .iter_mut()
                                .map(|e| {
                                    if let Expression::Value(Value::Identifier(key, _), _) = &e {
                                        if let Some((_, t)) = r.1.iter().find(|(s, _)| key.eq(s)) {
                                            return Err(t.clone());
                                        }
                                    }
                                    Ok(self.check_expression(e, scopeinfo.clone(), None))
                                })
                                .collect(),
                        ) {
                            Ok(t) => t,
                            Err(e) => panic!("{e}"),
                        }
                    } else {
                        panic!("could not find map type {id3}");
                    }
                } else {
                    panic!("could not find map {id}")
                }
            }
        }
    }
}

pub fn find_variable<'a>(
    id: Identifier<'_>,
    si: Rc<RefCell<ScopeInfo<'a>>>,
) -> Option<(&'a str, Type<'a>, i32, Option<i32>)> {
    let mut si = Some(si);
    while let Some(s) = si.clone() {
        if let Some(v) = s
            .borrow()
            .variables
            .iter()
            .find(|(vid, _, _, _)| vid.eq(&id))
        {
            return Some(v.clone());
        }
        si = s.borrow().previous.clone();
    }
    None
}

pub fn find_structmaptype<'a>(
    id: Identifier<'_>,
    si: Rc<RefCell<ScopeInfo<'a>>>,
) -> Option<(&'a str, Vec<(Identifier<'a>, Type<'a>)>, i32)> {
    let mut si = Some(si);
    while let Some(s) = si.clone() {
        if let Some(v) = s
            .borrow()
            .structmaptypes
            .iter()
            .find(|(vid, _, _)| vid.eq(&id))
        {
            return Some(v.clone());
        }
        si = s.borrow().previous.clone();
    }
    None
}

pub fn find_function<'a>(
    id: Identifier<'_>,
    si: Rc<RefCell<ScopeInfo<'a>>>,
) -> Option<(&'a str, Vec<Type<'a>>, Type<'a>, i32)> {
    let mut si = Some(si);
    while let Some(s) = si.clone() {
        if let Some(v) = s
            .borrow()
            .functions
            .iter()
            .find(|(vid, _, _, _)| vid.eq(&id))
        {
            return Some(v.clone());
        }
        si = s.borrow().previous.clone();
    }
    PREDEFINED_FUNCTIONS
        .iter()
        .find(|(s, _, _)| s.eq(&id))
        .map(|(s, args, rt)| (*s, args.clone(), rt.clone(), -1))
}
