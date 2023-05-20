use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

use derivative::Derivative;

use crate::parser::{BinOp, Block, Expression, Identifier, Program, Type, UnOp, Value};

lazy_static::lazy_static! {
    static ref UNARY_TABLE: HashMap<(UnOp, Type), Type> = {
        let mut m = HashMap::new();
        m.insert((UnOp::Invert, Type::Bool), Type::Bool);
        m.insert((UnOp::Invert, Type::Int), Type::Int);
        m.insert((UnOp::Negate, Type::Int), Type::Int);
        m
    };
    static ref BINARY_TABLE: HashMap<(Type, BinOp, Type), Type> = {
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
    };
}

pub struct TypeCheckContext<'a> {
    next_id: i32,
    root: Rc<RefCell<ScopeInfo<'a>>>,
}

#[derive(Derivative, PartialEq, Eq, Default)]
#[derivative(Debug)]
pub struct ScopeInfo<'a> {
    pub variables: Vec<(Identifier<'a>, Type, i32)>,
    pub functions: Vec<(Identifier<'a>, Vec<Type>, Type, i32)>,
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
        let id = tcc.next_id;
        tcc.next_id += 1;
        tcc.root.borrow_mut().functions.push((
            f.identifier,
            f.arguments.iter().map(|a| a.0).collect(),
            f.return_type,
            id,
        ));
    });

    //check blocks
    ast.functions.iter_mut().for_each(|f| {
        for arg in &f.arguments {
            f.body
                .scopeinfo
                .borrow_mut()
                .variables
                .push((arg.1, arg.0, tcc.next_id));
            tcc.next_id += 1;
        }
        if !tcc.check_block(&mut f.body, Some(f.return_type), tcc.root.clone()) {
            panic!("function {} at {:?} did not return", f.identifier, f.pos);
        }
    });
}

impl<'a> TypeCheckContext<'a> {
    fn check_block(
        &mut self,
        block: &mut Block<'a>,
        returntype: Option<Type>,
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
                    if self.check_expression(ifexpr, block.scopeinfo.clone()) != Type::Bool {
                        panic!("if statement needs a bool")
                    }
                    willreturn &= self.check_block(ifblock, returntype, block.scopeinfo.clone());
                    for (ieexpr, ieblock) in ifelse {
                        if self.check_expression(ieexpr, block.scopeinfo.clone()) != Type::Bool {
                            panic!()
                        }
                        willreturn &=
                            self.check_block(ieblock, returntype, block.scopeinfo.clone());
                    }
                    willreturn &= self.check_block(elseblock, returntype, block.scopeinfo.clone());
                    hasreturned |= willreturn;
                }
                crate::parser::StatementType::While((whileexpr, whileblock)) => {
                    if self.check_expression(whileexpr, block.scopeinfo.clone()) != Type::Bool {
                        panic!()
                    }
                    self.check_block(whileblock, returntype, block.scopeinfo.clone());
                }
                crate::parser::StatementType::Assignment(t, id, expr, o) => {
                    if self.check_expression(expr, block.scopeinfo.clone())
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
                                .any(|(vid, _, _)| vid.eq(id))
                            {
								panic!("already a variable '{id}' in this scope")
							}
                            //if new initialized variable
                            block.scopeinfo.borrow_mut().variables.push((
                                id,
                                t.unwrap(),
                                self.next_id,
                            ));
                            *o=Some(self.next_id);
                            self.next_id += 1;
                            *t.as_ref().unwrap()
                        }
                    {
                        panic!("type of expression {expr:?} does not match type of variable {id}")
                    }
                }
                crate::parser::StatementType::Call(id, exprs, o) => {
                    if let Some(v) = find_function(id, block.scopeinfo.clone()) {
                        if exprs.len() != v.1.len()
                            || !exprs.iter_mut().zip(v.1.iter()).all(|t| {
                                self.check_expression(t.0, block.scopeinfo.clone()) == *t.1
                            })
                        {
                            panic!(
                                "arguments dont match, function {id} needs {:?} but {:?} is given",
                                v.1,
                                exprs
                                    .iter_mut()
                                    .map(|e| self.check_expression(e, block.scopeinfo.clone()))
                                    .collect::<Vec<_>>()
                            );
                        }
                        *o = Some(v.3);
                    } else {
                        panic!("could not find function {id}")
                    }
                }
                crate::parser::StatementType::Return(expr) => {
                    if let Some(rt) = returntype {
                        if self.check_expression(expr, block.scopeinfo.clone()) != rt {
                            panic!("does not return correct type")
                        }
                        hasreturned = true;
                    } else {
                        panic!("can not return from here")
                    }
                }
            }
        });
        hasreturned
            | returntype.is_none()
            | (returntype.is_some() && returntype.unwrap() == Type::Unit)
    }

    fn check_expression(
        &mut self,
        expr: &mut Expression<'a>,
        scopeinfo: Rc<RefCell<ScopeInfo<'a>>>,
    ) -> Type {
        match expr {
            Expression::Binary(l, op, r) => {
                let k = (
                    self.check_expression(l, scopeinfo.clone()),
                    *op,
                    self.check_expression(r, scopeinfo),
                );
                if let Some(t) = BINARY_TABLE.get(&k) {
                    return *t;
                }
                panic!("invalid binary")
            }
            Expression::Unary(op, e) => {
                let k = (*op, self.check_expression(e, scopeinfo));
                if let Some(t) = UNARY_TABLE.get(&k) {
                    return *t;
                }
                panic!("invalid unary")
            }
            Expression::Value(v) => self.check_value(v, scopeinfo),
        }
    }

    fn check_value(
        &mut self,
        value: &mut Value<'a>,
        scopeinfo: Rc<RefCell<ScopeInfo<'a>>>,
    ) -> Type {
        match value {
            Value::Number(_) => Type::Int,
            Value::Bool(_) => Type::Bool,
            Value::Call(id, exprs, o) => {
                if let Some(f) = find_function(id, scopeinfo.clone()) {
                    if exprs.len() != f.1.len()
                        || !exprs
                            .iter_mut()
                            .zip(f.1.iter())
                            .all(|t| self.check_expression(t.0, scopeinfo.clone()) == *t.1)
                    {
                        panic!(
                            "arguments dont match, function {id} needs {:?} but {:?} is given",
                            f.1,
                            exprs
                                .iter_mut()
                                .map(|e| self.check_expression(e, scopeinfo.clone()))
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
                if let Some(v) = find_variable(id, scopeinfo) {
                    *o = Some(v.2);
                    v.1
                } else {
                    panic!("could not find variable {id}")
                }
            }
        }
    }
}

pub fn find_variable<'a>(
    id: Identifier<'_>,
    si: Rc<RefCell<ScopeInfo<'a>>>,
) -> Option<(&'a str, Type, i32)> {
    let mut si = Some(si);
    while let Some(s) = si.clone() {
        if let Some(v) = s.borrow().variables.iter().find(|(vid, _, _)| vid.eq(&id)) {
            return Some(*v);
        }
        si = s.borrow().previous.clone();
    }
    None
}

pub fn find_function<'a>(
    id: Identifier<'_>,
    si: Rc<RefCell<ScopeInfo<'a>>>,
) -> Option<(&'a str, Vec<Type>, Type, i32)> {
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
    None
}
