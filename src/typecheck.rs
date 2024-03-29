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

    m.insert((Type::Float, BinOp::Add, Type::Float), Type::Float);
    m.insert((Type::Float, BinOp::And, Type::Float), Type::Float);
    m.insert((Type::Float, BinOp::Divide, Type::Float), Type::Float);
    m.insert((Type::Float, BinOp::Multiply, Type::Float), Type::Float);
    m.insert((Type::Float, BinOp::Or, Type::Float), Type::Float);
    m.insert((Type::Float, BinOp::Subtract, Type::Float), Type::Float);
    m.insert((Type::Float, BinOp::Xor, Type::Float), Type::Float);

    m.insert((Type::Float, BinOp::Equal, Type::Float), Type::Bool);
    m.insert((Type::Float, BinOp::NotEqual, Type::Float), Type::Bool);
    m.insert((Type::Float, BinOp::Greater, Type::Float), Type::Bool);
    m.insert((Type::Float, BinOp::GreaterEqual, Type::Float), Type::Bool);
    m.insert((Type::Float, BinOp::Smaller, Type::Float), Type::Bool);
    m.insert((Type::Float, BinOp::SmallerEqual, Type::Float), Type::Bool);

    //todo chars and floats
    m
});

#[derive(Hash, Eq, PartialEq, Debug, Clone)]
pub enum ConstValue {
    Bits(u64),
    Map(Vec<(ConstValue, ConstValue)>),
}

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
    //check perfect hash maps
    for fm in &mut ast.findmaps {
        fm.values = tcc.check_perfect_map(fm);
        tcc.root.borrow_mut().variables.push((
            fm.identifier,
            fm.maptype.clone(),
            tcc.next_id,
            None,
        ));
        fm.nid = tcc.next_id;
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
                    let exprtype = self.check_expression(expr, block.scopeinfo.clone(), None);
                    if id != &"_"
                        && exprtype
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
                            false,
                        ) {
                            panic!("{e}");
                        }
                    } else if let Some((_, Type::PerfectMap(k, v), n, _)) = fv {
                        *o = Some(n);
                        if let Err(e) = functions::valid_map_function(
                            *k,
                            *v,
                            &exprs
                                .iter_mut()
                                .map(|e| self.check_expression(e, block.scopeinfo.clone(), None))
                                .collect(),
                            id2,
                            true,
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
				crate::parser::StatementType::Return(None) => {
                    if !matches!(returntype, Some(Type::Unit))  {
						panic!("does not return correct type:{returntype:?}")
                    }
                }
                crate::parser::StatementType::Return(Some(expr)) => {
                    if let Some(rt) = returntype {
                        if self.check_expression(expr, block.scopeinfo.clone(), None) != *rt {
                            panic!("does not return correct type {returntype:?} in {:?}", &s)
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
                    } else {
                        panic!("could not find map {id}")
                    }
                }
                crate::parser::StatementType::For(k, v, map, innerblock, o) => {
                    let var = self.check_value(map, block.scopeinfo.clone());
                    *o = Some(var.clone());
                    let (ktype, vtype) = if let Type::Map(kt, vt) = &var {
                        (kt, vt)
                    } else if let Type::PerfectMap(kt, vt) = &var {
                        (kt, vt)
                    } else {
                        panic!("{map:?} is not a map")
                    };
                    innerblock.scopeinfo.borrow_mut().variables.push((
                        k,
                        *ktype.clone(),
                        self.next_id,
                        None,
                    ));
                    self.next_id += 1;
                    innerblock.scopeinfo.borrow_mut().variables.push((
                        v,
                        *vtype.clone(),
                        self.next_id,
                        None,
                    ));
                    self.next_id += 1;
                    self.check_block(innerblock, returntype, block.scopeinfo.clone());
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
            Value::Int(_) => Type::Int,
            Value::Float(_) => Type::Float,
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
                    if v.1 == Type::Unit {
                        panic!("can not use void type variable {id} as value")
                    }
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
                        false,
                    ) {
                        Ok(t) => t,
                        Err(e) => panic!("{e}"),
                    }
                } else if let Some((_, Type::PerfectMap(k, v), n, _)) = fv {
                    *o = Some(n);
                    match functions::valid_map_function(
                        *k,
                        *v,
                        &exprs
                            .iter_mut()
                            .map(|e| self.check_expression(e, scopeinfo.clone(), None))
                            .collect(),
                        id2,
                        true,
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
            Value::String(_) => Type::PerfectMap(Box::new(Type::Int), Box::new(Type::Char)),
        }
    }

    fn check_perfect_map(
        &mut self,
        fm: &mut crate::parser::PerfectMap<'a>,
    ) -> Vec<(ConstValue, ConstValue)> {
        assert!(
            matches!(fm.maptype, Type::PerfectMap(..)),
            "{fm:?} should be of type map"
        );

        if let Type::PerfectMap(k, v) = &fm.maptype {
            let _id = fm.identifier;
            let mut set: HashSet<ConstValue> = HashSet::new();
            let mut assoc = Vec::new();
            for e in &mut fm.entries {
                let key = self.get_const_value(&mut e.0, k);
                if !set.insert(key.clone()) {
                    panic!("duplicate key {:?}", e.0);
                }
                assoc.push((key, self.get_const_value(&mut e.1, v)));
            }
            assoc
        } else {
            panic!("{} should be of type map", fm.identifier);
        }
    }

    fn get_const_value(&mut self, v: &mut Value<'a>, t: &Type<'a>) -> ConstValue {
        assert_eq!((t), (&self.check_value(v, self.root.clone())));
        match t {
            Type::Unit => todo!(),
            Type::Map(_, _) => todo!(),
            Type::PerfectMap(_key, _val) => match v {
                Value::Int(_) => todo!(),
                Value::Float(_) => todo!(),
                Value::Bool(_) => todo!(),
                Value::Call(_, _, _) => todo!(),
                Value::Identifier(_, _) => todo!(),
                Value::Char(_) => todo!(),
                Value::MapCall(_, _, _, _) => todo!(),
                Value::String(s) => {
					let str = s.replace("\\n", "\n").into_bytes();
					ConstValue::Bits(str.iter().enumerate().fold(str.len() as u64, |acc, (p, b)| {
						acc ^ (*b as u64).rotate_right(p as u32)
					}))
				},
            },
            Type::StructMap(_) => todo!(),
            _ => ConstValue::Bits(match v {
                Value::Int(i) => *i as u64,
                Value::Float(i) => i.to_bits(),
                Value::Bool(b) => *b as u64,
                _ => panic!("invalid"),
            }),
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
