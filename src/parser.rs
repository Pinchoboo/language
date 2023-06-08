use std::{
    cell::RefCell,
    fmt::{Debug, Display},
    fs::File,
    io::Read,
    path::{Path, PathBuf},
    rc::Rc, process::exit,
};

use derivative::Derivative;
use once_cell::sync::Lazy;
use pest::{error::Error, iterators::Pair, pratt_parser::PrattParser, Parser, Span};

use crate::typecheck::ScopeInfo;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct LanguageParser;

static PRATT_PARSER: Lazy<PrattParser<Rule>> = Lazy::new(|| {
    use pest::pratt_parser::{Assoc::*, Op};
    use Rule::*;
    // Precedence is defined lowest to highest
    PrattParser::new()
        .op(Op::infix(or, Left))
        .op(Op::infix(xor, Left))
        .op(Op::infix(and, Left))
        .op(Op::infix(equal, Left) | Op::infix(notEqual, Left))
        .op(Op::infix(greater, Left)
            | Op::infix(greaterEqual, Left)
            | Op::infix(smaller, Left)
            | Op::infix(smallerEqual, Left))
        //bit shift here
        .op(Op::infix(add, Left) | Op::infix(subtract, Left))
        .op(Op::infix(multiply, Left) | Op::infix(divide, Left) | Op::infix(modulo, Left))
        .op(Op::prefix(negate) | Op::prefix(invert))
});

#[derive(Debug, PartialEq, Eq)]
pub struct Possition<'a> {
    filename: &'a Path,
    span: Span<'a>,
}

#[derive(Derivative, PartialEq)]
#[derivative(Debug)]
pub struct Program<'a> {
    #[derivative(Debug = "ignore")]
    pub pos: Possition<'a>,
    pub scopeinfo: Rc<RefCell<ScopeInfo<'a>>>,
    pub functions: Vec<Function<'a>>,
    pub structmaps: Vec<StructMap<'a>>,
}

#[derive(Derivative, PartialEq, Eq)]
#[derivative(Debug)]
pub struct StructMap<'a> {
    #[derivative(Debug = "ignore")]
    pub pos: Possition<'a>,
    pub identifier: Identifier<'a>,
    pub associations: Vec<(Identifier<'a>, Type<'a>)>,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Type<'a> {
    Int,
    Float,
    Bool,
    Char,
    Unit,
    Map(Box<Type<'a>>, Box<Type<'a>>),
    PerfectMap(Box<Type<'a>>, Box<Type<'a>>),
    StructMap(Identifier<'a>),
}

impl<'a> Display for Type<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int => f.write_str("int"),
            Type::Float => f.write_str("float"),
            Type::Bool => f.write_str("bool"),
            Type::Char => f.write_str("char"),
            Type::Unit => f.write_str("void"),
            Type::Map(k, v) => {
                {
                    f.write_str("map_")?;
                    std::fmt::Display::fmt(&k, f)?;
                    f.write_str("_to_")?;
                    std::fmt::Display::fmt(&v, f)?
                };
                Ok(())
            }
            Type::PerfectMap(k, v) => {
                {
                    f.write_str("const_map_")?;
                    std::fmt::Display::fmt(&k, f)?;
                    f.write_str("_to_")?;
                    std::fmt::Display::fmt(&v, f)?
                };
                Ok(())
            }
            Type::StructMap(s) => {
                {
                    f.write_str("mapstruct_")?;
                    std::fmt::Display::fmt(&s, f)?
                };
                Ok(())
            }
        }
    }
}

impl<'i> TryFrom<Pair<'i, Rule>> for Type<'i> {
    type Error = ();
    fn try_from(value: Pair<'i, Rule>) -> Result<Self, Self::Error> {
        if value.as_rule() == Rule::r#type || value.as_rule() == Rule::creatableType {
            let mut value = value.into_inner();
            let inner = value.next().ok_or(())?;
            match inner.as_rule() {
                Rule::intType => Ok(Type::Int),
                Rule::floatType => Ok(Type::Float),
                Rule::boolType => Ok(Type::Bool),
                Rule::charType => Ok(Type::Char),
                Rule::unitType => Ok(Type::Unit),
                Rule::mapType => {
                    let mut inner = inner.into_inner();
                    Ok(Type::Map(
                        Box::new(Type::try_from(inner.next().expect("key type to exist"))?),
                        Box::new(Type::try_from(inner.next().expect("value type to exist"))?),
                    ))
                }
                Rule::structmapType => {
                    Ok(Type::StructMap(inner.into_inner().next().unwrap().as_str()))
                }
                Rule::r#const => {
                    let mut inner = value.next().unwrap().into_inner();
                    Ok(Type::PerfectMap(
                        Box::new(Type::try_from(inner.next().expect("key type to exist"))?),
                        Box::new(Type::try_from(inner.next().expect("value type to exist"))?),
                    ))
                }
                _ => Err(()),
            }
        } else {
            Err(())
        }
    }
}

#[derive(Derivative, PartialEq)]
#[derivative(Debug)]
pub struct Function<'a> {
    #[derivative(Debug = "ignore")]
    pub pos: Possition<'a>,
    pub identifier: Identifier<'a>,
    pub return_type: Type<'a>,
    pub arguments: Vec<Argument<'a>>,
    pub body: Block<'a>,
}
pub type Identifier<'a> = &'a str;

#[derive(Debug, PartialEq)]
pub struct Block<'a> {
    pub scopeinfo: Rc<RefCell<ScopeInfo<'a>>>,
    pub statements: Vec<Statement<'a>>,
}

pub type ConditionalBlock<'a> = (Expression<'a>, Block<'a>);
pub type Argument<'a> = (Type<'a>, Identifier<'a>);

#[derive(Derivative, PartialEq)]
#[derivative(Debug)]
pub struct Statement<'a> {
    #[derivative(Debug = "ignore")]
    pub pos: Possition<'a>,
    pub statement: StatementType<'a>,
}

#[derive(Debug, PartialEq)]
pub enum StatementType<'a> {
    If(ConditionalBlock<'a>, Vec<ConditionalBlock<'a>>, Block<'a>),
    While(ConditionalBlock<'a>),
    Assignment(
        Option<Type<'a>>,
        Identifier<'a>,
        Expression<'a>,
        Option<i32>,
    ),
    Call(Identifier<'a>, Vec<Expression<'a>>, Option<i32>),
    Return(Expression<'a>),
    Creation(Type<'a>, Identifier<'a>, Option<i32>),
    Free(Identifier<'a>, Option<i32>),
    MapCall(
        Identifier<'a>,
        Identifier<'a>,
        Vec<Expression<'a>>,
        Option<i32>,
    ),
    For(Identifier<'a>, Identifier<'a>, Value<'a>, Block<'a>, Option<Type<'a>>),
}

#[derive(Debug, PartialEq)]
pub enum Expression<'a> {
    Binary(
        Box<Expression<'a>>,
        BinOp,
        Box<Expression<'a>>,
        Option<Type<'a>>,
    ),
    Unary(UnOp, Box<Expression<'a>>, Option<Type<'a>>),
    Value(Value<'a>, Option<Type<'a>>),
}

impl<'a> Expression<'a> {
    pub fn get_type(&self) -> Type {
        match self {
            Expression::Binary(_, _, _, t) => t,
            Expression::Unary(_, _, t) => t,
            Expression::Value(_, t) => t,
        }
        .clone()
        .unwrap()
    }
}
#[derive(Debug, PartialEq)]
pub enum Value<'a> {
    Int(i64),
	Float(f64),
    Bool(bool),
    Call(Identifier<'a>, Vec<Expression<'a>>, Option<i32>),
    Identifier(Identifier<'a>, Option<i32>),
    Char(char),
    MapCall(
        Identifier<'a>,
        Identifier<'a>,
        Vec<Expression<'a>>,
        Option<i32>,
    ),
    String(&'a str),
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum BinOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    Or,
    And,
    Xor,
    Equal,
    NotEqual,
    Greater,
    Smaller,
    GreaterEqual,
    SmallerEqual,
}

impl<'i> TryFrom<Pair<'i, Rule>> for BinOp {
    type Error = ();
    fn try_from(value: Pair<Rule>) -> Result<Self, Self::Error> {
        match value.as_rule() {
            Rule::add => Ok(BinOp::Add),
            Rule::subtract => Ok(BinOp::Subtract),
            Rule::multiply => Ok(BinOp::Multiply),
            Rule::divide => Ok(BinOp::Divide),
            Rule::modulo => Ok(BinOp::Modulo),
            Rule::or => Ok(BinOp::Or),
            Rule::and => Ok(BinOp::And),
            Rule::xor => Ok(BinOp::Xor),
            Rule::equal => Ok(BinOp::Equal),
            Rule::notEqual => Ok(BinOp::NotEqual),
            Rule::greater => Ok(BinOp::Greater),
            Rule::greaterEqual => Ok(BinOp::GreaterEqual),
            Rule::smaller => Ok(BinOp::Smaller),
            Rule::smallerEqual => Ok(BinOp::SmallerEqual),
            _ => Err(()),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum UnOp {
    Negate,
    Invert,
}

impl<'i> TryFrom<Pair<'i, Rule>> for UnOp {
    type Error = ();
    fn try_from(value: Pair<Rule>) -> Result<Self, Self::Error> {
        match value.as_rule() {
            Rule::negate => Ok(UnOp::Negate),
            Rule::invert => Ok(UnOp::Invert),
            _ => Err(()),
        }
    }
}

pub struct FileParser {
    path: PathBuf,
    buffer: String,
}
#[derive(Debug)]
pub enum FileParserError {
    FindFile(std::io::Error),
    OpenFile(std::io::Error),
    ReadFile(std::io::Error),
    PestParse(Box<Error<Rule>>),
}
impl<'a> FileParser {
    pub fn new(path: &str) -> Result<FileParser, FileParserError> {
        let path = Path::canonicalize(Path::new(path)).map_err(FileParserError::FindFile)?;
        let mut buffer = String::new();
        File::open(&path)
            .map_err(FileParserError::OpenFile)?
            .read_to_string(&mut buffer)
            .map_err(FileParserError::ReadFile)?;
        Ok(FileParser { path, buffer })
    }

    pub fn parse(&'a self) -> Result<Program<'a>, FileParserError> {
        let pest_program: Pair<Rule> = LanguageParser::parse(Rule::program, &self.buffer)
            .map_err(Box::new)
            .map_err(FileParserError::PestParse)?
            .next()
            .unwrap();

        let mut functions = vec![];
        let mut structs = vec![];
        for p in pest_program.clone().into_inner() {
            match p.as_rule() {
                Rule::structdef => structs.push(self.parse_structdef(p)),
                Rule::function => {
                    functions.push(self.parse_function(p));
                }
                _ => {
                    panic!("unreachable")
                }
            }
        }

        Ok(Program {
            pos: Possition {
                filename: &self.path,
                span: pest_program.as_span(),
            },
            functions,
            structmaps: structs,
            scopeinfo: Rc::new(RefCell::new(ScopeInfo::default())),
        })
    }

    fn parse_function(&'a self, pair: Pair<'a, Rule>) -> Function {
        assert_eq!(pair.as_rule(), Rule::function);
        let span = pair.as_span();

        let mut inner = pair.into_inner();
        let mut current = inner.next().expect("function should have more subpairs");

        let mut return_type = Type::Unit;
        if let Rule::r#type = current.as_rule() {
            return_type = Type::try_from(current).expect("valid type");
            current = inner.next().expect("function should have more subpairs");
        }

        assert_eq!(current.as_rule(), Rule::identifier);
        let identifier = current.as_str();

        //body first so the itterator will only have the arguments
        let body = self.parse_block(
            inner
                .next_back()
                .expect("function should have more subpairs"),
        );

        let mut arguments = vec![];

        //now arguments
        while inner.len() >= 2 {
            arguments.push((
                {
                    current = inner.next().expect("argument should have a type");
                    assert_eq!(current.as_rule(), Rule::r#type);
                    Type::try_from(current).expect("valid type")
                },
                {
                    current = inner.next().expect("argument should have a name");
                    assert_eq!(current.as_rule(), Rule::identifier);
                    current.as_str()
                },
            ));
        }

        Function {
            identifier,
            return_type,
            arguments,
            body,
            pos: Possition {
                filename: &self.path,
                span,
            },
        }
    }

    fn parse_block(&'a self, pair: Pair<'a, Rule>) -> Block {
        assert_eq!(pair.as_rule(), Rule::block);
        let span = pair.as_span();
        Block {
            scopeinfo: Rc::new(RefCell::new(ScopeInfo::default())),
            statements: pair
                .into_inner()
                .map(|sp: Pair<Rule>| {
                    Statement {
                        pos: Possition {
                            filename: &self.path,
                            span,
                        },
                        statement: match sp.as_rule() {
                            Rule::r#if => {
                                let mut inner = sp.into_inner();
                                StatementType::If(
                                    (
                                        self.parse_expression(
                                            inner.next().expect("if should have a condition"),
                                        ),
                                        self.parse_block(
                                            inner.next().expect("if should have a code block"),
                                        ),
                                    ),
                                    {
                                        let mut elseif = vec![];
                                        while inner.len() >= 2 {
                                            elseif.push((
                                                {
                                                    let c = inner
                                                        .next()
                                                        .expect("else if should have a condition");
                                                    //assert_eq!(c.as_rule(), Rule::expression);
                                                    self.parse_expression(c)
                                                },
                                                {
                                                    let b = inner
                                                        .next()
                                                        .expect("else if should have a code block");
                                                    assert_eq!(b.as_rule(), Rule::block);
                                                    self.parse_block(b)
                                                },
                                            ));
                                        }
                                        elseif
                                    },
                                    inner.next().map_or(
                                        Block {
                                            scopeinfo: Rc::new(RefCell::new(ScopeInfo::default())),
                                            statements: Vec::new(),
                                        },
                                        |b| self.parse_block(b),
                                    ),
                                )
                            }
                            Rule::r#while => {
                                let mut inner = sp.into_inner();
                                StatementType::While((
                                    self.parse_expression(
                                        inner.next().expect("while should have a condition"),
                                    ),
                                    self.parse_block(
                                        inner.next().expect("while should have a code block"),
                                    ),
                                ))
                            }
                            Rule::assignment => {
                                let mut inner = sp.into_inner();
                                let mut current =
                                    inner.next().expect("assignment should have a sub pair");
                                StatementType::Assignment(
                                    {
                                        if let Rule::r#type = current.as_rule() {
                                            let old = current;
                                            current = inner
                                                .next()
                                                .expect("assignment should have an identifier");
                                            Some(Type::try_from(old).expect("valid type"))
                                        } else {
                                            None
                                        }
                                    },
                                    current.as_str(),
                                    {
                                        self.parse_expression(
                                            inner
                                                .next()
                                                .expect("assignment should have a variable"),
                                        )
                                    },
                                    None,
                                )
                            }
                            Rule::call => {
                                let mut inner = sp.into_inner();
                                StatementType::Call(
                                    {
                                        let id = inner
                                            .next()
                                            .expect("function call should have an identifier");
                                        assert_eq!(id.as_rule(), Rule::identifier);
                                        id.as_str()
                                    },
                                    inner.map(|e| self.parse_expression(e)).collect(),
                                    None,
                                )
                            }
                            Rule::r#return => StatementType::Return(
                                self.parse_expression(
                                    sp.into_inner()
                                        .next()
                                        .expect("assignment should have a variable"),
                                ),
                            ),
                            Rule::creation => {
                                let mut inner = sp.into_inner();
                                StatementType::Creation(
                                    {
                                        Type::try_from(inner.next().expect("type"))
                                            .expect("valid type")
                                    },
                                    inner
                                        .next()
                                        .expect("creation should have an identifier")
                                        .as_str(),
                                    None,
                                )
                            }

                            Rule::free => StatementType::Free(
                                sp.into_inner().next().expect("identifier").as_str(),
                                None,
                            ),
                            Rule::mapCall => {
                                let mut inner = sp.into_inner();
                                StatementType::MapCall(
                                    inner.next().expect("identifier").as_str(),
                                    {
                                        inner = inner.next().unwrap().into_inner();
                                        inner.next().expect("identifier").as_str()
                                    },
                                    inner.map(|e| self.parse_expression(e)).collect(),
                                    None,
                                )
                            }
                            Rule::r#for => {
                                let mut inner = sp.into_inner();
                                StatementType::For(
                                    inner.next().expect("identifier").as_str(),
                                    inner.next().expect("identifier").as_str(),
									self.parse_value(inner.next().expect("value")),
                                    self.parse_block(inner.next().expect("block")),
                                    None,
                                )
                            }
                            _ => {
                                panic!("unreachable")
                            }
                        },
                    }
                })
                .collect(),
        }
    }

    fn parse_expression(&'a self, pair: Pair<'a, Rule>) -> Expression {
        assert_eq!(pair.as_rule(), Rule::expression);
        PRATT_PARSER
            .map_primary(|value| Expression::Value(self.parse_value(value), None))
            .map_infix(|lhs, op, rhs| {
                let rule = op.as_rule();
                Expression::Binary(
                    Box::new(lhs),
                    BinOp::try_from(op)
                        .unwrap_or_else(|_| panic!("expected infix operation, found {:?}", rule)),
                    Box::new(rhs),
                    None,
                )
            })
            .map_prefix(|op, rhs| {
                let rule = op.as_rule();
                Expression::Unary(
                    UnOp::try_from(op)
                        .unwrap_or_else(|_| panic!("expected unary operation, found {:?}", rule)),
                    Box::new(rhs),
                    None,
                )
            })
            .parse(pair.into_inner())
    }

    fn parse_value(&'a self, pair: Pair<'a, Rule>) -> Value {
        match pair.as_rule() {
            //todo handle float
            Rule::number => {
				if let Ok(v) = pair.as_str().parse::<i64>(){
					Value::Int(v)
				}else if let Ok(v) = pair.as_str().parse::<f64>(){
					Value::Float(v)
				}else{
					panic!("invalid number")
				}
			},
            Rule::boolean => Value::Bool(pair.as_str().parse::<bool>().expect("bool")),
            Rule::identifier => Value::Identifier(pair.as_str(), None),
            Rule::call => {
                let mut inner = pair.into_inner();
                Value::Call(
                    {
                        let id = inner
                            .next()
                            .expect("function call should have an identifier");
                        assert_eq!(id.as_rule(), Rule::identifier);
                        id.as_str()
                    },
                    inner.map(|e| self.parse_expression(e)).collect(),
                    None,
                )
            }
            Rule::char => Value::Char(pair.as_str().chars().nth(1).unwrap()),
            Rule::mapCall => {
                let mut inner = pair.into_inner();
                Value::MapCall(
                    inner.next().expect("identifier").as_str(),
                    {
                        inner = inner.next().unwrap().into_inner();
                        inner.next().expect("identifier").as_str()
                    },
                    inner.map(|e| self.parse_expression(e)).collect(),
                    None,
                )
            }
            Rule::string => Value::String(pair.into_inner().next().unwrap().as_str()),
            _ => panic!("unreachable"),
        }
    }

    fn parse_structdef(&'a self, p: Pair<'a, Rule>) -> StructMap {
        let mut inner = p.clone().into_inner();
        StructMap {
            pos: Possition {
                filename: &self.path,
                span: p.as_span(),
            },
            identifier: { inner.next().unwrap().as_str() },
            associations: { inner.map(|p| self.parse_association(p)).collect() },
        }
    }
    fn parse_association(&'a self, p: Pair<'a, Rule>) -> (Identifier<'a>, Type<'a>) {
        let mut innner = p.into_inner();
        (
            innner.next().unwrap().as_str(),
            innner.next().unwrap().try_into().unwrap(),
        )
    }
}
