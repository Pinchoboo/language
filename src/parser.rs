use std::{
    fmt::Debug,
    fs::File,
    io::Read,
    path::{Path, PathBuf},
};

use pest::{error::Error, iterators::Pair, pratt_parser::PrattParser, Parser, Span};

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct LanguageParser;

lazy_static::lazy_static! {
    static ref PRATT_PARSER: PrattParser<Rule> = {
        use pest::pratt_parser::{Assoc::*, Op};
        use Rule::*;
        // Precedence is defined lowest to highest
        PrattParser::new()
            .op(Op::infix(or, Left))
            .op(Op::infix(xor, Left))
            .op(Op::infix(and, Left))
            .op(Op::infix(equal, Left) | Op::infix(notEqual, Left))
            .op(Op::infix(greater, Left) | Op::infix(greaterEqual, Left) | Op::infix(smaller, Left) | Op::infix(smallerEqual, Left))
            //bit shift here
            .op(Op::infix(add, Left) | Op::infix(subtract, Left))
            .op(Op::infix(multiply, Left) | Op::infix(divide, Left) | Op::infix(modulo, Left))
            .op(Op::prefix(negate) | Op::prefix(invert))
    };
}

#[derive(Debug, PartialEq, Eq)]
pub struct Possition<'a> {
    filename: &'a Path,
    span: Span<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Program<'a> {
    pos: Possition<'a>,
    functions: Vec<Function<'a>>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Type {
    Int,
    Float,
    Bool,
    Char,
    Unit,
}

impl<'i> TryFrom<Pair<'i, Rule>> for Type {
    type Error = ();
    fn try_from(value: Pair<Rule>) -> Result<Self, Self::Error> {
        if value.as_rule() == Rule::r#type {
            match value.into_inner().next().ok_or(())?.as_rule() {
                Rule::intType => Ok(Type::Int),
                Rule::floatType => Ok(Type::Float),
                Rule::boolType => Ok(Type::Bool),
                Rule::charType => Ok(Type::Char),
                Rule::unitType => Ok(Type::Unit),
                _ => Err(()),
            }
        } else {
            Err(())
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Function<'a> {
    pos: Possition<'a>,
    identifier: Identifier<'a>,
    return_type: Type,
    arguments: Vec<Argument<'a>>,
    body: Block<'a>,
}
pub type Identifier<'a> = &'a str;
pub type Block<'a> = Vec<Statement<'a>>;
pub type ConditionalBlock<'a> = (Expression<'a>, Block<'a>);
pub type Argument<'a> = (Type, Identifier<'a>);

#[derive(Debug, PartialEq, Eq)]
pub struct Statement<'a> {
    pos: Possition<'a>,
    statement: StatementType<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum StatementType<'a> {
    If(ConditionalBlock<'a>, Vec<ConditionalBlock<'a>>, Block<'a>),
    While(ConditionalBlock<'a>),
    Assignment(Option<Type>, Identifier<'a>, Expression<'a>),
    Call(Identifier<'a>, Vec<Expression<'a>>),
    Return(Expression<'a>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Expression<'a> {
    Binary(Box<Expression<'a>>, BinOp, Box<Expression<'a>>),
    Unary(UnOp, Box<Expression<'a>>),
    Value(Value<'a>),
}
#[derive(Debug, PartialEq, Eq)]
pub enum Value<'a> {
    Number(i32),
    Bool(bool),
    Call(Identifier<'a>, Vec<Expression<'a>>),
    Identifier(Identifier<'a>),
}
#[derive(Debug, PartialEq, Eq)]
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

#[derive(Debug, PartialEq, Eq)]
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
        Ok(Program {
            pos: Possition {
                filename: &self.path,
                span: pest_program.as_span(),
            },
            functions: pest_program
                .into_inner()
                .map(|p| self.parse_function(p))
                .collect(),
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

        pair.into_inner()
            .map(|sp: Pair<Rule>| {
                match sp.as_rule() {
                    Rule::r#if => {
                        let mut inner = sp.into_inner();
                        Statement {
                            pos: Possition {
                                filename: &self.path,
                                span,
                            },
                            statement: StatementType::If(
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
                                inner.next().map_or(vec![], |b| self.parse_block(b)),
                            ),
                        }
                    }
                    Rule::r#while => {
                        let mut inner = sp.into_inner();
                        Statement {
                            pos: Possition {
                                filename: &self.path,
                                span,
                            },
                            statement: StatementType::While((
                                self.parse_expression(
                                    inner.next().expect("while should have a condition"),
                                ),
                                self.parse_block(
                                    inner.next().expect("while should have a code block"),
                                ),
                            )),
                        }
                    }
                    Rule::assignment => {
                        let mut inner = sp.into_inner();
                        let mut current = inner.next().expect("assignment should have a sub pair");
                        Statement {
                            pos: Possition {
                                filename: &self.path,
                                span,
                            },
                            statement: StatementType::Assignment(
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
                                        inner.next().expect("assignment should have a variable"),
                                    )
                                },
                            ),
                        }
                    }
                    Rule::call => {
                        let mut inner = sp.into_inner();
                        Statement {
                            pos: Possition {
                                filename: &self.path,
                                span,
                            },
                            statement: StatementType::Call(
                                {
                                    let id = inner
                                        .next()
                                        .expect("function call should have an identifier");
                                    assert_eq!(id.as_rule(), Rule::identifier);
                                    id.as_str()
                                },
                                inner.map(|e|self.parse_expression(e)).collect(),
                            ),
                        }
                    }
                    Rule::r#return => Statement {
                        pos: Possition {
                            filename: &self.path,
                            span,
                        },
                        statement: StatementType::Return(self.parse_expression(
                        sp.into_inner()
                            .next()
                            .expect("assignment should have a variable"),
                    ))},
                    _ => {
                        panic!("unreachable")
                    }
                }
            })
            .collect()
    }

    fn parse_expression(&'a self, pair: Pair<'a, Rule>) -> Expression {
        assert_eq!(pair.as_rule(), Rule::expression);
        PRATT_PARSER
            .map_primary(|value| Expression::Value(self.parse_value(value)))
            .map_infix(|lhs, op, rhs| {
                let rule = op.as_rule();
                Expression::Binary(
                    Box::new(lhs),
                    BinOp::try_from(op)
                        .unwrap_or_else(|_| panic!("expected infix operation, found {:?}", rule)),
                    Box::new(rhs),
                )
            })
            .map_prefix(|op, rhs| {
                let rule = op.as_rule();
                Expression::Unary(
                    UnOp::try_from(op)
                        .unwrap_or_else(|_| panic!("expected unary operation, found {:?}", rule)),
                    Box::new(rhs),
                )
            })
            .parse(pair.into_inner())
    }

    fn parse_value(&'a self, pair: Pair<'a, Rule>) -> Value {
        match pair.as_rule() {
            //todo handle float
            Rule::number => Value::Number(pair.as_str().parse::<i32>().expect("int")),
            Rule::boolean => Value::Bool(pair.as_str().parse::<bool>().expect("bool")),
            Rule::identifier => Value::Identifier(pair.as_str()),
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
                )
            }
            _ => panic!("unreachable"),
        }
    }
}
