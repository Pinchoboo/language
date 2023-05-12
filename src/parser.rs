use pest::{error::Error, iterators::Pair, Parser, pratt_parser::PrattParser};

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct LanguageParser;

lazy_static::lazy_static! {
    static ref PRATT_PARSER: PrattParser<Rule> = {
        use pest::pratt_parser::{Assoc::*, Op};
        use Rule::*;

        // Precedence is defined lowest to highest
        PrattParser::new()
            // Addition and subtract have equal precedence
			.op(Op::infix(or, Left))
			.op(Op::infix(xor, Left))
			.op(Op::infix(and, Left))
			.op(Op::infix(equal, Left) | Op::infix(notEqual, Left))
			.op(Op::infix(greater, Left) | Op::infix(greaterEqual, Left) | Op::infix(smaller, Left) | Op::infix(smallerEqual, Left))
            //shift here
			.op(Op::infix(add, Left) | Op::infix(subtract, Left))
            .op(Op::infix(multiply, Left) | Op::infix(divide, Left) | Op::infix(modulo, Left))
            .op(Op::prefix(negate) | Op::prefix(invert))
    };
}

#[derive(Debug, PartialEq, Eq)]
pub struct Program<'a> {
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

#[derive(Debug, PartialEq, Eq)]
pub struct Function<'a> {
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
pub enum Statement<'a> {
    If(ConditionalBlock<'a>, Vec<ConditionalBlock<'a>>, Block<'a>),
    While(ConditionalBlock<'a>),
    Assignment(Option<Type>, Identifier<'a>, Expression<'a>),
    Call(Identifier<'a>, Vec<Expression<'a>>),
    Return(Expression<'a>),
}
#[derive(Debug, PartialEq, Eq)]
pub enum Expression<'a> {
    Binary(Value<'a>, BinOp, Box<Expression<'a>>),
    Unary(UnOp, Value<'a>),
    Value(Value<'a>),
}
#[derive(Debug, PartialEq, Eq)]
pub enum Value<'a> {
    Number(i32),
    Bool(bool),
    Expression(Box<Expression<'a>>),
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

#[derive(Debug, PartialEq, Eq)]
pub enum UnOp {
    Negate,
    Invert,
}

impl TryFrom<&str> for UnOp {
    type Error = ();
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "!" => Ok(UnOp::Invert),
            "-" => Ok(UnOp::Negate),
            _ => Err(()),
        }
    }
}

fn print(i: i32, p: Pair<Rule>) {
    for _ in 0..i {
        print!("\t")
    }
    print!("{:?} [", p.as_rule());
    let txt = p.as_str();
    let inner = p.into_inner();
    if inner.len() == 0 {
        println!("{}]", txt);
    } else {
        println!();
        for inner_pair in inner {
            print(i + 1, inner_pair);
        }
        for _ in 0..i {
            print!("\t");
        }
        println!("]");
    }
}

#[derive(Debug)]
pub enum ParseError {
    PestError(Error<Rule>),
}

pub fn parse_program(program: &str) -> Result<Program, ParseError> {
    let pest_program: Pair<Rule> = LanguageParser::parse(Rule::program, program)
        .map_err(ParseError::PestError)?
        .next()
        .unwrap();
    let program = Program {
        functions: pest_program.into_inner().map(parse_function).collect(),
    };
    Ok(program)
}

fn parse_function(pair: Pair<Rule>) -> Function {
    assert_eq!(pair.as_rule(), Rule::function);

    let mut inner = pair.into_inner();
    let mut current = inner.next().expect("function should have more subpairs");

    let mut return_type = Type::Unit;
    if let Rule::r#type = current.as_rule() {
        return_type = Type::try_from(current.as_str()).expect("valid type");
        current = inner.next().expect("function should have more subpairs");
    }
    assert_eq!(current.as_rule(), Rule::identifier);
    let identifier = current.as_str();

    //body first so the itterator will only have the arguments
    let body = parse_block(
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
                Type::try_from(current.as_str()).expect("valid type")
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
    }
}
fn parse_block(pair: Pair<Rule>) -> Block {
    assert_eq!(pair.as_rule(), Rule::block);
    pair.into_inner()
        .map(|sp: Pair<Rule>| {
            print(0, sp.clone());
            match sp.as_rule() {
                Rule::r#if => {
                    let mut inner = sp.into_inner();
                    Statement::If(
                        (
                            parse_expression(inner.next().expect("if should have a condition")),
                            parse_block(inner.next().expect("if should have a code block")),
                        ),
                        {
                            let mut elseif = vec![];
                            while inner.len() >= 2 {
                                elseif.push((
                                    {
                                        let c =
                                            inner.next().expect("else if should have a condition");
                                        //assert_eq!(c.as_rule(), Rule::expression);
                                        parse_expression(c)
                                    },
                                    {
                                        let b =
                                            inner.next().expect("else if should have a code block");
                                        assert_eq!(b.as_rule(), Rule::block);
                                        parse_block(b)
                                    },
                                ));
                            }
                            elseif
                        },
                        inner.next().map_or(vec![], parse_block),
                    )
                }
                Rule::r#while => {
                    let mut inner = sp.into_inner();
                    Statement::While((
                        parse_expression(inner.next().expect("while should have a condition")),
                        parse_block(inner.next().expect("while should have a code block")),
                    ))
                }
                Rule::assignment => {
                    let mut inner = sp.into_inner();
                    let mut current = inner.next().expect("assignment should have a sub pair");
                    Statement::Assignment(
                        {
                            if let Rule::r#type = current.as_rule() {
								let s = current.as_str();
								current = inner.next().expect("assignment should have an identifier");
                                Some(Type::try_from(s).expect("valid type"))
                            } else {
                                None
                            }
                        },
                        current.as_str(),
                        {
                            parse_expression(
                                inner.next().expect("assignment should have a variable"),
                            )
                        },
                    )
                }
                Rule::call => {
                    let mut inner = sp.into_inner();
                    Statement::Call(
                        {
                            let id = inner
                                .next()
                                .expect("function call should have an identifier");
                            assert_eq!(id.as_rule(), Rule::identifier);
                            id.as_str()
                        },
                        inner.map(parse_expression).collect(),
                    )
                }
                Rule::r#return => Statement::Return(parse_expression(
                    sp.into_inner()
                        .next()
                        .expect("assignment should have a variable"),
                )),
                _ => {
                    panic!("unreachable")
                }
            }
        })
        .collect()
}

fn parse_expression(pair: Pair<Rule>) -> Expression {
    match pair.as_rule() {
        Rule::value => Expression::Value(parse_value(
            pair.into_inner()
                .next()
                .expect("value to contain something"),
        )),
        Rule::unnexpression => {
            let mut inner = pair.into_inner();
            Expression::Unary(
                {
                    let uo = inner
                        .next()
                        .expect("unary expression should have a unary operator");
                    assert_eq!(uo.as_rule(), Rule::unop);
                    UnOp::try_from(uo.as_str()).expect("valid unary operator")
                },
                {
                    let uv = inner.next().expect("unary expression should have a value");
                    assert_eq!(uv.as_rule(), Rule::value);
                    parse_value(uv)
                },
            )
        }
        Rule::binexpression => {
            let mut inner = pair.into_inner();
            Expression::Binary(
                {
                    let bv = inner.next().expect("binary expression should have a value");
                    assert_eq!(bv.as_rule(), Rule::value);
                    parse_value(bv)
                },
                {
                    let bv = inner
                        .next()
                        .expect("binary expression should have a unary operator");
                    assert_eq!(bv.as_rule(), Rule::binop);
                    BinOp::try_from(bv.as_str()).expect("valid binary operator")
                },
                {
                    let be = inner.next().expect("binary expression should have a value");
                    Box::new(parse_expression(be))
                },
            )
        }
        _ => {
            panic!("unreachable")
        }
    }
}

fn parse_value(pair: Pair<Rule>) -> Value {
    match pair.as_rule() {
        Rule::number => Value::Number(pair.as_str().parse::<i32>().expect("int")),
        Rule::boolean => Value::Bool(pair.as_str().parse::<bool>().expect("bool")),
        Rule::identifier => Value::Identifier(pair.as_str()),
        Rule::binexpression | Rule::unnexpression | Rule::value => {
            Value::Expression(Box::new(parse_expression(pair)))
        }
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
                inner.map(parse_expression).collect(),
            )
        }
        _ => {
            panic!("unreachable")
        }
    }
}
pub fn test() {
    let pairs = LanguageParser::parse(
        Rule::program,
        "
	fn main(){
		if true{}else if false{}else{}
		int ident = 1+2 
		while true{}
		selfdefined(-1,true)
	}",
    )
    .unwrap_or_else(|e| panic!("{}", e));
    // Because ident_list is silent, the iterator will contain idents
    for pair in pairs {
        // A pair is a combination of the rule which matched and a span of input
        print(0, pair);
        println!();
    }
}
