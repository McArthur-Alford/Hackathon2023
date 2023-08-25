use pest::Parser;
use pest_derive::Parser;
use std::fs;

#[derive(Parser)]
#[grammar = "grammar.pest"]
pub struct CSVParser;

enum Identifier {
    Generic(String),
    Absolute(String),
}

enum Value {
    Text(String),
    Number(i64),
    Identifier(Identifier),
}

struct WME {
    ident: Option<Identifier>,
    attr: Option<String>,
    value: Option<Value>,
}

struct Prod {
    precedence: usize,
    lhs: Vec<WME>,
    rhs: Vec<WME>,
}

fn main() {
    let unparsed_file = fs::read_to_string("script").expect("cannot read file");

    let parse_result = CSVParser::parse(Rule::file, &unparsed_file)
        .expect("Unsuccessful parse")
        .next()
        .unwrap();

    dbg!("{:?}", &parse_result);

    let tokens = parse_result.tokens();

    for token in tokens {
        println!("{:?}", token);
    }
}
