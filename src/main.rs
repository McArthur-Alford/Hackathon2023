use pest::{
    iterators::{Pair, Pairs},
    Parser,
};
use pest_derive::Parser;
use std::fs;

#[derive(Parser)]
#[grammar = "grammar.pest"]
pub struct CSVParser;

#[derive(Debug)]
struct Variable {
    identifier: String,
}

#[derive(Debug)]
enum Value {
    Text(String),
    Number(i64),
    Variable(Variable),
    Bool(bool),
}

#[derive(Debug)]
struct WME {
    ident: Option<Variable>,
    attr: Option<String>,
    value: Option<Value>,
}

#[derive(Debug)]
struct Prod {
    precedence: usize,
    lhs: Vec<WME>,
    rhs: Vec<WME>,
}

fn process_variable(pair: Pair<Rule>) -> Option<Variable> {
    let mut inner: Pairs<Rule> = pair.into_inner(); // we know this is a variable
    let contents = inner.next().unwrap();
    match contents.clone().as_rule() {
        Rule::generic => Some(Variable {
            identifier: contents
                .into_inner()
                .next()
                .unwrap()
                .as_span()
                .as_str()
                .to_string(),
        }),
        _ => None,
    }
}

fn process_attr(pair: Pair<Rule>) -> Option<String> {
    let mut inner: Pairs<Rule> = pair.into_inner();
    let contents = inner.next().unwrap();
    if contents.as_rule() == Rule::wildcard {
        None
    } else {
        Some(contents.as_str().to_string())
    }
}

fn process_value(pair: Pair<Rule>) -> Option<Value> {
    let mut inner = pair.into_inner();
    let contents = inner.next().unwrap();
    match contents.clone().as_rule() {
        Rule::constant => {
            let mut inner = contents.into_inner();
            let contents = inner.next().unwrap();
            match contents.clone().as_rule() {
                Rule::string => {
                    let string = contents.as_span().as_str().to_string();
                    let mut chars = string.chars();
                    chars.next();
                    chars.next_back();
                    let string = chars.as_str().to_string();
                    Some(Value::Text(string))
                }
                Rule::number => Some(Value::Number(contents.as_span().as_str().parse().unwrap())),
                Rule::bool => Some(Value::Bool(match contents.as_span().as_str() {
                    "True" => true,
                    _ => false,
                })),
                _ => {
                    panic!()
                }
            }
        }
        Rule::var => Some(Value::Variable(process_variable(contents)?)),
        _ => {
            panic!()
        }
    }
}

fn process_wme(pair: Pair<Rule>) -> WME {
    // "Safe" to assume pair IS a WME
    let mut inner: Pairs<Rule> = pair.into_inner();
    let ident = process_variable(inner.next().unwrap());
    let attr = process_attr(inner.next().unwrap());
    let value = process_value(inner.next().unwrap());

    WME { ident, attr, value }
}

fn process_block(pair: Pair<Rule>) -> Vec<WME> {
    // "Safe" to assume pair IS a block
    let mut output = Vec::new();
    let mut inner: Pairs<Rule> = pair.into_inner();
    for elem in inner {
        output.push(process_wme(elem));
    }
    output
}

fn process_production(pair: Pair<Rule>) -> Prod {
    // "Safe" to assume pair IS a production
    let mut inner: Pairs<Rule> = pair.into_inner();
    let id = inner.next().unwrap();
    let lhs = inner.next().unwrap();
    let rhs = inner.next().unwrap();
    Prod {
        precedence: 0,
        lhs: process_block(lhs),
        rhs: process_block(rhs),
    }
}

fn process_file(pair: Pair<Rule>) -> Vec<Prod> {
    // "Safe" to assume pair IS a file
    let mut output = Vec::new();
    for prod in pair.into_inner() {
        if prod.as_rule() == Rule::prod {
            // Valid production,
            output.push(process_production(prod));
        }
    }
    output
}

fn main() {
    let unparsed_file = fs::read_to_string("script").expect("cannot read file");

    let file = CSVParser::parse(Rule::file, &unparsed_file)
        .expect("Unsuccessful parse")
        .next()
        .unwrap();

    let out = process_file(file);
    dbg!(out);
}
