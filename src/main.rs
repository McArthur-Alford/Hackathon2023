use pest::Parser;
use pest_derive::Parser;
use std::fs;

#[derive(Parser)]
#[grammar = "grammar.pest"]
pub struct CSVParser;

struct rule {}

fn main() {
    let unparsed_file = fs::read_to_string("script").expect("cannot read file");

    let file = CSVParser::parse(Rule::file, &unparsed_file).expect("Unsuccessful parse");
    let tokens = file.tokens();

    for token in tokens {
        println!("{:?}", token);
    }
}
