use pest::{
    iterators::{Pair, Pairs},
    Parser,
};
use pest_derive::Parser;
use std::collections::{HashMap, HashSet};
use std::fs;

#[derive(Parser)]
#[grammar = "grammar.pest"]
pub struct CSVParser;

#[derive(Debug, Clone, Eq, PartialEq)]
struct Variable {
    identifier: String,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum Literal {
    Text(String),
    Number(i64),
    Bool(bool),
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum AbstractAttribute {
    Literal(String),
    Variable(Variable),
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum AbstractValue {
    Literal(Literal),
    Variable(Variable),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum ConcreteValue {
    Literal(Literal),
    Variable(EntityId),
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct AbstractWME {
    ident: Variable,
    attr: AbstractAttribute,
    value: AbstractValue,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct ConcreteWME {
    ident: EntityId,
    attr: String,
    value: ConcreteValue,
}

#[derive(Debug, Clone)]
struct AbstractProd {
    precedence: usize,
    lhs: Vec<AbstractWME>,
    rhs: Vec<AbstractWME>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct EntityId(usize);

#[derive(Debug)]
struct AlphaMemory {
    memories: HashSet<ConcreteWME>,
}

impl AlphaMemory {
    fn activate(&mut self, cw: ConcreteWME) {
        // Add the cw into this alpha memory
        self.memories.insert(cw);
    }
}

struct WMEStore {}

#[derive(Debug)]
struct ConstantTestNode {
    // Test to perform on incoming ConcreteWMEs
    test: Option<AbstractWME>,
    // Downstream alpha memories
    output_memory: Option<AlphaMemory>,
    // Downstream constant tests
    children: Vec<Box<ConstantTestNode>>,
}

// Ensures:
// cw and aw have the same attribute (if it is literal)
// cw and aw have the same value IF it is a literal
fn pattern_match(cw: ConcreteWME, aw: AbstractWME) -> bool {
    // Match the attr if it is literal
    if let AbstractAttribute::Literal(lit) = aw.attr {
        if lit != cw.attr {
            return false;
        }
    }
    // Match the value if it is literal
    if let AbstractValue::Literal(lit) = aw.value {
        if let ConcreteValue::Literal(lit2) = cw.value {
            if lit != lit2 {
                return false;
            }
        }
    }
    true
}

impl ConstantTestNode {
    fn activate(&mut self, cw: ConcreteWME) {
        if let Some(test) = self.test.clone() {
            if pattern_match(cw.clone(), test) {
                // CW matched this constant test node pattern
                // Add it to any directly downstream alpha memory:
                if let Some(output_memory) = &mut self.output_memory {
                    output_memory.activate(cw.clone());
                }

                // Trigger all downstream concrete tests:
                for child in &mut self.children {
                    child.activate(cw.clone());
                }
            }
        } else {
            // CW matched this constant test node pattern
            // Add it to any directly downstream alpha memory:
            if let Some(output_memory) = &mut self.output_memory {
                output_memory.activate(cw.clone());
            }

            // Trigger all downstream concrete tests:
            for child in &mut self.children {
                child.activate(cw.clone());
            }
        }
    }

    // This should only be run on root
    // else everything in the world will crash & burn
    fn add_awme(&mut self, aw: AbstractWME) {
        self.add_awme_attr(aw);
    }

    // This should only be run on the middle rule
    fn add_awme_attr(&mut self, aw: AbstractWME) {
        for child in &mut self.children {
            // This child has the same test as this
            if let Some(test) = child.test.clone() {
                if test.attr == aw.clone().attr {
                    // We hit an existing child testing this attr!
                    for child2 in &mut child.children {
                        if let Some(test) = child2.test.clone() {
                            if test.value == aw.value {
                                return;
                            }
                        }
                    }
                    self.children.push(Box::new(ConstantTestNode {
                        test: Some(AbstractWME {
                            ident: aw.ident.clone(),
                            attr: aw.attr.clone(),
                            value: aw.value.clone(),
                        }),
                        output_memory: Some(AlphaMemory {
                            memories: HashSet::new(),
                        }),
                        children: Vec::new(),
                    }));
                    return;
                }
            }
        }
        // No child already matched the attr part
        // Create a new child!

        // We make an output memory for a new alpha node if there isnt any more depth
        let mut children: Vec<Box<ConstantTestNode>> = Vec::new();
        let output_memory = if !(matches!(aw.value, AbstractValue::Variable(_))) {
            // We can also create a child node, seeing as it goes deeper
            children.push(Box::new(ConstantTestNode {
                test: Some(AbstractWME {
                    ident: aw.ident.clone(),
                    attr: aw.attr.clone(),
                    value: aw.value,
                }),
                output_memory: Some(AlphaMemory {
                    memories: HashSet::new(),
                }),
                children: Vec::new(),
            }));
            None
        } else {
            Some(AlphaMemory {
                memories: HashSet::new(),
            })
        };
        self.children.push(Box::new(ConstantTestNode {
            test: Some(AbstractWME {
                ident: aw.ident.clone(),
                attr: aw.attr.clone(),
                value: AbstractValue::Variable(Variable {
                    identifier: "_".to_string(),
                }),
            }),
            output_memory,
            children,
        }));
    }

    // Drops an entityId from the network
    // Useful if it is being modified
    fn drop_entity(&mut self, id: EntityId) {
        // if let Some(memory) = self.output_memory {
        //     memory.drop_entity(id);
        // }
        // for child in &mut self.children {
        //     child.
        // }
    }
}

fn process_variable(pair: Pair<Rule>) -> Variable {
    let mut inner: Pairs<Rule> = pair.into_inner(); // we know this is a variable
    let contents = inner.next().unwrap();
    match contents.clone().as_rule() {
        Rule::generic => {
            (Variable {
                identifier: contents
                    .into_inner()
                    .next()
                    .unwrap()
                    .as_span()
                    .as_str()
                    .to_string(),
            })
        }
        _ => panic!(),
    }
}

fn process_attr(pair: Pair<Rule>) -> AbstractAttribute {
    let mut inner: Pairs<Rule> = pair.into_inner();
    let contents = inner.next().unwrap();
    match contents.clone().as_rule() {
        Rule::generic => AbstractAttribute::Variable(Variable {
            identifier: contents
                .into_inner()
                .next()
                .unwrap()
                .as_span()
                .as_str()
                .to_string(),
        }),
        _ => AbstractAttribute::Literal(contents.as_span().as_str().to_string()),
    }
    // AbstractAttribute::Literal("WOO".to_string())
}

fn process_value(pair: Pair<Rule>) -> AbstractValue {
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
                    (AbstractValue::Literal(Literal::Text(string)))
                }
                Rule::number => {
                    (AbstractValue::Literal(Literal::Number(
                        contents.as_span().as_str().parse().unwrap(),
                    )))
                }
                Rule::bool => {
                    (AbstractValue::Literal(Literal::Bool(match contents.as_span().as_str() {
                        "True" => true,
                        _ => false,
                    })))
                }
                _ => {
                    panic!()
                }
            }
        }
        Rule::var => (AbstractValue::Variable(process_variable(contents))),
        _ => {
            panic!()
        }
    }
}

fn process_wme(pair: Pair<Rule>) -> AbstractWME {
    // "Safe" to assume pair IS a WME
    let mut inner: Pairs<Rule> = pair.into_inner();
    let ident = process_variable(inner.next().unwrap());
    let attr = process_attr(inner.next().unwrap());
    let value = process_value(inner.next().unwrap());

    AbstractWME { ident, attr, value }
}

fn process_block(pair: Pair<Rule>) -> Vec<AbstractWME> {
    // "Safe" to assume pair IS a block
    let mut output = Vec::new();
    let mut inner: Pairs<Rule> = pair.into_inner();
    for elem in inner {
        output.push(process_wme(elem));
    }
    output
}

fn process_production(pair: Pair<Rule>) -> AbstractProd {
    // "Safe" to assume pair IS a production
    let mut inner: Pairs<Rule> = pair.into_inner();
    let id = inner.next().unwrap();
    let lhs = inner.next().unwrap();
    let rhs = inner.next().unwrap();
    AbstractProd {
        precedence: 0,
        lhs: process_block(lhs),
        rhs: process_block(rhs),
    }
}

fn process_file(pair: Pair<Rule>) -> Vec<AbstractProd> {
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

    let root = ConstantTestNode {
        test: None,
        output_memory: None,
        children: Vec::new(),
    };
    dbg!(root);
}

#[cfg(test)]
mod tests {
    use crate::*;
    #[test]
    fn test_add_rule() {
        let mut root = ConstantTestNode {
            test: Some(AbstractWME {
                ident: Variable {
                    identifier: "_".to_string(),
                },
                attr: AbstractAttribute::Variable(Variable {
                    identifier: "_".to_string(),
                }),
                value: AbstractValue::Variable(Variable {
                    identifier: "_".to_string(),
                }),
            }),
            output_memory: Some(AlphaMemory {
                memories: HashSet::new(),
            }),
            children: vec![],
        };
        root.add_awme(AbstractWME {
            ident: Variable {
                identifier: "x".to_string(),
            },
            attr: AbstractAttribute::Literal("yeet".to_string()),
            value: AbstractValue::Literal(Literal::Number(1)),
        });

        let test_wme1 = ConcreteWME {
            ident: EntityId(0),
            attr: "yeet".to_string(),
            value: ConcreteValue::Literal(Literal::Number(1)),
        };
        let test_wme2 = ConcreteWME {
            ident: EntityId(1),
            attr: "yeet".to_string(),
            value: ConcreteValue::Literal(Literal::Number(2)),
        };

        root.activate(test_wme1);
        root.activate(test_wme2);

        dbg!(&root);
    }

    #[test]
    fn test_add_wme() {
        let child = ConstantTestNode {
            test: Some(AbstractWME {
                ident: Variable {
                    identifier: "_".to_string(),
                },
                attr: AbstractAttribute::Variable(Variable {
                    identifier: "_".to_string(),
                }),
                value: AbstractValue::Literal(Literal::Number(1)),
            }),
            output_memory: Some(AlphaMemory {
                memories: HashSet::new(),
            }),
            children: Vec::new(),
        };
        let child = ConstantTestNode {
            test: Some(AbstractWME {
                ident: Variable {
                    identifier: "_".to_string(),
                },
                attr: AbstractAttribute::Literal("yete".to_string()),
                value: AbstractValue::Variable(Variable {
                    identifier: "_".to_string(),
                }),
            }),
            output_memory: Some(AlphaMemory {
                memories: HashSet::new(),
            }),
            children: vec![Box::new(child)],
        };
        let mut root = ConstantTestNode {
            test: Some(AbstractWME {
                ident: Variable {
                    identifier: "_".to_string(),
                },
                attr: AbstractAttribute::Variable(Variable {
                    identifier: "_".to_string(),
                }),
                value: AbstractValue::Variable(Variable {
                    identifier: "_".to_string(),
                }),
            }),
            output_memory: Some(AlphaMemory {
                memories: HashSet::new(),
            }),
            children: vec![Box::new(child)],
        };
        dbg!(&root);

        let test_wme = ConcreteWME {
            ident: EntityId(0),
            attr: "yote".to_string(),
            value: ConcreteValue::Literal(Literal::Number(1)),
        };
        let test_wme2 = ConcreteWME {
            ident: EntityId(1),
            attr: "yete".to_string(),
            value: ConcreteValue::Literal(Literal::Number(1)),
        };
        let test_wme3 = ConcreteWME {
            ident: EntityId(2),
            attr: "yete".to_string(),
            value: ConcreteValue::Literal(Literal::Number(2)),
        };

        dbg!(&test_wme);

        root.activate(test_wme);
        root.activate(test_wme2);
        root.activate(test_wme3);

        dbg!(&root);
    }
}
