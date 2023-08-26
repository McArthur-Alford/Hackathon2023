use pest::{
    iterators::{Pair, Pairs},
    Parser,
};
use pest_derive::Parser;
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::rc::{Rc, Weak};

#[derive(Parser)]
#[grammar = "grammar.pest"]
pub struct CSVParser;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct Variable {
    identifier: String,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum Literal {
    Text(String),
    Number(i64),
    Bool(bool),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum AbstractAttribute {
    Literal(String),
    Variable(Variable),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum AbstractValue {
    Literal(Literal),
    Variable(Variable),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum ConcreteValue {
    Literal(Literal),
    Variable(EntityId),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
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

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct AbstractProd {
    precedence: usize,
    lhs: Vec<AbstractWME>,
    rhs: Vec<AbstractWME>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct EntityId(usize);

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct Production {
    abstract_production: AbstractProd,
}

#[derive(Debug)]
struct AlphaMemory {
    memories: HashSet<ConcreteWME>,
    downstream: HashSet<Join>,
}

impl AlphaMemory {
    fn activate(&mut self, cw: ConcreteWME, mode: ActivationMode) {
        // Add the cw into this alpha memory
        if mode == ActivationMode::Add {
            self.memories.insert(cw);
        } else {
            self.memories.remove(&cw);
        }
    }
}

#[derive(Debug, Clone)]
struct BetaNode {
    memories: Vec<JoinTable>,
    downstream: Vec<Rc<RefCell<Join>>>,
    productions: Vec<Rc<RefCell<Production>>>,
}

#[derive(Debug, Clone)]
struct Join {
    test: Option<Vec<AbstractWME>>,
    left_parent: Rc<BetaNode>,
    right_parent: Rc<AlphaMemory>,
    downstream: Vec<Rc<RefCell<BetaNode>>>, // A list of shared mutable references to all downstream nodes
}

#[derive(Debug, Clone)]
struct JoinTable(HashMap<String, JoinTableEntry>);

// Represents all possible values of any symbol in the join table
#[derive(Debug, Clone)]
enum JoinTableEntry {
    Variable(EntityId),
    Literal(Literal),
}

// Turns a concrete wme into a triplet of new join table entries
// Or returns none if its not possible
fn concrete_wme_into_jte(cw: ConcreteWME) -> (JoinTableEntry, JoinTableEntry, JoinTableEntry) {
    let id = cw.ident;
    let attr = Literal::Text(cw.attr); // Only String (this is nearly useless!)
    let value: ConcreteValue = cw.value; // Either Literal or EntityId
    let mut out = None;
    if let ConcreteValue::Literal(x) = value {
        out = Some(JoinTableEntry::Literal(x));
    } else if let ConcreteValue::Variable(x) = value {
        out = Some(JoinTableEntry::Variable(x));
    }
    let out = out.unwrap();
    (
        JoinTableEntry::Variable(id),
        JoinTableEntry::Literal(attr),
        out,
    )
}

impl Join {
    // Activates with a new element from the right
    fn activate_right(&mut self, cw: ConcreteWME, mode: ActivationMode) {
        let new_matches: Vec<ConcreteWME> = Vec::new();
        // Join the cw with every left hand match
        for left in Rc::try_unwrap(self.left_parent.clone()).unwrap().memories {
            // Going through each memory in the left parent!
        }
    }

    // Activates with a new match from the left
    fn activate_left(&mut self, cws: Vec<ConcreteWME>, mode: ActivationMode) {}
}

impl BetaNode {
    fn activate(&mut self, cws: Vec<ConcreteWME>, mode: ActivationMode) {}
}

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

fn compare_aa(wme1: AbstractWME, wme2: AbstractWME) -> (bool, bool) {
    // Is the attr the same, literally, or both a val
    let mut out = (false, false);
    if let AbstractAttribute::Literal(lit1) = wme1.attr.clone() {
        if let AbstractAttribute::Literal(lit2) = wme2.attr.clone() {
            if lit1 == lit2 {
                out = (true, out.1);
            }
        }
    }
    // Its a variable, so we match them regardless
    if matches!(wme1.attr.clone(), AbstractAttribute::Variable(x))
        && matches!(wme2.attr.clone(), AbstractAttribute::Variable(x))
    {
        out = (true, out.1);
    }
    // Ensure both literal values are the same
    if let AbstractValue::Literal(lit) = wme1.value.clone() {
        if let AbstractValue::Literal(lit2) = wme2.value.clone() {
            if lit == lit2 {
                out = (out.0, true);
            }
        }
    }
    // OR ensure they are both variables
    if matches!(wme1.value.clone(), AbstractValue::Variable(x))
        && matches!(wme2.value.clone(), AbstractValue::Variable(x))
    {
        out = (out.0, true);
    }
    out
}

fn compare_ac(wme1: AbstractWME, wme2: ConcreteWME) -> (bool, bool) {
    // Is the attr the same, literally, or both a val
    let mut out = (false, false);
    if let AbstractAttribute::Literal(text) = wme1.attr.clone() {
        if text == wme2.attr {
            // Same text value
            out = (true, out.1);
        }
    }
    // Its a variable, so we match them regardless
    if matches!(wme1.attr.clone(), AbstractAttribute::Variable(x)) {
        out = (true, out.1);
    }
    // Ensure both literal values are the same
    if let AbstractValue::Literal(lit) = wme1.value.clone() {
        if let ConcreteValue::Literal(lit2) = wme2.value.clone() {
            if lit == lit2 {
                out = (out.0, true);
            }
        }
    }
    // OR ensure they are both variables
    if matches!(wme1.value.clone(), AbstractValue::Variable(x))
        && matches!(wme2.value.clone(), ConcreteValue::Variable(x))
    {
        out = (out.0, true);
    }
    out
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
enum ActivationMode {
    Add,
    Delete,
}

impl ConstantTestNode {
    fn activate(&mut self, cw: ConcreteWME, mode: ActivationMode) {
        if let Some(test) = self.test.clone() {
            if pattern_match(cw.clone(), test) {
                // CW matched this constant test node pattern
                // Add it to any directly downstream alpha memory:
                if let Some(output_memory) = &mut self.output_memory {
                    output_memory.activate(cw.clone(), mode);
                }

                // Trigger all downstream concrete tests:
                for child in &mut self.children {
                    child.activate(cw.clone(), mode);
                }
            }
        } else {
            // CW matched this constant test node pattern
            // Add it to any directly downstream alpha memory:
            if let Some(output_memory) = &mut self.output_memory {
                output_memory.activate(cw.clone(), mode);
            }

            // Trigger all downstream concrete tests:
            for child in &mut self.children {
                child.activate(cw.clone(), mode);
            }
        }
    }

    // This should only be run on root
    // else everything in the world will crash & burn
    fn add_awme(&mut self, aw: AbstractWME) {
        self.add_awme_rec(aw, true);
    }

    fn add_abstract_production(&mut self, prod: Production) {
        let lhs = prod.abstract_production.lhs;
        for elem in lhs {
            self.add_awme_rec(elem, true);
        }
    }

    fn add_awme_rec(&mut self, aw: AbstractWME, at_attr: bool) {
        let aw_value_is_var = matches!(aw.value.clone(), AbstractValue::Variable(x));
        let aw_attr_is_var = matches!(aw.attr.clone(), AbstractAttribute::Variable(x));
        if aw_value_is_var && aw_attr_is_var {
            // In this case everything is already handled by the root node! Wohoo!
            return;
        }
        if !at_attr && aw_value_is_var {
            // We dont need to create anything in this case, however you would sure hope the parent has an
            // alpha memory ready!
            return;
        }
        for child in &mut self.children {
            if let Some(test) = child.test.clone() {
                let comparison = compare_aa(aw.clone(), test.clone());
                if comparison.0 && at_attr {
                    if aw_value_is_var {
                        // We dont need to create a child, but we can verify this has a alpha memory
                        if matches!(child.output_memory, None) {
                            child.output_memory = Some(AlphaMemory {
                                memories: HashSet::new(),
                                downstream: HashSet::new(),
                            });
                        }
                        return;
                    }
                    // We found a child which already matches this attr, so we will forward the work to it
                    child.add_awme_rec(aw, !at_attr);
                    return;
                }
                if comparison.1 && !at_attr {
                    // We found a child which already matches this value, so we dont need to do anything
                    return;
                }
            }
        }
        // No child was found already matching, so we can create one safely!
        if at_attr {
            let mut child = Box::new(ConstantTestNode {
                test: Some(AbstractWME {
                    ident: Variable {
                        identifier: "_".to_string(),
                    },
                    attr: if !aw_attr_is_var {
                        aw.attr.clone()
                    } else {
                        AbstractAttribute::Variable(Variable {
                            identifier: "_".to_string(),
                        })
                    },
                    value: AbstractValue::Variable(Variable {
                        identifier: "_".to_string(),
                    }),
                }),
                output_memory: if aw_value_is_var {
                    Some(AlphaMemory {
                        memories: HashSet::new(),
                        downstream: HashSet::new(),
                    })
                } else {
                    None
                },
                children: Vec::new(),
            });
            if !aw_value_is_var {
                // Make sure the subnode is prepared if necessary
                child.add_awme_rec(aw, !at_attr);
            }
            self.children.push(child);
        } else {
            let mut child = Box::new(ConstantTestNode {
                test: Some(AbstractWME {
                    ident: Variable {
                        identifier: "_".to_string(),
                    },
                    attr: if !aw_attr_is_var {
                        aw.attr.clone()
                    } else {
                        AbstractAttribute::Variable(Variable {
                            identifier: "_".to_string(),
                        })
                    },
                    value: if !aw_value_is_var {
                        aw.value.clone()
                    } else {
                        AbstractValue::Variable(Variable {
                            identifier: "_".to_string(),
                        })
                    },
                }),
                output_memory: Some(AlphaMemory {
                    memories: HashSet::new(),
                    downstream: HashSet::new(),
                }),
                children: Vec::new(),
            });
            self.children.push(child);
        }
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
            downstream: HashSet::new(),
        }),
        children: vec![],
    };

    for prod in out {
        root.add_abstract_production(Production {
            abstract_production: prod,
        });
    }
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
                downstream: HashSet::new(),
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
        root.add_awme(AbstractWME {
            ident: Variable {
                identifier: "x".to_string(),
            },
            attr: AbstractAttribute::Literal("yeet".to_string()),
            value: AbstractValue::Literal(Literal::Number(2)),
        });
        root.add_awme(AbstractWME {
            ident: Variable {
                identifier: "x".to_string(),
            },
            attr: AbstractAttribute::Literal("magic".to_string()),
            value: AbstractValue::Literal(Literal::Number(1)),
        });
        root.add_awme(AbstractWME {
            ident: Variable {
                identifier: "x".to_string(),
            },
            attr: AbstractAttribute::Literal("magic".to_string()),
            value: AbstractValue::Literal(Literal::Number(2)),
        });
        root.add_awme(AbstractWME {
            ident: Variable {
                identifier: "x".to_string(),
            },
            attr: AbstractAttribute::Literal("magic".to_string()),
            value: AbstractValue::Variable(Variable {
                identifier: "y".to_string(),
            }),
        });

        let test_wme1 = ConcreteWME {
            ident: EntityId(0),
            attr: "yeet".to_string(),
            value: ConcreteValue::Literal(Literal::Number(1)),
        };
        let test_wme2 = ConcreteWME {
            ident: EntityId(2),
            attr: "yeet".to_string(),
            value: ConcreteValue::Literal(Literal::Number(1)),
        };
        let test_wme3 = ConcreteWME {
            ident: EntityId(1),
            attr: "yeet".to_string(),
            value: ConcreteValue::Literal(Literal::Number(2)),
        };

        root.activate(test_wme1.clone(), ActivationMode::Add);
        root.activate(test_wme2.clone(), ActivationMode::Add);
        root.activate(test_wme3.clone(), ActivationMode::Add);

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
                downstream: HashSet::new(),
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
                downstream: HashSet::new(),
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
                downstream: HashSet::new(),
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

        root.activate(test_wme, ActivationMode::Add);
        root.activate(test_wme2, ActivationMode::Add);
        root.activate(test_wme3, ActivationMode::Add);

        dbg!(&root);
    }

    #[test]
    fn test_simple_remove() {
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
                downstream: HashSet::new(),
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
        root.add_awme(AbstractWME {
            ident: Variable {
                identifier: "x".to_string(),
            },
            attr: AbstractAttribute::Literal("yote".to_string()),
            value: AbstractValue::Literal(Literal::Number(2)),
        });
        root.add_awme(AbstractWME {
            ident: Variable {
                identifier: "x".to_string(),
            },
            attr: AbstractAttribute::Literal("yeet".to_string()),
            value: AbstractValue::Variable(Variable {
                identifier: "z".to_string(),
            }),
        });

        let test_wme1 = ConcreteWME {
            ident: EntityId(0),
            attr: "yeet".to_string(),
            value: ConcreteValue::Literal(Literal::Number(1)),
        };
        let test_wme2 = ConcreteWME {
            ident: EntityId(0),
            attr: "yote".to_string(),
            value: ConcreteValue::Literal(Literal::Number(2)),
        };

        root.activate(test_wme1.clone(), ActivationMode::Add);
        root.activate(test_wme2.clone(), ActivationMode::Add);
        dbg!(&root);

        root.activate(test_wme1.clone(), ActivationMode::Delete);
        dbg!(&root);
    }
}
