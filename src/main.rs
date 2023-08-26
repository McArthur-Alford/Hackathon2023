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

#[derive(PartialEq, Eq, Hash, Clone)]
enum Symbol {
    Id(String),
    Text(String),
}

impl Symbol {
    fn symbol_eq(&self, other: &Self) -> bool {
        if let Symbol::Text(str) = self {
            if let Symbol::Text(str2) = other {
                if str == str2 {
                    return true;
                }
            }
        }
        if let Symbol::Id(_) = self {
            if let Symbol::Id(_) = other {
                return true;
            }
        }
        return false;
    }
}

// Id, Attr, Text
#[derive(PartialEq, Eq, Hash, Clone)]
struct Memory(String, String, String);

// Symbol is generics OR literals for matching
#[derive(PartialEq, Eq, Hash, Clone)]
struct Pattern(Symbol, Symbol, Symbol);

impl Pattern {
    fn pattern_match(&self, other: &Self) -> (bool, bool, bool) {
        let mut out = (false, false, false);
        out = (
            self.0.symbol_eq(&other.0),
            self.1.symbol_eq(&other.1),
            self.2.symbol_eq(&other.2),
        );
        out
    }
}

// WME is a memory and its pattern
#[derive(PartialEq, Eq, Hash, Clone)]
struct WME(Memory, Pattern);

// Alpha Store, universal pattern for all WMEs
#[derive(PartialEq, Eq, Clone)]
struct AlphaNode(HashSet<WME>);

impl AlphaNode {
    fn activate(&mut self, wme: WME) {
        self.0.insert(wme);
    }
}

// Scope maps Symbol ids to values
// Literals are not included (only for pattern matching)
// This maps a Symbol::Id to Text
#[derive(PartialEq, Eq, Clone)]
struct Scope(HashMap<String, String>);

struct Node {
    guard: Pattern,
    children: Vec<Box<Node>>,
    alpha: AlphaNode,
}

impl Node {
    fn activate(&mut self, wme: WME) {
        let pmr = self.guard.pattern_match(&wme.1);
        if pmr == (true, true, true) {
            self.alpha.activate(wme.clone());
        } else {
            for child in &mut self.children {
                child.activate(wme.clone());
            }
        }
    }

    fn find_alpha(&mut self, pattern: Pattern) -> Option<AlphaNode> {
        for elem in self.alpha.0.iter() {
            if elem.1.pattern_match(&pattern) == (true, true, true) {
                return Some(self.alpha.clone());
            } else {
                break;
            }
        }
        for child in &mut self.children {
            let out = child.find_alpha(pattern.clone());
            if out != None {
                return out;
            }
        }
        None
    }

    fn add_pattern(&mut self, pattern: Pattern) -> bool {
        let pmr = self.guard.pattern_match(&pattern);
        match pmr {
            (true, true, true) => {
                return true;
            }
            (true, true, false) => {
                for child in &mut self.children {
                    if child.add_pattern(pattern.clone()) {
                        return true;
                    }
                }
                self.children.push(Box::new(Node {
                    guard: pattern,
                    children: Vec::new(),
                    alpha: AlphaNode(HashSet::new()),
                }));
                return true;
            }
            _ => {
                for child in &mut self.children {
                    child.add_pattern(pattern.clone());
                }
                return true;
            }
        }
    }
}

fn join(mut alphas: Vec<AlphaNode>) -> Vec<Scope> {
    if alphas.len() == 1 {
        let mut maps = Vec::<HashMap<String, String>>::new();
        for wme in alphas[0].0.iter() {
            let mut map = HashMap::new();
            if let Symbol::Id(id) = wme.1 .0.clone() {
                map.insert(id, wme.0 .0.clone());
            };
            if let Symbol::Id(id) = wme.1 .1.clone() {
                map.insert(id, wme.0 .1.clone());
            };
            if let Symbol::Id(id) = wme.1 .2.clone() {
                map.insert(id, wme.0 .2.clone());
            };
            maps.push(map);
        }
        return maps.iter().map(|x| Scope(x.clone())).collect();
    } else {
        let alpha = alphas.pop().unwrap();
        let scopes = join(alphas);
        let mut new_scopes = Vec::new();
        for wme in alpha.0.iter() {
            'mid: for scope in scopes.clone() {
                let mut mini_scope: Scope = scope.clone();
                for (symbol, val) in vec![wme.1 .0.clone(), wme.1 .1.clone(), wme.1 .2.clone()]
                    .iter()
                    .zip(vec![wme.0 .0.clone(), wme.0 .1.clone(), wme.0 .2.clone()])
                {
                    if let Symbol::Id(id) = symbol {
                        // This is an id, we care
                        if let Some(existing) = mini_scope.0.get(id) {
                            if existing.clone() != val {
                                continue 'mid;
                            }
                        } else {
                            mini_scope.0.insert(id.clone(), val);
                        }
                    }
                }
                new_scopes.push(mini_scope);
            }
        }
        return new_scopes;
    }
}

fn process_file(f: Pair<Rule>) -> () {
    ()
}

fn main() {
    let unparsed_file = fs::read_to_string("script").expect("cannot read file");

    let file = CSVParser::parse(Rule::file, &unparsed_file)
        .expect("Unsuccessful parse")
        .next()
        .unwrap();

    let out = process_file(file);
}
