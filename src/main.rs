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
struct CSVParser;

fn process_variable(pair: Pair<Rule>) -> Symbol {
    let mut inner: Pairs<Rule> = pair.into_inner(); // we know this is a variable
    let contents = inner.next().unwrap();
    match contents.clone().as_rule() {
        Rule::generic => Symbol::Id(
            contents
                .into_inner()
                .next()
                .unwrap()
                .as_span()
                .as_str()
                .to_string(),
        ),
        _ => panic!(),
    }
}

fn process_attr(pair: Pair<Rule>) -> Symbol {
    let mut inner: Pairs<Rule> = pair.into_inner();
    let contents = inner.next().unwrap();
    match contents.clone().as_rule() {
        Rule::generic => Symbol::Id(
            contents
                .into_inner()
                .next()
                .unwrap()
                .as_span()
                .as_str()
                .to_string(),
        ),
        _ => Symbol::Text(contents.as_span().as_str().to_string()),
    }
    // AbstractAttribute::Literal("WOO".to_string())
}

fn process_value(pair: Pair<Rule>) -> Symbol {
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
                    // chars.next();
                    // chars.next_back();
                    let string = chars.as_str().to_string();
                    (Symbol::Text(string))
                }
                _ => {
                    panic!()
                }
            }
        }
        Rule::var => (process_variable(contents)),
        _ => {
            panic!()
        }
    }
}

fn process_wme(pair: Pair<Rule>) -> Pattern {
    // "Safe" to assume pair IS a WME
    let mut inner: Pairs<Rule> = pair.into_inner();
    let ident = process_variable(inner.next().unwrap());
    let attr = process_attr(inner.next().unwrap());
    let value = process_value(inner.next().unwrap());

    Pattern(ident, attr, value)
}

fn process_block(pair: Pair<Rule>) -> Vec<Pattern> {
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
    Prod(process_block(lhs), process_block(rhs))
}

#[derive(Debug)]
struct Prod(Vec<Pattern>, Vec<Pattern>);

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

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
enum Symbol {
    Id(String),
    Text(String),
}

impl Symbol {
    fn blank() -> Self {
        Symbol::Id("_".to_string())
    }

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
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct Memory(String, String, String);

// Symbol is generics OR literals for matching
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
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

    fn wme_match(&self, other: WME) -> (bool, bool, bool) {
        // Match against the concrete where its not variables
        (
            if let Symbol::Text(t) = self.0.clone() {
                t == other.0 .0
            } else {
                true
            },
            if let Symbol::Text(t) = self.1.clone() {
                t == other.0 .1
            } else {
                true
            },
            if let Symbol::Text(t) = self.2.clone() {
                t == other.0 .2
            } else {
                true
            },
        )
    }
}

// WME is a memory and its pattern
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct WME(Memory, Pattern);

impl WME {
    fn from(a: &str, b: &str, c: &str) -> WME {
        WME(
            Memory(a.to_string(), b.to_string(), c.to_string()),
            Pattern(Symbol::blank(), Symbol::blank(), Symbol::blank()),
        )
    }
}

// Alpha Store, universal pattern for all WMEs
#[derive(PartialEq, Eq, Clone, Debug)]
struct AlphaNode(HashSet<WME>, Pattern);

impl AlphaNode {
    fn activate(&mut self, wme: WME) {
        self.0.insert(wme);
    }
}

// Scope maps Symbol ids to values
// Literals are not included (only for pattern matching)
// This maps a Symbol::Id to Text
#[derive(PartialEq, Eq, Clone, Debug)]
struct Scope(HashMap<String, String>);

fn join(mut alphas: Vec<AlphaNode>) -> Vec<Scope> {
    if alphas.len() == 1 {
        let mut maps = Vec::<HashMap<String, String>>::new();
        let pattern: Pattern = alphas[0].1.clone();
        for wme in alphas[0].0.iter() {
            let mut map = HashMap::new();
            if let Symbol::Id(id) = pattern.0.clone() {
                map.insert(id, wme.0 .0.clone());
            };
            if let Symbol::Id(id) = pattern.1.clone() {
                map.insert(id, wme.0 .1.clone());
            };
            if let Symbol::Id(id) = pattern.2.clone() {
                map.insert(id, wme.0 .2.clone());
            };
            maps.push(map);
        }
        return maps.iter().map(|x| Scope(x.clone())).collect();
    } else {
        let alpha = alphas.pop().unwrap();
        let scopes = join(alphas);
        let mut new_scopes = Vec::new();
        let pattern: Pattern = alpha.1.clone();
        for wme in alpha.0.iter() {
            'mid: for scope in scopes.clone() {
                let mut mini_scope: Scope = scope.clone();
                for (symbol, val) in vec![pattern.0.clone(), pattern.1.clone(), pattern.2.clone()]
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

fn find_alpha(alphas: &mut Vec<AlphaNode>, pattern: Pattern) -> Option<&mut AlphaNode> {
    for alpha in alphas {
        if alpha.1.pattern_match(&pattern) == (true, true, true) {
            return Some(alpha);
        }
    }
    return None;
}

fn activate(alphas: &mut Vec<AlphaNode>, element: WME) {
    // Doesnt already exist!
    let mut nohit = true;

    // If this already exists (id and attr) with a different value, clear it
    for alpha in &mut *alphas {
        if alpha.1.wme_match(element.clone()) == (true, true, false)
            || alpha.1.wme_match(element.clone()) == (true, true, true)
        {
            // We are in a WME that COULD store this same attribute
            // Thus, we want to nuke it
            alpha.0 = alpha
                .0
                .iter()
                .filter(|&e| !(e.0 .0 == element.0 .0 && e.0 .1 == element.0 .1))
                .cloned()
                .collect();
        }
    }

    for alpha in alphas {
        if alpha.1.wme_match(element.clone()) == (true, true, true) {
            alpha.0.insert(element.clone());
            nohit = false;
        }
    }
    // Add a new alpha memory, this is clearly new!
    if nohit {}
}

fn main() {
    let unparsed_file = fs::read_to_string("script").expect("cannot read file");

    let file = CSVParser::parse(Rule::file, &unparsed_file)
        .expect("Unsuccessful parse")
        .next()
        .unwrap();

    let out = process_file(file);
    let mut root = Vec::<AlphaNode>::new();

    // Ensure all the alpha nodes exist!
    for prod in &out {
        'mid: for pattern in prod.0.clone() {
            for alpha in &root {
                if alpha.1.pattern_match(&pattern) == (true, true, true) {
                    continue 'mid;
                }
            }
            // Doesnt already exist!
            root.push(AlphaNode(HashSet::new(), pattern.clone()));
        }
        'mid: for pattern in prod.1.clone() {
            for alpha in &root {
                if alpha.1.pattern_match(&pattern) == (true, true, true) {
                    continue 'mid;
                }
            }
            // Doesnt already exist!
            root.push(AlphaNode(HashSet::new(), pattern.clone()));
        }
    }
    // root.push(AlphaNode(
    //     HashSet::new(),
    //     Pattern(
    //         Symbol::Id("io".to_string()),
    //         Symbol::Text("print".to_string()),
    //         Symbol::Id("out".to_string()),
    //     ),
    // ));
    root.push(AlphaNode(
        HashSet::new(),
        Pattern(
            Symbol::Id("io".to_string()),
            Symbol::Text("doread".to_string()),
            Symbol::Text("true".to_string()),
        ),
    ));
    let mut fresh_id: usize = 10;

    activate(&mut root, WME::from("time", "std", "timekeeper"));
    activate(&mut root, WME::from("time", "init", "true"));
    activate(&mut root, WME::from("io", "std", "IO"));
    activate(&mut root, WME::from("io", "print", ""));
    activate(&mut root, WME::from("io", "doread", ""));
    activate(&mut root, WME::from("io", "read", ""));

    // Main Loop
    loop {
        let mut changes = Vec::new();
        for prod in &out {
            let mut alphas = Vec::new();
            for pattern in prod.0.clone() {
                if let Some(alpha) = find_alpha(&mut root, pattern) {
                    alphas.push(alpha.clone());
                }
            }
            let joins = join(alphas.clone());
            for join in joins {
                for rhs in prod.1.clone() {
                    let mut memory = Memory(fresh_id.to_string(), "".to_string(), "".to_string());
                    if let Symbol::Id(id) = rhs.0.clone() {
                        if let Some(val) = join.0.get(&id) {
                            memory.0 = val.clone();
                        }
                    };
                    if let Symbol::Id(id) = rhs.1.clone() {
                        if let Some(val) = join.0.get(&id) {
                            memory.1 = val.clone();
                        }
                    };
                    if let Symbol::Text(text) = rhs.1.clone() {
                        memory.1 = text;
                    }
                    if let Symbol::Id(id) = rhs.2.clone() {
                        if let Some(val) = join.0.get(&id) {
                            memory.2 = val.clone();
                        }
                    };
                    if let Symbol::Text(text) = rhs.2.clone() {
                        memory.2 = text;
                    }
                    changes.push(memory);
                }
            }
        }
        for change in changes {
            activate(&mut root, WME::from(&change.0, &change.1, &change.2));
        }
        // Do IO?
        let io = find_alpha(
            &mut root,
            Pattern(
                Symbol::Id("IO".to_string()),
                Symbol::Text("print".to_string()),
                Symbol::Id("_".to_string()),
            ),
        );
        if let Some(io) = &io {
            let out = io.0.iter().next().unwrap().0 .2.clone();
            if out != "" {
                println!("{}", out);
            }
        };

        let read = find_alpha(
            &mut root,
            Pattern(
                Symbol::Id("IO".to_string()),
                Symbol::Text("doread".to_string()),
                Symbol::Text("true".to_string()),
            ),
        );
        // println!("----------");
        if let Some(read) = &read {
            // dbg!(&read);
            if read.0.len() != 0 {
                use std::io::{stdin, stdout, Write};
                let mut s = String::new();
                print!("Please enter some text: ");
                let _ = stdout().flush();
                stdin()
                    .read_line(&mut s)
                    .expect("Did not enter a correct string");
                let s = s.trim();
                activate(&mut root, WME::from("io", "read", &s));
                activate(&mut root, WME::from("io", "doread", "false"));
            }
        }

        let timekeeper = find_alpha(
            &mut root,
            Pattern(
                Symbol::Id("TIME".to_string()),
                Symbol::Text("init".to_string()),
                Symbol::Text("true".to_string()),
            ),
        );
        if let Some(timekeeper) = &timekeeper {
            activate(&mut root, WME::from("time", "init", "false"));
        }
        // dbg!(&io);
        // dbg!(root.clone());
    }
}
