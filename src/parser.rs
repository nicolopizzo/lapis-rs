use std::{collections::HashMap, rc::Rc};

use dedukti_parse::{
    term::{App, AppH},
    Command, Intro, Strict, Symb,
};

use crate::lnode::LNode;

type Term<'a> = dedukti_parse::Term<Symb<&'a str>, &'a str>;
type Result<T> = std::result::Result<T, String>;
type ParseResult<'a, T> = std::result::Result<Vec<T>, dedukti_parse::Error>;

fn map_to_node(
    gamma: &mut HashMap<String, Rc<LNode>>,
    app: App<AppH<Symb<&str>, &str>>,
) -> Option<Rc<LNode>> {
    let head = match app.head {
        AppH::Atom(sym) => {
            if sym.name == "Type" {
                Some(Rc::new(LNode::new_var(None)))
            } else {
                gamma.get(sym.name).map(|t| t.clone())
            }
        }
        AppH::Abst(x, t, body) => {
            let body = map_to_node(gamma, body.as_ref().clone()).unwrap();
            // bind x to t in gamma
            let t = t.map(|x| map_to_node(gamma, x.as_ref().clone()).unwrap());
            if let Some(t) = t {
                gamma.insert(x.to_owned(), t);
            }

            Some(Rc::new(LNode::new_abs(body)))
        }
        AppH::Prod(x, a, t) => {
            let l = map_to_node(gamma, a.as_ref().clone()).unwrap();
            // TODO: bind x to l in gamma if the product is named?
            if let Some(x) = x {
                //TODO: If there is no need to memorize the variable name, can do this?
                // let l = LNode::new_var(Some(l));

                gamma.insert(x.to_string(), l.clone());
            }

            let r = map_to_node(gamma, t.as_ref().clone()).unwrap();

            let node = Rc::new(LNode::new_app(l.clone(), r.clone()));

            l.add_parent(node.clone());
            r.add_parent(node.clone());

            Some(node)
        }
    };

    let mut res = head;
    // Apply all the arguments to the head node (left application)
    for arg in app.args {
        let t = map_to_node(gamma, arg).unwrap();
        res = Some(Rc::new(LNode::new_app(res.unwrap(), t)));
    }

    res
}

pub fn parse(cmds: String) -> HashMap<String, Rc<LNode>> {
    let parse: ParseResult<_> = Strict::<_, Symb<&str>, &str>::new(&cmds).collect();
    let parse = parse.unwrap();

    let mut gamma = HashMap::new();
    let mut rules = Vec::new();
    for cmd in parse {
        match cmd {
            Command::Intro(name, _path, f) => match f {
                Intro::Declaration(x) => {
                    let t = map_to_node(&mut gamma, x);
                    let node = Rc::new(LNode::new_var(t));

                    gamma.insert(name.to_string(), node);
                }
                Intro::Definition(x, y) => {
                    if let Some(x) = x {
                        let t = map_to_node(&mut gamma, x);
                        let node = Rc::new(LNode::new_var(t));

                        gamma.insert(name.to_string(), node);

                        // If a definition has a type, you can simply memorize its snf type (?).
                        continue;
                    }

                    if let Some(y) = y {
                        let t = map_to_node(&mut gamma, y);
                        let node = Rc::new(LNode::new_var(t));

                        gamma.insert(name.to_string(), node);
                    }
                }
                Intro::Theorem(_, _) => todo!(),
            },
            Command::Rules(r) => rules.append(&mut r.clone()),
        }
    }

    gamma
}

#[test]
fn test_parse() {
    let cmds = r#"
        Nat: Type.
        zero: Nat.
        def S: Nat -> Nat.
        def one := S (S zero).
        def plus: Nat -> Nat -> Nat.
        [n: Nat] plus zero n --> n.
        [m: Nat,n : Nat] plus (S m) n --> S (plus m n).
        "#;

    let gamma = parse(cmds.to_string());

    let nat = gamma.get("Nat").unwrap();
    let zero = gamma.get("zero").unwrap();
    let one = gamma.get("one").unwrap();
    let s = gamma.get("S").unwrap();
    let plus = gamma.get("plus").unwrap();

    // DEBUG
    // let parse: ParseResult<_> = Strict::<_, Symb<&str>, &str>::new(&cmds).collect();
    // let parse = parse.unwrap();

    assert_eq!(zero.get_type().unwrap(), *nat);
    // println!("{:#?}", plus);
    assert_ne!(one.get_type().unwrap(), *s);
}
