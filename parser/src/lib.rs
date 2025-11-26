use pest::Parser;
use pest_derive::Parser;
use pest::error::Error;

#[derive(Parser)]
#[grammar = "grammar.pest"]
pub struct FormulaParser;

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum BinOperator {
    Equality,
    Conjunction,
    Disjunction,
    Implication,
    Until,
    Release,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum UnaryOperator {
    Negation,
    Globally,
    Eventually,
    Next,
}

#[derive(PartialEq, Eq, Debug, Clone, Hash)]
pub enum TraceType {
    Arbitrary,
    UserType(String),
    IntroducedType(usize),
}

#[derive(PartialEq, Debug, Clone)]
pub enum AstNode {
    HAQuantifier {
        identifier: String,
        trace_type: TraceType,
        form: Box<AstNode>,
    },
    HEQuantifier {
        identifier: String,
        trace_type: TraceType,
        form: Box<AstNode>,
    },
    AAQuantifier {
        identifier: String,
        form: Box<AstNode>,
    },
    AEQuantifier {
        identifier: String,
        form: Box<AstNode>,
    },
    BinOp {
        operator: BinOperator,
        lhs: Box<AstNode>,
        rhs: Box<AstNode>,
    },
    UnOp {
        operator: UnaryOperator,
        operand: Box<AstNode>,
    },
    HIndexedProp {
        proposition: String,
        path_identifier: String,
    },
    AIndexedProp {
        proposition: String,
        path_identifier: String,
        traj_identifier: String,
    },
    Constant {
        value: String,
    }
}

pub fn parse(source: &str) -> Result<AstNode, Error<Rule>> {
    // Get Pair for 'formula'
    let pair = FormulaParser::parse(Rule::formula, source)
        .expect("Can not parse source file")
        .next().unwrap();
    
    // Parse the formula
    Ok(build_ast_from_form_rec(pair.into_inner().next().unwrap()))
}

fn build_ast_from_form_rec(body_pair: pest::iterators::Pair<Rule>) -> AstNode {
    match body_pair.as_rule() {
        Rule::path_formula => build_ast_from_path(body_pair),
        Rule::traj_formula => build_ast_from_traj(body_pair),
        Rule::inner_hltl => build_ast_from_inner_ltl(body_pair.into_inner().next().unwrap()),
        _ => unreachable!(),
    }
}

fn build_ast_from_path(pair: pest::iterators::Pair<Rule>) -> AstNode {
    // Extract the iterator for ident and the body
    let mut pairs = pair.clone().into_inner();

    // Extract the identifier name and the body of the formula
    let identifier = pairs.next().unwrap();
    let body_or_type = pairs.next().unwrap();
    let (trace_type, body) = if let Some(body) = pairs.next() {
        (TraceType::UserType(body_or_type.as_str().to_string()), body)
    } else {
        (TraceType::Arbitrary, body_or_type)
    };
    
    // What type of formula is the body? Get its corresponding AST
    let body_ast = build_ast_from_form_rec(body.into_inner().next().unwrap());
    
    // Identify Quantifier type and build final AST
    match &pair.as_str()[..1] {
        "F" => AstNode::HAQuantifier {
                identifier: String::from(identifier.as_str()),
                trace_type,
                form: Box::new(body_ast),
            },
        _ => AstNode::HEQuantifier {
                identifier: String::from(identifier.as_str()),
                trace_type,
                form: Box::new(body_ast),
            }
    }
}


fn build_ast_from_traj(pair: pest::iterators::Pair<Rule>) -> AstNode {
    // Extract the iterator for ident and the body
    let mut pairs = pair.clone().into_inner();

    // Extract the identifier name and the body of the formula
    let identifier = pairs.next().unwrap();
    let body = pairs.next().unwrap();
    
    // What type of formula is the body? Get its corresponding AST
    let body_pair = body.into_inner().next().unwrap();
    let body_ast = match body_pair.as_rule() {
        Rule::traj_formula => build_ast_from_traj(body_pair),
        Rule::inner_altl => build_ast_from_inner_ltl(body_pair.into_inner().next().unwrap()),
        _ => unreachable!(),
    };
    
    // Identify Quantifier type and build final AST
    match &pair.as_str()[..1] {
        "A" => AstNode::AAQuantifier {
                identifier: String::from(identifier.as_str()),
                form: Box::new(body_ast),
            },
        _ => AstNode::AEQuantifier {
                identifier: String::from(identifier.as_str()),
                form: Box::new(body_ast),
            }
    }
}

fn build_ast_from_inner_ltl(pair: pest::iterators::Pair<Rule>) -> AstNode {
    // We always reach here with an 'hequal/aequal' node in the parser. Skip it.
    let mut pairs = pair.into_inner();

    // Check the length of the iterator
    match pairs.len() {
        1 => build_ast_from_impl(pairs.next().unwrap()),
        2 => {
            let lhs = pairs.next().unwrap(); // This is impl
            let lhs_ast = build_ast_from_impl(lhs);
            let rhs = pairs.next().unwrap(); // This is equal
            let rhs_ast = build_ast_from_inner_ltl(rhs);
            AstNode::BinOp {
                operator: BinOperator::Equality,
                lhs: Box::new(lhs_ast),
                rhs: Box::new(rhs_ast),
            }
        },
        _ => unreachable!(),
    }
}

fn build_ast_from_impl(pair: pest::iterators::Pair<Rule>) -> AstNode {
    // We always reach here with an 'himpl/aimpl' node in the parser. Skip it.
    let mut pairs = pair.into_inner();

    // Check the length of the iterator
    match pairs.len() {
        1 => build_ast_from_disj(pairs.next().unwrap()),
        2 => {
            let lhs = pairs.next().unwrap(); // This is disj
            let lhs_ast = build_ast_from_disj(lhs);
            let rhs = pairs.next().unwrap(); // This is impl
            let rhs_ast = build_ast_from_impl(rhs);
            AstNode::BinOp {
                operator: BinOperator::Implication,
                lhs: Box::new(lhs_ast),
                rhs: Box::new(rhs_ast),
            }
        },
        _ => unreachable!(),
    }
}

fn build_ast_from_disj(pair: pest::iterators::Pair<Rule>) -> AstNode {
    // We always reach here with an 'hdisj/adisj' node in the parser. Skip it.
    let mut pairs = pair.into_inner();

    // Check the length of the iterator
    match pairs.len() {
        1 => build_ast_from_conj(pairs.next().unwrap()),
        2 => {
            let lhs = pairs.next().unwrap(); // This is conj
            let lhs_ast = build_ast_from_conj(lhs);
            let rhs = pairs.next().unwrap(); // This is disj
            let rhs_ast = build_ast_from_disj(rhs);
            AstNode::BinOp {
                operator: BinOperator::Disjunction,
                lhs: Box::new(lhs_ast),
                rhs: Box::new(rhs_ast),
            }
        },
        _ => unreachable!(),
    }
}

fn build_ast_from_conj(pair: pest::iterators::Pair<Rule>) -> AstNode {
    // We always reach here with an 'hconj/aconj' node in the parser. Skip it.
    let mut pairs = pair.into_inner();

    // Check the length of the iterator
    match pairs.len() {
        1 => build_ast_from_until(pairs.next().unwrap()),
        2 => {
            let lhs = pairs.next().unwrap(); // This is factor
            let lhs_ast = build_ast_from_until(lhs);
            let rhs = pairs.next().unwrap(); // This is conj
            let rhs_ast = build_ast_from_conj(rhs);
            AstNode::BinOp {
                operator: BinOperator::Conjunction,
                lhs: Box::new(lhs_ast),
                rhs: Box::new(rhs_ast),
            }
        },
        _ => unreachable!(),
    }
}

fn build_ast_from_until(pair: pest::iterators::Pair<Rule>) -> AstNode {
    // We always reach here with an 'hconj/aconj' node in the parser. Skip it.
    let mut pairs = pair.into_inner();

    // Check the length of the iterator
    match pairs.len() {
        1 => build_ast_from_release(pairs.next().unwrap()),
        2 => {
            let lhs = pairs.next().unwrap(); // This is factor
            let lhs_ast = build_ast_from_release(lhs);
            let rhs = pairs.next().unwrap(); // This is conj
            let rhs_ast = build_ast_from_until(rhs);
            AstNode::BinOp {
                operator: BinOperator::Until,
                lhs: Box::new(lhs_ast),
                rhs: Box::new(rhs_ast),
            }
        },
        _ => unreachable!(),
    }
}

fn build_ast_from_release(pair: pest::iterators::Pair<Rule>) -> AstNode {
    // We always reach here with an 'hconj/aconj' node in the parser. Skip it.
    let mut pairs = pair.into_inner();

    // Check the length of the iterator
    match pairs.len() {
        1 => build_ast_from_factor(pairs.next().unwrap()),
        2 => {
            let lhs = pairs.next().unwrap(); // This is factor
            let lhs_ast = build_ast_from_factor(lhs);
            let rhs = pairs.next().unwrap(); // This is conj
            let rhs_ast = build_ast_from_release(rhs);
            AstNode::BinOp {
                operator: BinOperator::Release,
                lhs: Box::new(lhs_ast),
                rhs: Box::new(rhs_ast),
            }
        },
        _ => unreachable!(),
    }
}



fn build_ast_from_factor(pair: pest::iterators::Pair<Rule>) -> AstNode {
    // We always reach here with an 'hfactor/afactor' node in the parser. Skip it.
    let mut pairs = pair.into_inner();

    // Check the length of the iterator
    match pairs.len() {
        1 => {
            // It's either a parenthesized expression or an atom
            let inner_item = pairs.next().unwrap();
            match inner_item.as_rule() {
                Rule::form_rec  => build_ast_from_form_rec(inner_item.into_inner().next().unwrap()),
                Rule::inner_hltl | Rule::inner_altl => build_ast_from_inner_ltl(inner_item.into_inner().next().unwrap()),
                Rule::hltl_atom => build_ast_from_hprop(inner_item),
                Rule::altl_atom => build_ast_from_aprop(inner_item),
                _ => unreachable!()
            }
        },
        2 => {
            // It's a unary operator
            let op = pairs.next().unwrap();
            let factor = pairs.next().unwrap();

            // Match the operator
            let operator = match op.as_str() {
                "~" => UnaryOperator::Negation,
                "G" => UnaryOperator::Globally,
                "F" => UnaryOperator::Eventually,
                "X" => UnaryOperator::Next,
                _ => unreachable!()
            };

            AstNode::UnOp {
                operator: operator,
                operand: Box::new(build_ast_from_factor(factor)),
            }
        },
        _ => unreachable!(),
    }
}

fn build_ast_from_hprop(pair: pest::iterators::Pair<Rule>) -> AstNode {
    // We always reach here with an 'hltl-atom' node in the parser. Skip it.
    let mut pairs = pair.into_inner();

    // Its either a constant or a proposition
    // We need to peek inside to find out.
    let inner = pairs.next().unwrap();

    match inner.as_rule() {
        Rule::constant => AstNode::Constant{value: String::from(inner.as_str())},
        Rule::number => AstNode::Constant{value: String::from(inner.as_str())},
        Rule::ident => {
            let path = pairs.next().unwrap();
            AstNode::HIndexedProp {
                proposition: String::from(inner.as_str()),
                path_identifier: String::from(path.as_str()),
}
        }
        _ => unreachable!(),
    }
}

fn build_ast_from_aprop(pair: pest::iterators::Pair<Rule>) -> AstNode {
    // We always reach here with an 'altl-atom' node in the parser. Skip it.
    let mut pairs = pair.into_inner();

    // Its either a constant or a proposition
    // We need to peek inside to find out.
    let inner = pairs.next().unwrap();

    match inner.as_rule() {
        Rule::constant => AstNode::Constant{value: String::from(inner.as_str())},
        Rule::number => AstNode::Constant{value: String::from(inner.as_str())},
        Rule::ident => {
            let path = pairs.next().unwrap();
            let traj = pairs.next().unwrap();
            AstNode::AIndexedProp {
                proposition: String::from(inner.as_str()),
                path_identifier: String::from(path.as_str()),
                traj_identifier: String::from(traj.as_str()),
            }
        }
        _ => unreachable!(),
    }
}


#[test]
fn test_parsing() {
    let implies = |l,r|  AstNode::BinOp { operator: BinOperator::Implication, lhs: Box::new(l), rhs: Box::new(r), };
    let eq = |l,r|  AstNode::BinOp { operator: BinOperator::Equality, lhs: Box::new(l), rhs: Box::new(r), };
    let and = |l,r|  AstNode::BinOp { operator: BinOperator::Conjunction, lhs: Box::new(l), rhs: Box::new(r), };
    let not = |f|  AstNode::UnOp { operator: UnaryOperator::Negation, operand: Box::new(f), };
    #[allow(non_snake_case)]
    let G = |f|  AstNode::UnOp { operator: UnaryOperator::Globally, operand: Box::new(f), };
    let forall = |x: &str,f|  AstNode::HAQuantifier { identifier: x.to_string(), trace_type: TraceType::Arbitrary, form: Box::new(f) };
    let exists = |x: &str,f|  AstNode::HEQuantifier { identifier: x.to_string(), trace_type: TraceType::Arbitrary, form: Box::new(f) };
    let p = |x: &str| AstNode::HIndexedProp { proposition: "p".to_string(), path_identifier: x.to_string() };
    let q = |x: &str| AstNode::HIndexedProp { proposition: "q".to_string(), path_identifier: x.to_string() };

    assert_eq!(Ok(implies(
                forall("x", p("x")) ,
                exists("x", p("x")) ,
        )),
        parse("(Forall x . p[x]) -> (Exists x . p[x])"));

    assert_eq!(Ok(and(not(p("x")), p("y"))),
        parse("~p[x] & p[y]"));


    assert_eq!(Ok(forall("x", not(and(eq(p("x"), p("y")), not(eq(q("x"), q("y"))))))),
        parse("Forall x . ~((p[x] = p[y]) & ~(q[x] = q[y]))"));

    assert_eq!(Ok(and(G(p("x")), G(p("z")))),
        parse("G p[x] &  G p[z]"));

}
