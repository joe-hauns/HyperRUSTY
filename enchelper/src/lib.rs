use std::collections::HashMap;
use ir::*;
use parser::{
    UnaryOperator, BinOperator,
    AstNode,
};

#[derive(Debug, Clone)]
pub enum Semantics {
    Pes,
    Opt,
    Hpes,
    HOpt,
}

// Creates a mapping of the quantified path variables to their corresponding
// index in the state set.
pub fn create_path_mapping(formula: &AstNode, k: usize) -> HashMap<&str, usize> {
    let mut mapping = HashMap::<&str, usize>::new();
    match formula {
        AstNode::HAQuantifier{identifier, form} |
        AstNode::HEQuantifier{identifier, form} => {
            // Recursively map inner quantifiers.
            mapping.extend(create_path_mapping(form, k + 1));
            // Update mapping
            mapping.insert(identifier, k);
            // Return the result
            mapping
        }
        _ => mapping
    }
}

pub fn inner_ltl(formula: &AstNode) -> &AstNode {
    match formula {
        AstNode::HAQuantifier{identifier: _, form} |
        AstNode::HEQuantifier{identifier: _, form} |
        AstNode::AAQuantifier{identifier: _, form} |
        AstNode::AEQuantifier{identifier: _, form} => {
            inner_ltl(form)
        }
        _ => formula
    }
}

pub fn is_hltl(formula: &AstNode) -> bool {
    match formula {
        AstNode::HAQuantifier{identifier: _, form} |
        AstNode::HEQuantifier{identifier: _, form} => is_hltl(form),
        AstNode::AAQuantifier{identifier: _, form} |
        AstNode::AEQuantifier{identifier: _, form} => false,
        _ => true
    }
}

pub fn is_ahltl(formula: &AstNode) -> bool {
    !is_hltl(formula)
}