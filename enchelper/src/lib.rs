use std::collections::HashMap;
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
        AstNode::AAQuantifier{identifier: _, form: _} |
        AstNode::AEQuantifier{identifier: _, form: _} => false,
        _ => true
    }
}

pub fn is_ahltl(formula: &AstNode) -> bool {
    !is_hltl(formula)
}

pub fn get_path_identifiers(formula: &AstNode) -> Vec<&str> {
    match formula {
        AstNode::HAQuantifier{identifier, form} |
        AstNode::HEQuantifier{identifier, form} => {
            // Recursively find inner paths.
            let mut path_list = get_path_identifiers(form);
            // The result is reversed, so we reverse it again
            path_list.reverse();
            // Update the list with the current identifier
            path_list.push(identifier);
            // Reverse the result
            path_list.reverse();
            // Return the result
            path_list
            
        }
        _ => Vec::<&str>::new()
    }
}

pub fn get_traj_identifiers(formula: &AstNode) -> Vec<&str> {
    match formula {
        AstNode::AAQuantifier{identifier, form} |
        AstNode::AEQuantifier{identifier, form} => {
            // Recursively find inner paths.
            let mut traj_list = get_traj_identifiers(form);
            // The result is reversed, so we reverse it again
            traj_list.reverse();
            // Update the list with the current identifier
            traj_list.push(identifier);
            // Reverse the result
            traj_list.reverse();
            // Return the result
            traj_list
        }
        AstNode::HAQuantifier{identifier:_, form} |
        AstNode::HEQuantifier{identifier:_, form} => get_traj_identifiers(form),
        _ => Vec::<&str>::new()
    }
}