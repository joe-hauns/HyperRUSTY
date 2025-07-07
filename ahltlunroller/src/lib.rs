use std::collections::HashMap;
use ir::*;
use enchelper::{Semantics, create_path_mapping, inner_ltl};
use z3::{Context,
    ast::{
        Ast, Dynamic, Bool,
    }
};
use parser::{
    UnaryOperator, BinOperator,
    AstNode,
};

enum UnrollingReturn<'ctx> {
    Bool(Bool<'ctx>),
    Var(Dynamic<'ctx>),
}

impl<'ctx> UnrollingReturn<'ctx> {
    pub fn unwrap_bool(self) -> Bool<'ctx> {
        match self {
            UnrollingReturn::Bool(b) => b,
            _ => panic!("Expected UnrollingReturn::Bool type"),
        }
    }
}

pub struct AHLTLObject<'ctx> {
    pub k: usize,
    pub m: usize,
    pub path_mappings: HashMap<String, usize>,
    pub positions: HashMap<String, HashMap<String, HashMap<String, Bool<'ctx>>>>,
    pub trajectories: HashMap<String, HashMap<String, Vec<Bool<'ctx>>>>,
    pub offs: HashMap<String, HashMap<String, Vec<Bool<'ctx>>>>,
    pub semantics: Semantics,
}

impl<'ctx> AHLTLObject<'ctx> {
    pub fn new(
        path_mappings: HashMap<String, usize>,
        positions: HashMap<String, HashMap<String, HashMap<String, Bool<'ctx>>>>,
        trajectories: HashMap<String, HashMap<String, Vec<Bool<'ctx>>>>,
        offs: HashMap<String, HashMap<String, Vec<Bool<'ctx>>>>,
        k: usize,
        m: usize,
        semantics: Semantics,
    ) -> Self {
        AHLTLObject {
            k,
            m,
            path_mappings,
            positions,
            trajectories,
            offs,
            semantics,
        }
    }

    // fn setpos(& self, path_name: String, traj_name: String, i: usize, j: usize) -> Bool {

    // }
}