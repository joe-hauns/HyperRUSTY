use std::{collections::HashMap, usize};

use z3::{
    ast::{
        Ast, Bool, 
        Int, BV,
    },
    Context,
};
use ir::*;
use enchelper::*;
use hltlunroller::*;
use parser::*;

fn adj_bool_to_z3<'ctx>(ctx: &'ctx Context, adj: &Vec<Vec<bool>>) -> Vec<Vec<Bool<'ctx>>> {
    adj.iter()
        .map(|row| row.iter().map(|&b| Bool::from_bool(ctx, b)).collect())
        .collect()
}

pub struct LoopCondition<'env, 'ctx> {
    pub ctx: &'ctx Context,
    pub model1: &'env SMVEnv<'ctx>,
    pub model2: &'env SMVEnv<'ctx>,
    pub symstates1: Vec<EnvState<'ctx>>,
    pub symstates2: Vec<EnvState<'ctx>>,
    pub vals1: Vec<ConcreteState<'ctx>>,
    pub vals2: Vec<ConcreteState<'ctx>>,
    pub sim_i_j: Vec<Vec<Bool<'ctx>>>,
    pub trans_i_ipr: Vec<Vec<Bool<'ctx>>>,
    pub trans_j_jpr: Vec<Vec<Bool<'ctx>>>
}

impl<'env, 'ctx> LoopCondition<'env, 'ctx> {
    pub fn new(ctx: &'ctx Context, model1: &'env SMVEnv<'ctx>, model2: &'env SMVEnv<'ctx>) -> Self {
        Self {
            ctx,
            model1,
            model2,
            symstates1: Vec::new(),
            symstates2: Vec::new(),
            vals1: Vec::new(),
            vals2: Vec::new(),
            trans_i_ipr: Vec::new(),
            trans_j_jpr: Vec::new(),
            sim_i_j: Vec::new(),
        }
    }

    pub fn init_forall_exist(&mut self) {
        let g1 = self.model1.bfs_build_explicit_graph(Some("m1"));
        let g2 = self.model2.bfs_build_explicit_graph(Some("m2"));

        self.vals1 = g1.states;
        self.trans_i_ipr = adj_bool_to_z3(self.ctx, &g1.adjacency);

        self.vals2 = g2.states;
        self.trans_j_jpr = adj_bool_to_z3(self.ctx, &g2.adjacency);

        self.symstates1 = Vec::with_capacity(self.vals1.len());
        for i in 0..self.vals1.len() {
            self.symstates1.push(self.model1.make_enum_dummy_state(self.ctx, i, 1));
        }
        self.symstates2 = Vec::with_capacity(self.vals2.len());
        for i in 0..self.vals2.len() {
            self.symstates2.push(self.model2.make_enum_dummy_state(self.ctx, i, 2));
        }

        self.sim_i_j = Vec::with_capacity(self.vals1.len());
        for i in 0..self.vals1.len() {
            let mut row = Vec::with_capacity(self.vals2.len());
            for j in 0..self.vals2.len() {
                row.push(Bool::new_const(self.ctx, format!("sim_{}_{}", i, j)));
            }
            self.sim_i_j.push(row);
        }
    }

    pub fn init_exist_forall(&mut self){
        self.symstates1 = self.model1.generate_all_symbolic_states(Some("m1"));
        self.symstates2 = self.model2.generate_all_symbolic_states( Some("m2"));

        self.sim_i_j = Vec::with_capacity(self.symstates1.len());
        for i in 0..self.symstates1.len() {
            let mut row = Vec::with_capacity(self.symstates2.len());
            for j in 0..self.symstates2.len() {
                row.push(Bool::new_const(self.ctx, format!("sim_{}_{}", i, j)));
            }
            self.sim_i_j.push(row);
        }
    }

    fn pin_state_eq(&self, env: &SMVEnv<'ctx>, sym: &EnvState<'ctx>, conc: &ConcreteState<'ctx>) -> Vec<Bool<'ctx>> {
        let mut cs = Vec::<Bool>::new();
        for (name, var) in env.get_variables().iter() {
            match (&var.sort, conc.get(name).expect("missing concrete value")) {
                (VarType::Bool{..}, ConcreteVal::B(b)) => {
                    let v = bool_var!(sym, name);
                    cs.push(v._eq(&Bool::from_bool(self.ctx, *b)));
                }
                (VarType::Int{..}, ConcreteVal::I(n)) => {
                    let v = int_var!(sym, name);
                    cs.push(v._eq(&Int::from_i64(self.ctx, *n)));
                }
                (VarType::BVector{width, ..}, ConcreteVal::BV(n, w)) => {
                    assert_eq!(*width, *w, "BV width mismatch for {}", name);
                    let v = bv_var!(sym, name);
                    cs.push(v._eq(&BV::from_i64(self.ctx, *n, *w)));
                }
                _ => panic!("type mismatch while pinning {}", name),
            }
        }
        cs
    }

    pub fn pin_all_explicit_states(&self) -> Vec<Bool<'ctx>> {
        let mut out = Vec::<Bool>::new();
        for i in 0..self.symstates1.len() {
            out.extend(self.pin_state_eq(self.model1, &self.symstates1[i], &self.vals1[i]));
        }
        for i in 0..self.symstates2.len() {
            out.extend(self.pin_state_eq(self.model2, &self.symstates2[i], &self.vals2[i]));
        }
        out
    }

    pub fn legal_explicit_state(&self) -> Vec<Bool<'env>>{
        self.pin_all_explicit_states()
    }
    pub fn legal_state(&self) -> Vec<Bool<'env>> {
        let mut valid_states = Vec::new();
        for symstate in &self.symstates1 {
            let constraints = self.model1.generate_scope_constraints_for_state(symstate);
            valid_states.extend(constraints);
        }
        for symstate in &self.symstates2 {
            let constraints = self.model2.generate_scope_constraints_for_state(symstate);
            valid_states.extend(constraints);
        }
        valid_states.extend(self.model1.generate_initial_constraints(&self.symstates1));
        valid_states.extend(self.model2.generate_initial_constraints(&self.symstates2));
        valid_states
    }

    pub fn exhaustive_exploration(&self, is_q: bool) -> Vec<Bool<'env>> {
        let (model, symstates) = if is_q {
            (&self.model2, &self.symstates2)
        } else {
            (&self.model1, &self.symstates1)
        };

        let mut constraints = Vec::new();
        for i in 0..symstates.len() {
            for j in (i + 1)..symstates.len() {
                let si = &symstates[i];
                let sj = &symstates[j];
                
                let scope_i = model.generate_scope_constraints_for_state(si);
                let ki = Bool::and(self.ctx, &scope_i.iter().collect::<Vec<_>>());

                let scope_j = model.generate_scope_constraints_for_state(sj);
                let kj = Bool::and(self.ctx, &scope_j.iter().collect::<Vec<_>>());

                let mut diff = Vec::new();
                for (name, _) in model.get_variables().iter() {
                    if let (Some(bi), Some(bj)) = (si.get(name), sj.get(name)) {
                        diff.push(bi._eq(bj).not());
                    }
                }
                let distinct = Bool::or(self.ctx, &diff.iter().collect::<Vec<_>>());
                let and_expr = Bool::and(self.ctx, &[&ki, &kj]);
                
                constraints.push(and_expr.implies(&distinct));
            }
        }
        constraints
    }

    pub fn initial_state_sim_exist_forall(&self) -> Vec<Bool<'env>> {
        let mut constraints = Vec::new();
        constraints.extend(self.model1.generate_initial_constraints(&self.symstates1));
        for j in 0..(self.symstates2.len()) {
            let initial_constraints_2 = self.model2.generate_initial_constraints_for_state(&self.symstates2, j);
            let initial_and = Bool::and(self.ctx, &initial_constraints_2.iter().collect::<Vec<_>>());
            constraints.push(initial_and.implies(&self.sim_i_j[0][j]));
        }
        constraints
    }

    pub fn initial_state_sim_forall_exsist(&self) -> Vec<Bool<'env>> {
        let mut constraints = Vec::new();
        for i in 0..self.symstates1.len() {
            let init_constraint_m1 = self.model1.generate_initial_constraints_for_state(&self.symstates1, i);
            let init_constraint_m1_and = Bool::and(self.ctx, &init_constraint_m1.iter().collect::<Vec<_>>());
            let mut inner_formula = Vec::new();
            for j in 0..self.symstates2.len() {
                let mut inner_and = Vec::new();
                let init_constraint_m2 = self.model2.generate_initial_constraints_for_state(&self.symstates2, j);
                inner_and.push(Bool::and(self.ctx, &init_constraint_m2.iter().collect::<Vec<_>>()));
                inner_and.push(self.sim_i_j[i][j].clone());
                inner_formula.push(Bool::and(self.ctx, &inner_and.iter().collect::<Vec<_>>()));
            }
            let inner_or = Bool::or(self.ctx, &inner_formula.iter().collect::<Vec<_>>());
            constraints.push(init_constraint_m1_and.implies(&inner_or));
        }
        constraints
    }

    pub fn succ_t(&self, x: usize, x_pr: usize) -> Bool<'env> {
        let mut constraints = Vec::new();
        let m = self.symstates2.len();
        
        for y in 0..m {
            let mut inner_implication = Vec::new();
            for y_pr in 0..m {
                let transition = self.model2.generate_transition_relation(&self.symstates2[y], &self.symstates2[y_pr]);
                let transition_constraint: Bool<'_> = Bool::and(self.ctx, &transition.iter().collect::<Vec<_>>());
                inner_implication.push(transition_constraint.implies(&self.sim_i_j[x_pr][y_pr]));
            }
            let inner_implication = Bool::and(self.ctx, &inner_implication.iter().collect::<Vec<_>>());
            constraints.push(self.sim_i_j[x][y].implies(&inner_implication));
        }
        Bool::and(self.ctx, &constraints.iter().collect::<Vec<&Bool>>())
    }

    pub fn valid_path(&self, n: usize) -> Vec<Bool<'env>> {
        let mut constraints = Vec::new();
        for i in 0..(n - 1) {
            let mut transition = self.model1.generate_transition_relation(&self.symstates1[i], &self.symstates1[i + 1]);
            transition.push(self.succ_t(i, i + 1));
            constraints.extend(transition);
        }
        constraints
    }

    pub fn loop_back(&self, n: usize) -> Bool<'env> {
        let mut constraints = Vec::new();
        for i in 0..(n) {
            let transition = self.model1.generate_transition_relation(&self.symstates1[n - 1], &self.symstates1[i]);
            let transition_constraint = Bool::and(self.ctx, &transition.iter().collect::<Vec<_>>());
            let mut inner_formula = Vec::new();
            inner_formula.push(transition_constraint);
            inner_formula.push(self.succ_t(n - 1, i));
            constraints.push(Bool::and(self.ctx, &inner_formula.iter().collect::<Vec<_>>()));
        }
        Bool::or(self.ctx, &constraints.iter().collect::<Vec<&Bool>>())
    }

    pub fn simulation_constrains_exsist_forall(&self) -> Bool<'env> {
        let mut constrains = Vec::new();
        for n in 1..self.symstates1.len(){
            let mut valid_path_constain = self.valid_path(n);
            valid_path_constain.push(self.loop_back(n));
            constrains.push(Bool::and(self.ctx, &valid_path_constain.iter().collect::<Vec<_>>()));
        }
        Bool::or(self.ctx, &constrains.iter().collect::<Vec<&Bool>>())
    }

    pub fn simulation_constrains_forall_exsist(&self) -> Vec<Bool<'env>> {
        let mut constraints = Vec::new();
        let n = self.symstates1.len();
        let k = self.symstates2.len();

        for i in 0..n {
            for t in 0..n {
                let tx = self.trans_i_ipr[i][t].clone();
                let mut per_j = Vec::new();
                for j in 0..k {
                    let mut exists_r = Vec::new();
                    for r in 0..k {
                        let ty = self.trans_j_jpr[j][r].clone();
                        exists_r.push(Bool::and(self.ctx, &[&ty, &self.sim_i_j[t][r]]));
                    }
                    let exists_r = Bool::or(self.ctx, &exists_r.iter().collect::<Vec<_>>());
                    per_j.push(self.sim_i_j[i][j].implies(&exists_r));
                }
                let per_j = Bool::and(self.ctx, &per_j.iter().collect::<Vec<_>>());
                constraints.push(tx.implies(&per_j));
            }
        }
        constraints
    }

    pub fn predicate(&self, formula: &AstNode, i: usize, j: usize, mapping: &HashMap<&str, usize>) -> UnrollingReturn<'ctx> {
        match formula {
            AstNode::Constant {value} => {
                if value.parse::<i64>().is_ok() {
                    let number = value.parse::<i64>().unwrap();
                    return UnrollingReturn::Var(Int::from_i64(self.ctx, number).into());
                }
                if value == "TRUE" {
                    UnrollingReturn::Bool(Bool::from_bool(self.ctx, true))
                }else {
                    UnrollingReturn::Bool(Bool::from_bool(self.ctx, false))
                }
            }
            AstNode::UnOp {operator, operand} => {
                match operator {
                        UnaryOperator::Negation => {
                            UnrollingReturn::Bool(self.predicate(operand, i, j, mapping).unwrap_bool().not())
                        }
                        UnaryOperator::Globally => {
                            UnrollingReturn::Bool(self.predicate(operand, i, j, mapping).unwrap_bool())
                        }
                        _=> panic!("The UnOP in the formula is not supported")
                    }
            }
            AstNode::BinOp { operator, lhs, rhs } => {
                match operator {
                    parser::BinOperator::Equality =>  match (
                        self.predicate(lhs, i, j, mapping),
                        self.predicate(rhs, i, j, mapping),
                    ) {
                        (UnrollingReturn::Bool(b1), UnrollingReturn::Bool(b2)) => UnrollingReturn::Bool(b1._eq(&b2)),
                        (UnrollingReturn::Var(v1), UnrollingReturn::Var(v2)) => match (v1.as_int(), v2.as_int()) {
                            (Some(i1), Some(i2)) => UnrollingReturn::Bool(i1._eq(&i2)),
                            _ => match (v1.as_bv(), v2.as_bv()) {
                                (Some(bv1), Some(bv2)) => UnrollingReturn::Bool(bv1._eq(&bv2)),
                                _ => match (v1.as_bool(), v2.as_bool()) {
                                    (Some(varb1), Some(varb2)) => UnrollingReturn::Bool(varb1._eq(&varb2)),
                                    _ =>panic!("Invalid comparison"),
                                }
                            }
                        },
                        _ => panic!("Invalid comparison")
                    }
                    BinOperator::Conjunction => {
                        let lhs_bool = self.predicate(lhs, i, j, mapping).unwrap_bool();
                        let rhs_bool = self.predicate(rhs, i, j, mapping).unwrap_bool();
                        UnrollingReturn::Bool(Bool::and(self.ctx, &[&lhs_bool, &rhs_bool]))
                    }
                    BinOperator::Disjunction => {
                        let lhs_bool = self.predicate(lhs, i, j, mapping).unwrap_bool();
                        let rhs_bool = self.predicate(rhs, i, j, mapping).unwrap_bool();
                        UnrollingReturn::Bool(Bool::or(self.ctx, &[&lhs_bool, &rhs_bool]))
                    }
                    BinOperator::Implication => {
                        let lhs_bool = self.predicate(lhs, i, j, mapping).unwrap_bool();
                        let rhs_bool = self.predicate(rhs, i, j, mapping).unwrap_bool();
                        UnrollingReturn::Bool(lhs_bool.implies(&rhs_bool))
                    }
                _=> panic!("The BinOp in the fomrula is not supported")
                }
            }
            AstNode::HIndexedProp { proposition, path_identifier } => {
                let idx = *mapping
                    .get(path_identifier.as_str())
                    .expect("missing path_identifier in mapping");

                let (curr_state, env) = match idx {
                    0 => (&self.symstates1[i], &self.model1),
                    1 => (&self.symstates2[j], &self.model2),
                    _ => panic!("wrong mapping"),
                };

                if let Some(v) = curr_state.get(proposition.as_str()) {
                    if let Some(node) = v.as_bool() {
                        UnrollingReturn::Bool(node)
                    } else {
                        UnrollingReturn::Var(v.clone())
                    }
                } else {
                    match env.predicates.get(proposition.as_str()) {
                        Some(predicate) => {
                            let clause = predicate(env, self.ctx, curr_state);
                            UnrollingReturn::Bool(clause)
                        }
                        None => panic!("Undefined variable or predicate `{}`", proposition),
                    }
                }
            }
            _ => unreachable!()
        }
    }

    pub fn relation_predicate(&self, formula: &AstNode) -> Vec<Bool<'env>> {
        let mut constraints = Vec::new();
        for i in 0..self.symstates1.len() {
            for j in 0..self.symstates2.len() {
                let mapping = create_path_mapping(formula, 0);
                let relation_pred = self.predicate(inner_ltl(formula), i, j, &mapping).unwrap_bool();
                constraints.push(self.sim_i_j[i][j].implies(&relation_pred));
            }
        }
        constraints
    }

    pub fn build_loop_condition(&mut self, formula: &AstNode) -> Bool<'env> {
        if !starts_with_g_or_f(formula) {
            panic!("The formula must start with G or F");
        }
        if !has_no_until_or_release(formula) {
            panic!("The formula must not contain Until or Release operators");
        }
        let check = detect_quantifier_order(formula);
        match check {
            0 => panic!("The formula must be AE or EA"),
            1 => {
                self.init_forall_exist();
                let mut all_constraints = Vec::new();
                all_constraints.extend(self.legal_explicit_state());
                all_constraints.extend(self.exhaustive_exploration(false));
                all_constraints.extend(self.initial_state_sim_forall_exsist());
                all_constraints.extend(self.simulation_constrains_forall_exsist());
                all_constraints.extend(self.relation_predicate(formula));
                let refs: Vec<&Bool> = all_constraints.iter().collect();
                Bool::and(self.ctx, &refs)
            }
            2 => {
                self.init_exist_forall();
                let mut all_constraints = Vec::new();
                all_constraints.extend(self.legal_state());     
                all_constraints.extend(self.exhaustive_exploration(true));
                all_constraints.extend(self.initial_state_sim_exist_forall());
                all_constraints.push(self.simulation_constrains_exsist_forall());
                all_constraints.extend(self.relation_predicate(formula));
                let refs: Vec<&Bool<'env>> = all_constraints.iter().collect();
                Bool::and(self.ctx, &refs)
            }
            _ => panic!("Unsupported quantifier order detected"),
        }
    }
}
