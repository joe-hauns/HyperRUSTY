use std::collections::HashMap;
use z3::{
    ast::{
        Ast, Bool, Dynamic, 
        forall_const, exists_const,
    },
    Context,
};
use enchelper::*;
use ir::*;
use hltlunroller::*;
use ahltlunroller::*;
use parser::*;

/****************************
*
*   Shared Encoding functions
*
****************************/

pub fn get_z3_encoding<'env, 'ctx>(env: &'env SMVEnv<'ctx>, formula: &'ctx AstNode, k: usize, m: Option<usize>, sem: Semantics) -> Bool<'env> {
    // First, extract path names from the formula
    let path_names = get_path_identifiers(formula);
    // Next, get the corresponding states and path encoding for each name
    let mut states: Vec<Vec<EnvState<'env>>> = Vec::new();
    let mut constraints: Vec<Bool<'env>> = Vec::new();
    for &name in &path_names {
        let (new_states, new_constraint) = env.generate_symbolic_path(k, Some(name));
        states.push(new_states);
        constraints.push(new_constraint);
    }
    // detect the type of formula
    if is_hltl(formula) {
        // Last, call the encoding generator
        generate_hltl_encoding(env.ctx, formula, states, constraints, sem)
    }else {
        // It's an A-HLTL formula
        // Extract M. If it is not provided, panic!
        let m = match m {
            Some(m) => m,
            None => panic!("Unrolloing bound of trajectories can not be None!"),
        };
        // The semantics must be halting
        if !matches!(sem, Semantics::Hpes | Semantics::Hopt) {
            panic!("Only halting semantics is allowed for A-HLTL BMC.");
        }
        // First, create path mappings
        let mapping = create_path_mapping(formula, 0);
        // Second, get trajectory names
        let traj_names = get_traj_identifiers(formula);
        // Next, create position, trajectory, and off encoding variables
        let mut positions = HashMap::new();
        for traj in &traj_names {
            let mut path_map = HashMap::new();
            for path in &path_names {
                let mut ij_map = HashMap::new();
                for i in 0..=k {
                    for j in 0..=m {
                        let key = format!("{}_{}", i, j);
                        let val = Bool::new_const(
                            env.ctx,
                            format!("pos_{}_{}_{}_{}", path, traj, i, j),
                        );
                        ij_map.insert(key, val);
                    }
                }
                path_map.insert(path.clone(), ij_map);
            }
            positions.insert(traj.clone(), path_map);
        }
        
        let mut trajectories = HashMap::new();
        for traj in &traj_names {
            let traj_key = traj.clone();
            let mut path_map = HashMap::new();
            for path in &path_names {
                let path_key = path.clone();
                let mut bool_vec = Vec::with_capacity(m + 1);
                for j in 0..=m {
                    let name = format!("{}_{}_{}", traj, path, j);
                    let b = Bool::new_const(env.ctx, name);
                    bool_vec.push(b);
                }
                path_map.insert(path_key, bool_vec);
            }
            trajectories.insert(traj_key, path_map);
        }

        let mut off = HashMap::new();
        for traj in &traj_names {
            let traj_key = traj.clone();
            let mut path_map = HashMap::new();
            for path in &path_names {
                let path_key = path.clone();
                let mut bool_vec = Vec::with_capacity(m + 1);
                for j in 0..=m {
                    let name = format!("off_{}_{}_{}", path, traj, j);
                    let b = Bool::new_const(env.ctx, name);
                    bool_vec.push(b);
                }
                path_map.insert(path_key, bool_vec);
            }
            off.insert(traj_key, path_map);
        }

        let ahltl_obj = AHLTLObject::new(
            env,
            formula,
            path_names.clone(),
            traj_names,
            mapping,
            positions,
            trajectories,
            off,
            k,
            m,
            sem,
        );
        // Generate the mapping again (why?)
        let mapping = create_path_mapping(formula, 0);

        // Get the A-HLTL pos /\ enc(phi) encoding
        let inner_ltl = ahltl_obj.build_inner();
        // Include valid path conditions
        let inner_with_paths = generate_inner_encoding(env.ctx, formula, &constraints, inner_ltl, 0);

        // Create a partial encoding for E pos. E off. inner_with_paths
        let flat_pos: Vec<_> = ahltl_obj.flatten_pos();
        let pos_refs: Vec<&dyn Ast<'env>> = flat_pos.iter().map(|v| *v as &dyn Ast<'env>).collect();
        let flat_off: Vec<_> = ahltl_obj.flatten_off();
        let off_refs: Vec<&dyn Ast<'env>> = flat_off.iter().map(|v| *v as &dyn Ast<'env>).collect();
        let partial_formula = exists_const(
            env.ctx,
            &pos_refs,
            &[],
            &exists_const(
                env.ctx,
                &off_refs,
                &[],
                &inner_with_paths,
            ),
        );
        let flat_traj = ahltl_obj.flatten_traj();
        complete_ahltl_encoding(env.ctx, formula, partial_formula, flat_traj, states, &mapping)
    }
}

pub fn complete_ahltl_encoding<'ctx>(ctx: &'ctx Context, formula: &AstNode, inner: Bool<'ctx>, traj: HashMap<&'ctx str, Vec<&Bool<'ctx>>>, states: Vec<Vec<EnvState<'ctx>>>, mapping: &HashMap<&str, usize>) -> Bool<'ctx> {
    match formula {
        AstNode::HAQuantifier {identifier, form} => {
            let idx = mapping[identifier as &str];
            let selected_path = &states[idx];
            let vars: Vec<Dynamic<'ctx>> = selected_path
                .iter()
                .flat_map(|env| env.values().cloned()) // clones Dynamic<'ctx>
                .collect();
            let ast_refs: Vec<&dyn Ast<'ctx>> = vars.iter().map(|v| v as &dyn Ast<'ctx>).collect();
            forall_const(
                ctx,
                &ast_refs,
                &[],
                &complete_ahltl_encoding(ctx, form, inner, traj, states, mapping)
            )
        }
        AstNode::HEQuantifier {identifier, form} => {
            let idx = mapping[identifier as &str];
            let selected_path = &states[idx];
            let vars: Vec<Dynamic<'ctx>> = selected_path
                .iter()
                .flat_map(|env| env.values().cloned()) // clones Dynamic<'ctx>
                .collect();
            let ast_refs: Vec<&dyn Ast<'ctx>> = vars.iter().map(|v| v as &dyn Ast<'ctx>).collect();
            exists_const(
                ctx,
                &ast_refs,
                &[],
                &complete_ahltl_encoding(ctx, form, inner, traj, states, mapping)
            )
        }
        AstNode::AEQuantifier {identifier, form} => {
            // Get the corresponding variables from trajectories
            let selected_vars = &traj[identifier as &str];
            let vars: Vec<Dynamic<'ctx>> = selected_vars
                .iter()
                .copied()
                .map(|node| Dynamic::from_ast(node))
                .collect();
            let ast_refs: Vec<&dyn Ast<'ctx>> = vars.iter().map(|v| v as &dyn Ast<'ctx>).collect();
            exists_const(
                ctx,
                &ast_refs,
                &[],
                &complete_ahltl_encoding(ctx, form, inner, traj, states, mapping)
            )
        }
        AstNode::AAQuantifier {identifier, form} => {
            // Get the corresponding variables from trajectories
            let selected_vars = &traj[identifier as &str];
            let vars: Vec<Dynamic<'ctx>> = selected_vars
                .iter()
                .copied()
                .map(|node| Dynamic::from_ast(node))
                .collect();
            let ast_refs: Vec<&dyn Ast<'ctx>> = vars.iter().map(|v| v as &dyn Ast<'ctx>).collect();
            forall_const(
                ctx,
                &ast_refs,
                &[],
                &complete_ahltl_encoding(ctx, form, inner, traj, states, mapping)
            )
        }
        _ => Bool::from_bool(ctx, true),
    }
}

// Combines the LTL encoding of the formula with valid path conditions
fn generate_inner_encoding<'ctx>(ctx: &'ctx Context, formula: &AstNode, path_encodings: &Vec<Bool<'ctx>>, inner_ltl: Bool<'ctx>, k: usize) -> Bool<'ctx> {
    match formula {
        AstNode::HAQuantifier {form, ..} => path_encodings[k].implies(&generate_inner_encoding(ctx, form, path_encodings, inner_ltl, k + 1)),
        AstNode::HEQuantifier {form, ..} => Bool::and(ctx, &[&path_encodings[k], &generate_inner_encoding(ctx, form, path_encodings, inner_ltl, k + 1)]),
        _ => inner_ltl
    }
}


/****************************
*
*   HLTL Encoding Functions
*
****************************/

fn generate_quantified_encoding<'ctx>(ctx: &'ctx Context, formula: &AstNode, paths: &Vec<Vec<EnvState<'ctx>>>, path_encodings: &Vec<Bool<'ctx>>, mapping: &HashMap<&str, usize>, inner: Bool<'ctx>) -> Bool<'ctx> {
    match formula {
        AstNode::HAQuantifier {form, identifier} => {
            let idx = mapping.get(identifier as &str).unwrap();
            let selected_path = &paths[*idx];
            let vars: Vec<Dynamic<'ctx>> = selected_path
                .iter()
                .flat_map(|env| env.values().cloned()) // clones Dynamic<'ctx>
                .collect();
            let ast_refs: Vec<&dyn Ast<'ctx>> = vars.iter().map(|v| v as &dyn Ast<'ctx>).collect();
            // Step 2: Convert to a slice
            let ast_slice: &[&dyn Ast<'ctx>] = &ast_refs;
            forall_const(
                ctx,
                ast_slice,
                &[],
                &generate_quantified_encoding(ctx, form, paths, path_encodings, mapping, inner)
            )
        }
        AstNode::HEQuantifier {form, identifier} => {
            let idx = mapping.get(identifier as &str).unwrap();
            let selected_path = &paths[*idx];
            let vars: Vec<Dynamic<'ctx>> = selected_path
                .iter()
                .flat_map(|env| env.values().cloned()) // clones Dynamic<'ctx>
                .collect();
            let ast_refs: Vec<&dyn Ast<'ctx>> = vars.iter().map(|v| v as &dyn Ast<'ctx>).collect();
            // Step 2: Convert to a slice
            let ast_slice: &[&dyn Ast<'ctx>] = &ast_refs;
            exists_const(
                ctx,
                ast_slice,
                &[],
                &generate_quantified_encoding(ctx, form, paths, path_encodings, mapping, inner)
            )
        }
        _ => inner
    }
}

fn generate_hltl_encoding<'ctx>(ctx: &'ctx Context, formula: &AstNode, paths: Vec<Vec<EnvState<'ctx>>>, path_encodings: Vec<Bool<'ctx>>, sem: Semantics) -> Bool<'ctx> {
    // Unroll the formula first
    let inner_ltl = unroll_hltl_formula(ctx, formula, &paths, &sem);
    // Construct the inner encoding
    let inner = generate_inner_encoding(ctx, formula, &path_encodings, inner_ltl.clone(), 0);
    // Get the mapping
    let mapping = create_path_mapping(formula, 0);
    // Build the complete encoding
    generate_quantified_encoding(ctx, formula, &paths, &path_encodings, &mapping, inner.clone())

}

/****************************
*
*   AHLTL Encoding Functions
*
****************************/

// fn generate_ahltl_encoding<'env,'ctx>(ctx: &'ctx Context, formula: &AstNode, ahltl_enc: AHLTLObject<'env, 'ctx>, states: Vec<Vec<EnvState<'ctx>>>, constraints: Vec<Bool<'ctx>>) -> Bool<'ctx> {

//     // Get the A-HLTL pos /\ enc(phi) encoding
//     let inner_ltl = ahltl_enc.build_inner();
//     // Include valid path conditions
//     let inner_with_paths = generate_inner_encoding(ctx, formula, &constraints, inner_ltl, 0);

//     // Create a partial encoding for E pos. E off. inner_with_paths
//     let flat_pos: Vec<_> = ahltl_enc.flatten_pos();
//     let flat_refs: Vec<&dyn Ast<'ctx>> = flat_pos.iter().map(|v| *v as &dyn Ast<'env>).collect();
//     let flat_off: Vec<_> = ahltl_enc.flatten_off();

//     println!("{:?}", flat_off);

//     Bool::from_bool(ctx, true)
// }
