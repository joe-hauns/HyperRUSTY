use clap::{arg, value_parser, ArgGroup, Command, Subcommand};
use clap::Parser;
use anyhow::bail;
use anyhow::Context;
use std::cell::RefCell;
use std::collections::HashMap;
use std::path::{self, *};
use log::*;
use ir::*;
use parser::*;
use std::fs;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {

    /// NuSMV input file
    #[arg(short, long)]
    nusmv: Vec<String>,

    /// Yosys input file
    #[arg(short, long)]
    verilog: Vec<PathBuf>,

    /// Yosys input file
    #[arg(short = 'o', long)]
    yosys_output: Option<PathBuf>,

    /// Top yosys module name
    #[arg(short, long, default_value = "main")]
    top: String,

    /// Hyperproperty formula file
    #[arg(short, long)]
    formula: String,

}

impl Args {
    fn validate(&self) -> anyhow::Result<()> {
        if self.verilog.len() != 0 && self.yosys_output.is_none() {
            bail!("if using yosys files (-v, --verilog) the yosys output model.smt2 must be added as option (-o, --yosys-output)");
        }
        Ok(())
    }
}

fn main() -> anyhow::Result<()> {

    env_logger::init();
    let args = Args::parse();
    args.validate()?;

    let mut cfg = z3::Config::new();
    let ctx = z3::Context::new(&cfg);

    let mut envs: Vec<SMVEnv> = 
        std::iter::chain(
            args.nusmv.iter()
                .map(|n|{
                    info!("parsing {n}");
                    Ok(parser_nusmv::parse_smv(
                        &ctx,
                        &n,
                        Some("output.txt".to_owned()),
                        // None, /* output path */
                        /* bit_encode */ false,
                        "model",
                        "ir",
                        ))
                }),
            args.verilog.iter()
                .map(|v| -> anyhow::Result<_>{
                    info!("parsing {}", v.display());
                    let r = hqb_verilog::build_smvenv_from_verilog(
                                    v,
                                    &args.top, 
                                    args.yosys_output.as_ref().unwrap(),
                                    &ctx);
                    Ok(r?)
                                
                })
            ).collect::<anyhow::Result<Vec<_>>>()?;

    let formula = fs::read_to_string(&args.formula)
        .context("Failed to read the formula")?;


    let formula = parser::parse(&formula)
        .context("Failed parsing the formula")?;


    to_smt(&ctx, &envs, &formula)?;
 
    Ok(())
}


// fn term_to_smt<'c>(ctx: &'c z3::Context, term: Box<AstNode>) -> z3::ast::Bool {
//     use z3::ast::*;
//     match self {
//         AstNode::HAQuantifier { identifier, form } => todo!(),
//         AstNode::HEQuantifier { identifier, form } => todo!(),
//         AstNode::AAQuantifier { identifier, form } => todo!(),
//         AstNode::AEQuantifier { identifier, form } => todo!(),
//         AstNode::BinOp { operator, lhs, rhs } => match operator {
//             BinOperator::Equality => lhs.to_smt(ctx)._eq(rhs.to_smt(ctx)),
//             BinOperator::Conjunction => lhs.to_smt(ctx).as_bool().unwrap() & rhs.to_smt(ctx).as_bool().unwrap(),
//             BinOperator::Implication => todo!(),
//             BinOperator::Until => todo!(),
//             BinOperator::Release => todo!(),
//         },
//         AstNode::UnOp { operator, operand } => todo!(),
//         AstNode::HIndexedProp { proposition, path_identifier } => todo!(),
//         AstNode::AIndexedProp { proposition, path_identifier, traj_identifier } => todo!(),
//         AstNode::Constant { value } => todo!(),
//     }
// }


struct SmtTranslationContext<'c, 'd> {
    z3: &'c z3::Context,
    envs: HashMap<&'d str, &'d SMVEnv<'c>>,
    path_sort: z3::Sort<'c>,
    propositions: RefCell<HashMap<&'d str, z3::FuncDecl<'c>>>,
    predicates: RefCell<HashMap<&'d str, z3::FuncDecl<'c>>>,
}

impl<'c, 'd> SmtTranslationContext<'c, 'd> {
    fn from(z3: &'c z3::Context, envs: HashMap<&'d str, &'d SMVEnv<'c>>) -> anyhow::Result<Self> {
        Ok(Self {
            z3, 
            envs,
            path_sort: z3::Sort::uninterpreted(z3, "Path".into()),
            propositions: RefCell::new(Default::default()),
            predicates: RefCell::new(Default::default()),
        })
    }

    fn path_var(&self, var: &str) -> z3::ast::Dynamic<'c> {
        z3::ast::Dynamic::new_const(self.z3, var, &self.path_sort)
    }

    fn proposition(&self, proposition: &'d str, path: &str, z: &z3::ast::Int<'c>)  -> z3::ast::Dynamic<'c> {
        let mut props = self.propositions.borrow_mut();
        let decl = props.entry(proposition)
            .or_insert_with(||{
                let var = &self.envs[path].variables[proposition];
                for (en, e) in &self.envs {
                    assert_eq!(&e.variables[proposition], var);
                }
                let sort = match &var.sort {
                    VarType::Bool { init: _ } => z3::Sort::bool(self.z3),
                    VarType::Int { init: _, lower: _, upper: _ } => z3::Sort::int(self.z3),
                    VarType::BVector { width: _, lower: _, upper: _, init: _ } => todo!(),
                };
                z3::FuncDecl::new(self.z3, proposition, &[&self.path_sort, &z3::Sort::int(self.z3)], &sort)
            });

        decl.apply(&[&self.path_var(path), z])
    }


    fn predicate(&self, p: &'d str, path: &str, z: &z3::ast::Int<'c>)  -> z3::ast::Dynamic<'c> {
        let mut preds = self.predicates.borrow_mut();
        let decl = preds.entry(p)
            .or_insert_with(||{
                let sort = z3::Sort::bool(self.z3);
                z3::FuncDecl::new(self.z3, p, &[&self.path_sort, &z3::Sort::int(self.z3)], &sort)
            });

        decl.apply(&[&self.path_var(path), z])
    }

    fn trace_definition(&self, trace: &'d str) -> z3::ast::Bool<'c> {
        let z3 = self.z3;

        let z0 = &z3::ast::Int::fresh_const(z3, "z");
        let z1 = &(z0 + z3::ast::Int::from_i64(z3, 1));


        let smv_env = &self.envs[trace];
        use z3::ast::Ast;

        let smv_env_state = |z| smv_env.variables.iter()
            .map(|(v, _)| (*v, self.proposition(*v, trace, z)))
            .collect();

        let mut assertions = vec![];

        let env_state0 = smv_env_state(z0);


        let disj = |mut xs: Vec<_>| {
            if let Some(x) = xs.pop() {
                let mut out = x;
                while let Some(x) = xs.pop() {
                    out = out | x;
                }
                return out;
            } else {
                return z3::ast::Bool::from_bool(z3, false);
            }
        };

        let to_smt_vec = |r: ReturnType<'c>| match r {
            ReturnType::Bool(items) => items.iter().map(|b| z3::ast::Dynamic::from(z3::ast::Bool::from_bool(z3, *b))).collect(),
            ReturnType::Int(items) => items.iter().map(|i| z3::ast::Dynamic::from(z3::ast::Int::from_i64(z3, *i))).collect(),
            ReturnType::BVector(items) => todo!(),
            ReturnType::DynAst(dynamic) => vec![dynamic],
        };

        use z3::ast::{Bool,Dynamic,Int};


        let int = |i| Int::from_i64(z3, i);
        let bol = |i| Bool::from_bool(z3, i);

        for (var, Variable { sort }) in &smv_env.variables {
            
            let init: Option<Vec<Dynamic>> = match sort {
                VarType::Bool { init } => init.as_ref().map(|vals| vals.iter().map(|b| Dynamic::from(bol(*b))).collect()),
                VarType::Int { init, lower, upper } => {
                    if let Some(lower) = lower {
                        assertions.push(self.proposition(var, trace, z0).as_int().unwrap().ge(&int(*lower)));
                    }
                    if let Some(upper) = upper {
                        assertions.push(self.proposition(var, trace, z0).as_int().unwrap().le(&int(*upper)));
                    }
                    init.as_ref().map(|vals| vals.iter().map(|v| Dynamic::from(Int::from_i64(z3, *v))).collect())
                },
                VarType::BVector { width, lower, upper, init } => todo!(),
            };
            if let Some(init) = init {
                assertions.push(disj(init.into_iter().map(|x| self.proposition(var, trace, &int(0))._eq(&x)).collect()));
            }
        }

        for (pred, def) in &smv_env.predicates {
            assertions.push(self.predicate(pred, trace, z0)._eq(&Dynamic::from(def(smv_env, z3, &env_state0))));
        }

        for (var, deltas) in &smv_env.transitions {
            let mut neg_last_conditions = vec![];

            for (condition, transition) in deltas {

                let condition_options = to_smt_vec(condition(smv_env, z3, &env_state0)).into_iter().map(|c| c.as_bool().expect("ir conditions must be boolean!")).collect::<Vec<_>>();
                let condition = disj(condition_options);
                let value_options = to_smt_vec(transition(smv_env, z3, &env_state0));
                let value_assignment = disj(value_options.into_iter()
                    .map(|value| self.proposition(var, trace, z1)._eq(&value))
                    .collect::<Vec<_>>());

                let mut full_condition = condition.clone();
                for c in &neg_last_conditions {
                    full_condition = full_condition & c;
                }

                let transition_formula = full_condition.implies(&value_assignment);
                assertions.push(transition_formula);
                neg_last_conditions.push(condition.not());
            }
        }

        z3::ast::forall_const(z3, &[z0], &[], &z3::ast::Bool::and(z3, &assertions))
    }

}

fn formula_to_smt<'c, 'd>(ctx: &SmtTranslationContext<'c, 'd>, term: &'d AstNode, z: &z3::ast::Int<'c>) -> z3::ast::Dynamic<'c> {
    use z3::ast::*;
    use z3::*;
    let z3 = ctx.z3;
    let dr = |x, z| formula_to_smt(ctx, x, z);
    let br = |x, z| {
        let r = dr(x, z);
        match r.as_bool() {
            Some(b) => b,
            None => panic!("expected bool, got {}", r),
        }
    };
    let exists = |v, f| z3::ast::exists_const(z3, &[v], &[], &f);
    let forall = |v, f| z3::ast::forall_const(z3, &[v], &[], &f);
    match term {
        AstNode::HAQuantifier { identifier, form } => todo!(),
        AstNode::HEQuantifier { identifier, form } => todo!(),
        AstNode::AAQuantifier { identifier, form } => todo!(),
        AstNode::AEQuantifier { identifier, form } => todo!(),
        // AstNode::BinOp { operator, lhs, rhs } => todo!(),
        AstNode::BinOp { operator, lhs, rhs } => match operator {
            BinOperator::Equality => Dynamic::from(dr(lhs, z)._eq(&dr(rhs, z))),
            BinOperator::Conjunction => Dynamic::from(br(lhs, z) & br(rhs, z)),
            BinOperator::Disjunction => Dynamic::from(br(lhs, z) | br(rhs, z)),
            BinOperator::Implication => Dynamic::from(br(lhs, z).implies(&br(rhs, z))),
            // trans(L U R) <-> exists zR. (zR >= z & trans(R[z/zR]) & forall zL. (z <= zL < zR ==>  trans(L[z/zL]) ))
            BinOperator::Until => {
                let z_l = &z3::ast::Int::fresh_const(z3, "zL");
                let z_r = &z3::ast::Int::fresh_const(z3, "zR");
                Dynamic::from(exists(z_r, z.le(z_r) & br(rhs, z_r) 
                                     & forall(z_l, (z.le(z_l) & z_l.lt(z_r)).implies(&br(lhs, z_l)))))
            }
            BinOperator::Release => {
                let z_l = &z3::ast::Int::fresh_const(z3, "zL");
                let z_r = &z3::ast::Int::fresh_const(z3, "zR");
                Dynamic::from(forall(z_r, z.le(z_r).implies(&br(rhs, z_r))) 
                            | exists(z_l, z.le(z_l) & br(lhs, z_l) 
                                     & forall(z_r, (z.le(z_r) & z_r.le(z_l)).implies(&br(rhs, z_r)))))
            }
        },
        AstNode::UnOp { operator, operand: phi } => match operator {
            UnaryOperator::Negation => Dynamic::from(br(phi, z).not()),
            UnaryOperator::Globally => {
                let zg = &z3::ast::Int::fresh_const(z3, "zG");
                Dynamic::from(forall(zg, z.le(zg).implies(&br(phi, zg))))
            }
            UnaryOperator::Eventually => {
                let ze = &z3::ast::Int::fresh_const(z3, "zE");
                Dynamic::from(exists(ze, z.le(ze) & br(phi, ze)))
            }
            UnaryOperator::Next => { dr(phi, &(z + Int::from_i64(z3, 1))) },
        },
        AstNode::HIndexedProp { proposition, path_identifier } => ctx.proposition(&proposition, &path_identifier, z),
        AstNode::AIndexedProp { proposition, path_identifier, traj_identifier } => todo!(),
        AstNode::Constant { value } => Dynamic::from(Int::from_str(z3, value).expect(&format!("expected int value, got {value}"))),
    }
}

enum Quantifier {
    Forall, 
    Exists,
}

fn strip_quantifiers(mut formula: &parser::AstNode) -> (Vec<(Quantifier, &str)>, &parser::AstNode) {
    let mut out = Vec::new();
    loop {
        match formula {
            AstNode::HAQuantifier { identifier, form } => {
                out.push((Quantifier::Forall, identifier.as_str()));
                formula = &*form;
            }
            AstNode::HEQuantifier { identifier, form } => {
                out.push((Quantifier::Exists, identifier.as_str()));
                formula = &*form;
            }
            AstNode::AAQuantifier { identifier, form } => todo!(),
            AstNode::AEQuantifier { identifier, form } => todo!(),
            _ => return (out, formula)
        };
    }
}

fn to_smt<'c, 'd>(z3: &'c z3::Context, envs: &'d Vec<SMVEnv<'c>>, formula: &'d parser::AstNode) -> anyhow::Result<()> {

    let (qs, formula) = strip_quantifiers(formula);
    if qs.len() != envs.len() {
        bail!("quantifiers prefix of formula does not match the number of smv environments given")
    }

    let ctx = SmtTranslationContext::from(z3, 
        qs.iter().map(|(_q, trace)| *trace)
            .zip(envs.iter())
            .collect())?;

    let smt_without_qs = formula_to_smt(&ctx, formula, &z3::ast::Int::from_i64(ctx.z3, 0)).as_bool().expect("HyperLTL formula must be of type bool");


    let mut full_smt = smt_without_qs;
    for (q, trace) in qs.iter().rev() {
        let def = ctx.trace_definition(trace);
        let trace = ctx.path_var(trace);
        full_smt = match q {
            Quantifier::Forall => z3::ast::forall_const(z3, &[&trace], &[], &def.implies(&full_smt)),
            Quantifier::Exists => z3::ast::exists_const(z3, &[&trace], &[], &(def & full_smt)),
        };
    }

    println!("
(set-logic AUFLIA)

(assert (not {full_smt}))

(check-sat)
    ");

    Ok(())

}

