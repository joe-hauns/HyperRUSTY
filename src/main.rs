#![allow(warnings)]
use std::fs;
use std::path::PathBuf;
use ir::*;
use parser::*;
use enchelper::*;
use encoder::*;
use z3::{
    ast::{
        Ast, Dynamic, Int, Bool,
        BV,
    },
    Config, Context, Solver, SatResult,
};
use clap::{arg, value_parser, ArgGroup, Command};

fn main() {

    //clap setup
    let cli = Command::new("hyperqb")
        .arg(
            arg!(
                -v --verilog <FILE> "Yosys build file"
            )
            .required(false)
            .value_parser(value_parser!(PathBuf)),
        )
        .arg(
            arg!(
                -n --nusmv <FILE> "NuSMV"
            )
            .required(false)
            .num_args(1..)
            .value_parser(value_parser!(PathBuf)),
        )
        .arg(
            arg!(
                -f --formula <FILE> "Hyperproperty formula"
            )
            .required(true)
            .value_parser(value_parser!(PathBuf)),
        )
        .arg(
            arg!(
                -k --unrolling_bound <FILE> "Unrolling bound"
            )
            .required(true)
            .value_parser(value_parser!(usize)),
        )
        .arg(
            arg!(
                -s --semantics <FILE> "Choice of semantics"
            )
            .required(true)
            .value_parser(value_parser!(String)),
        )
        .arg(
            arg!(
                -m --trajectory_bound <FILE> "Trajectory bound"
            )
            .required(false)
            .value_parser(value_parser!(usize)),
        )
        .arg(
            arg!(
                -q --qbf_solver "Use QBF solver (default is Z3)"
            )
            .required(false)
        )
        .arg(
            arg!(
                -t --top <TOP_MODULE> "Top module name (default: main)"
            )
            .required(false)
            .default_value("main")
            .value_parser(value_parser!(String)),
        )
        .arg(
            arg!(
                -o --yosys_output <SMT2_FILE> "Location of SMT2 file if using a build file"
            )
            .required(false)
            .value_parser(value_parser!(PathBuf)),
        )
        .group(ArgGroup::new("input")
            .args(["verilog", "nusmv"])
            .required(true)
            .multiple(false)
        );
        // .group(ArgGroup::new("verilog-branch")
        //     .args(["top", "yosys_output"])
        //     .requires("verilog")
        // );

    let matches = cli.get_matches();

    let unrolling_bound = matches
        .get_one::<usize>("unrolling_bound").unwrap();

    let formula_path = matches
        .get_one::<PathBuf>("formula").unwrap();

    let semantics = match matches
        .get_one::<String>("semantics").unwrap().as_str() {
            "pes" => Semantics::Pes,
            "opt" => Semantics::Opt,
            "hpes" => Semantics::Hopt,
            "hopt" => Semantics::Hpes,
            _ => panic!("Invalid choice of semantics")
        };

    if let Some(nusmv_models) = matches.get_many::<PathBuf>("nusmv") {
        // NuSMV Path
        let model_paths: Vec<_> = nusmv_models.cloned().collect();
        let model_paths: Vec<&str> = model_paths
            .iter()
            .map(|p| {
                p.to_str()
                .expect("Path is not valid UTF-8")
            })
            .collect();
        
            let trajectory_bound = matches
                .get_one::<usize>("trajectory_bound");
    }else {
        // Verilog Path
        let build_path = matches
            .get_one::<PathBuf>("verilog").unwrap();

        let output_file = matches
            .get_one::<PathBuf>("yosys_output").unwrap();

        let top_module = matches
            .get_one::<String>("top").unwrap();
    }





    // To be replaced with the formula path
    let formula = fs::read_to_string("formula.hq").expect("Failed to read the formula");
    let ast_node = parse(&formula).expect("Failed parsing the formula");

    let mut cfg = Config::new();
    cfg.set_model_generation(true);
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    // here we get an SMVEnv from the arguments
    // let env = parse_smv(
    //     input_path,
    //     output_path,
    //     bit_encode,
    //     input_format,
    //     output_format,
    // );

    // Replace this with the value of K
    let K: usize = 5;

    // Get the type of semantics based on the string


    // // Get identifier names to create unrolled paths
    // let path_identifiers: Vec<&str> = get_path_identifiers(&ast_node);
    // let unrolled_models = Vec::new();

    // for i in 0..path_identifiers.len() {
    //     // parse the smv for this model
    //     let env = parse_smv(
    //         input_path[i],
    //         Some("output.txt".to_string()),
    //          false,
    //         "model",
    //         "ir",
    //     );
    //     unrolled_models.push(
    //         env.generate_symbolic_path(K, Some(path_identifiers[i]))
    //     );
    // }

    // let (states_a, sym_path_a) = env.generate_symbolic_path(K, Some("A"));
    // let (states_b, sym_path_b) = env.generate_symbolic_path(K, Some("B"));

    // let form = get_z3_encoding(&env, &ast_node, K, Some(M), Semantics::Hpes);

    // solver.assert(&form);

    // match solver.check() {
    //     SatResult::Sat => {
    //         println!("result: sat.");
    //     },
    //     SatResult::Unsat => {
    //         println!("result: unsat.");
    //     },
    //     SatResult::Unknown => {
    //         println!("result: unknown.");
    //     }
    // };

}