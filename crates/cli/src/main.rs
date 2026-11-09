use std::ops::ControlFlow;
use std::path::PathBuf;
use std::process::ExitCode;
use std::{env, fs};

use lang::{ProbType, ScpModel};
use solver::{Config, Outcome, Solution};

const USAGE: &str = "usage: cps <model.scp> [--proof <path-stem>]";

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(msg) => {
            eprintln!("cps: {msg}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    let mut args = env::args().skip(1);
    let mut model_path: Option<PathBuf> = None;
    let mut config = Config::default();

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--proof" => {
                let stem = args.next().ok_or("--proof needs a path")?;
                config.proof = Some(PathBuf::from(stem));
            }
            "-h" | "--help" => {
                println!("{USAGE}");
                return Ok(());
            }
            _ if arg.starts_with('-') => return Err(format!("unknown option {arg}\n{USAGE}")),
            _ if model_path.is_none() => model_path = Some(PathBuf::from(arg)),
            _ => return Err(format!("unexpected argument {arg}\n{USAGE}")),
        }
    }

    let model_path = model_path.ok_or(USAGE)?;
    let source = fs::read_to_string(&model_path)
        .map_err(|e| format!("cannot read {}: {e}", model_path.display()))?;

    let (model, scp) = lang::read_scp(&source).map_err(|e| format!("{}: {e}", model_path.display()))?;
    let solver_error = |e| format!("solver error: {e}");

    match scp.prob_type {
        ProbType::Decide => match solver::solve(&model, &config).map_err(solver_error)? {
            Outcome::Satisfiable(sol) => {
                println!("SATISFIABLE");
                print_solution(&scp, &sol);
            }
            Outcome::Unsatisfiable => println!("UNSATISFIABLE"),
            Outcome::Unknown => println!("UNKNOWN"),
        },
        ProbType::Enumerate => {
            let count = solver::enumerate(&model, &config, |sol| {
                print_solution(&scp, sol);
                ControlFlow::Continue(())
            })
            .map_err(solver_error)?;
            println!("{count} solutions");
        }
        ProbType::Minimize(_) | ProbType::Maximize(_) => {
            return Err("optimisation problems aren't supported yet".into());
        }
    }
    Ok(())
}

/// One line per solution: `name=value`, in declaration order.
fn print_solution(scp: &ScpModel, sol: &Solution) {
    let parts: Vec<String> = scp
        .variables
        .iter()
        .map(|(name, var)| format!("{name}={}", sol.value(*var)))
        .collect();
    println!("{}", parts.join(" "));
}
