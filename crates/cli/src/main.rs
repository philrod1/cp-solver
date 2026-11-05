use std::path::PathBuf;
use std::process::ExitCode;
use std::{env, fs};

use solver::{Config, Outcome};

const USAGE: &str = "usage: cps <model-file> [--proof <path-stem>]";

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

    let model = lang::parse(&source).map_err(|e| format!("{}: {e}", model_path.display()))?;
    let outcome = solver::solve(&model, &config).map_err(|e| format!("solver error: {e}"))?;

    match outcome {
        Outcome::Satisfiable(_) => println!("SATISFIABLE"),
        Outcome::Unsatisfiable => println!("UNSATISFIABLE"),
        Outcome::Unknown => println!("UNKNOWN"),
    }
    Ok(())
}
