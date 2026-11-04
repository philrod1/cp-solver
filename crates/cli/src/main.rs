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
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        return Err(USAGE.to_string());
    }
    let model_file = &args[1];
    let proof_path = if args.len() > 3 && args[2] == "--proof" {
        Some(PathBuf::from(&args[3]))
    } else {
        None
    };

    let source = fs::read_to_string(model_file)
        .map_err(|e| format!("failed to read model file {model_file}: {e}"))?;

    let model = lang::parse(&source)
        .map_err(|e| format!("failed to parse model file {model_file}: {e}"))?;

    let config = Config { proof: proof_path };

    match solver::solve(&model, &config) {
        Ok(Outcome::Satisfiable) => {
            println!("satisfiable");
            Ok(())
        }
        Ok(Outcome::Unsatisfiable) => {
            println!("unsatisfiable");
            Ok(())
        }
        Ok(Outcome::Unknown) => {
            println!("unknown");
            Ok(())
        }
        Err(e) => Err(format!("solver error: {e}")),
    }
}
