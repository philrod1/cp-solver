use std::io::{self, Read};
use std::ops::ControlFlow;
use std::path::PathBuf;
use std::process::ExitCode;
use std::{env, fs};

use lang::{ErrorKind, ProbType, ScpError, ScpModel};
use solver::{Config, Outcome, Solution};

const USAGE: &str = "\
usage: cps <model.scp> [--proof <path-stem>]
       cps --check [--json] <model.scp>

  --proof <stem>  write a VeriPB proof to <stem>.opb and <stem>.pbp
  --check         report every problem in the model, without solving it
  --json          with --check, report them as a JSON array

A model path of - reads the model from standard input.
Exit status: 0 if all went well, 1 if the model has problems, 2 if cps
could not run (bad arguments, an unreadable file).";

/// Why `cps` stopped early.
enum Failure {
    /// The model has problems, already reported.
    Model,
    /// `cps` itself couldn't run.
    Usage(String),
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(Failure::Model) => ExitCode::from(1),
        Err(Failure::Usage(msg)) => {
            eprintln!("cps: {msg}");
            ExitCode::from(2)
        }
    }
}

struct Args {
    model: String,
    check: bool,
    json: bool,
    config: Config,
}

fn parse_args() -> Result<Option<Args>, String> {
    let mut args = env::args().skip(1);
    let mut model = None;
    let (mut check, mut json) = (false, false);
    let mut config = Config::default();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--proof" => {
                let stem = args.next().ok_or("--proof needs a path")?;
                config.proof = Some(PathBuf::from(stem));
            }
            "--check" => check = true,
            "--json" => json = true,
            "-h" | "--help" => return Ok(None),
            "-" if model.is_none() => model = Some(arg),
            _ if arg.starts_with('-') => return Err(format!("unknown option {arg}\n{USAGE}")),
            _ if model.is_none() => model = Some(arg),
            _ => return Err(format!("unexpected argument {arg}\n{USAGE}")),
        }
    }
    let model = model.ok_or(USAGE)?;
    if json && !check {
        return Err(format!("--json goes with --check\n{USAGE}"));
    }
    if check && config.proof.is_some() {
        return Err(format!(
            "--check solves nothing, so writes no proof\n{USAGE}"
        ));
    }
    Ok(Some(Args {
        model,
        check,
        json,
        config,
    }))
}

fn run() -> Result<(), Failure> {
    let Some(args) = parse_args().map_err(Failure::Usage)? else {
        println!("{USAGE}");
        return Ok(());
    };
    let source = read_model(&args.model).map_err(Failure::Usage)?;

    if args.check {
        let problems = lang::check_scp(&source);
        if args.json {
            println!("{}", json_problems(&problems));
        } else {
            report(&args.model, &problems);
        }
        return if problems.is_empty() {
            Ok(())
        } else {
            Err(Failure::Model)
        };
    }

    let Ok((model, scp)) = lang::read_scp(&source) else {
        report(&args.model, &lang::check_scp(&source));
        return Err(Failure::Model);
    };
    let config = args.config;
    let solver_error = |e| Failure::Usage(format!("solver error: {e}"));

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
            eprintln!("{}: optimisation problems aren't supported yet", args.model);
            return Err(Failure::Model);
        }
    }
    Ok(())
}

/// The model's text, from a file or, for `-`, standard input.
fn read_model(path: &str) -> Result<String, String> {
    if path == "-" {
        let mut text = String::new();
        io::stdin()
            .read_to_string(&mut text)
            .map_err(|e| format!("cannot read standard input: {e}"))?;
        return Ok(text);
    }
    fs::read_to_string(path).map_err(|e| format!("cannot read {path}: {e}"))
}

/// One line per problem, on standard error, as `path:line:column: kind:
/// message`.
fn report(path: &str, problems: &[ScpError]) {
    let path = if path == "-" { "<stdin>" } else { path };
    for p in problems {
        let at = p.span.start;
        let kind = match p.kind {
            ErrorKind::Unsupported => "unsupported",
            ErrorKind::Syntax | ErrorKind::Malformed => "error",
        };
        eprintln!("{path}:{}:{}: {kind}: {}", at.line, at.column, p.message);
    }
}

/// The problems as a JSON array, each
/// `{"kind": ..., "message": ..., "start": {...}, "end": {...}}`, with
/// `kind` one of `syntax`, `malformed` or `unsupported`, and each position
/// as `{"offset": ..., "line": ..., "column": ...}`: offsets in bytes,
/// lines and columns from 1, columns in characters.
fn json_problems(problems: &[ScpError]) -> String {
    let position = |p: lang::sexpr::Position| {
        format!(
            r#"{{"offset":{},"line":{},"column":{}}}"#,
            p.offset, p.line, p.column
        )
    };
    let items: Vec<String> = problems
        .iter()
        .map(|p| {
            let kind = match p.kind {
                ErrorKind::Syntax => "syntax",
                ErrorKind::Malformed => "malformed",
                ErrorKind::Unsupported => "unsupported",
            };
            format!(
                r#"{{"kind":"{kind}","message":{},"start":{},"end":{}}}"#,
                json_string(&p.message),
                position(p.span.start),
                position(p.span.end)
            )
        })
        .collect();
    format!("[{}]", items.join(","))
}

fn json_string(s: &str) -> String {
    let mut out = String::from('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
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
