use std::io::{self, Read};
use std::ops::ControlFlow;
use std::path::PathBuf;
use std::process::ExitCode;
use std::{env, fs};

use lang::{CONSTRAINTS, ConstraintKind, ErrorKind, ProbType, ScpError, ScpModel};
use solver::{Config, Objective, Outcome, Solution};

const USAGE: &str = "\
usage: cps <model.scp> [--proof <path-stem>]
       cps --check [--json] <model.scp>
       cps --constraints [--json]

  --proof <stem>  write a VeriPB proof to <stem>.opb and <stem>.pbp
  --check         report every problem in the model, without solving it
  --constraints   list the constraint kinds a model can use
  --json          with --check or --constraints, print JSON

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

/// What the arguments ask for.
enum Command {
    Help,
    Constraints { json: bool },
    Check { model: String, json: bool },
    Solve { model: String, config: Config },
}

fn parse_args() -> Result<Command, String> {
    let mut args = env::args().skip(1);
    let mut model = None;
    let (mut check, mut constraints, mut json) = (false, false, false);
    let mut config = Config::default();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--proof" => {
                let stem = args.next().ok_or("--proof needs a path")?;
                config.proof = Some(PathBuf::from(stem));
            }
            "--check" => check = true,
            "--constraints" => constraints = true,
            "--json" => json = true,
            "-h" | "--help" => return Ok(Command::Help),
            "-" if model.is_none() => model = Some(arg),
            _ if arg.starts_with('-') => return Err(format!("unknown option {arg}")),
            _ if model.is_none() => model = Some(arg),
            _ => return Err(format!("unexpected argument {arg}")),
        }
    }
    let proof = config.proof.is_some();
    match (constraints, check, model) {
        (true, false, None) if !proof => Ok(Command::Constraints { json }),
        (true, _, _) => Err("--constraints takes no model, and no other options but --json".into()),
        (false, true, Some(_)) if proof => Err("--check solves nothing, so writes no proof".into()),
        (false, true, Some(model)) => Ok(Command::Check { model, json }),
        (false, false, Some(_)) if json => Err("--json goes with --check or --constraints".into()),
        (false, false, Some(model)) => Ok(Command::Solve { model, config }),
        (false, _, None) => Err("no model given".into()),
    }
}

fn run() -> Result<(), Failure> {
    let usage = |msg: String| Failure::Usage(format!("{msg}\n{USAGE}"));
    match parse_args().map_err(usage)? {
        Command::Help => {
            println!("{USAGE}");
            Ok(())
        }
        Command::Constraints { json } => {
            if json {
                println!("{}", json_constraints(CONSTRAINTS));
            } else {
                print_constraints(CONSTRAINTS);
            }
            Ok(())
        }
        Command::Check { model, json } => {
            let source = read_model(&model).map_err(Failure::Usage)?;
            let problems = lang::check_scp(&source);
            if json {
                println!("{}", json_problems(&problems));
            } else {
                report(&model, &problems);
            }
            if problems.is_empty() {
                Ok(())
            } else {
                Err(Failure::Model)
            }
        }
        Command::Solve { model, config } => {
            let source = read_model(&model).map_err(Failure::Usage)?;
            solve(&model, &source, &config)
        }
    }
}

fn solve(path: &str, source: &str, config: &Config) -> Result<(), Failure> {
    let Ok((model, scp)) = lang::read_scp(source) else {
        report(path, &lang::check_scp(source));
        return Err(Failure::Model);
    };
    let solver_error = |e| Failure::Usage(format!("solver error: {e}"));

    match scp.prob_type {
        ProbType::Decide => match solver::solve(&model, config).map_err(solver_error)? {
            Outcome::Satisfiable(sol) => {
                println!("SATISFIABLE");
                print_solution(&scp, &sol);
            }
            Outcome::Unsatisfiable => println!("UNSATISFIABLE"),
            Outcome::Unknown => println!("UNKNOWN"),
        },
        ProbType::Enumerate => {
            let count = solver::enumerate(&model, config, |sol| {
                print_solution(&scp, sol);
                ControlFlow::Continue(())
            })
            .map_err(solver_error)?;
            println!("{count} solutions");
        }
        ProbType::Minimize(x) | ProbType::Maximize(x) => {
            let objective = match scp.prob_type {
                ProbType::Minimize(_) => Objective::Minimize(x),
                _ => Objective::Maximize(x),
            };
            // Each solution as it is found, each better than the last.
            let outcome = solver::optimise(&model, objective, config, |sol| {
                print_solution(&scp, sol);
            })
            .map_err(solver_error)?;
            match outcome {
                Outcome::Satisfiable(best) => println!("OPTIMUM {}", best.value(x)),
                _ => println!("UNSATISFIABLE"),
            }
        }
    }
    Ok(())
}

/// One line per kind, as it would be written, then what it says:
///
/// ```text
/// (label not_equals x y)
///     x ≠ y
/// ```
fn print_constraints(kinds: &[ConstraintKind]) {
    for k in kinds {
        println!("(label {} {})", k.keyword, k.arguments.join(" "));
        println!("    {}", k.summary);
    }
}

/// The kinds as a JSON array, each
/// `{"keyword": ..., "arguments": [...], "summary": ..., "example": ...}`.
/// `example` is the text after the keyword in a constraint that reads,
/// over variables `x`, `y` and `z` from 0 to 3.
fn json_constraints(kinds: &[ConstraintKind]) -> String {
    let items: Vec<String> = kinds
        .iter()
        .map(|k| {
            let arguments: Vec<String> = k.arguments.iter().map(|a| json_string(a)).collect();
            format!(
                r#"{{"keyword":{},"arguments":[{}],"summary":{},"example":{}}}"#,
                json_string(k.keyword),
                arguments.join(","),
                json_string(k.summary),
                json_string(k.example)
            )
        })
        .collect();
    format!("[{}]", items.join(","))
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
