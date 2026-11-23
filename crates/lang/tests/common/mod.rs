//! Shared by the test harnesses: run one `.scp` document, tally results,
//! check proofs.
//!
//! Each test binary compiles its own copy of this module and uses a
//! different part of it, so unused items are expected.
#![allow(dead_code)]

use std::collections::BTreeMap;
use std::ops::ControlFlow;
use std::path::Path;
use std::process::Command;

use lang::{ErrorKind, ProbType, read_scp};
use solver::{Config, Objective, Outcome};

/// What happened to one document.
pub enum Run {
    /// Solved: this many solutions (all of them for `enumerate`; 0 or 1
    /// for `decide`).
    Solutions(u64),
    /// Uses something the reader doesn't support yet, and what.
    Unsupported(String),
    /// Optimised: the best value of the objective, if there is a solution.
    Optimum(Option<i64>),
}

/// Read and solve one document. A malformed document is an error, because
/// every corpus file should be valid.
pub fn run(text: &str) -> Result<Run, String> {
    run_with(text, &Config::default())
}

fn run_with(text: &str, config: &Config) -> Result<Run, String> {
    let (model, scp) = match read_scp(text) {
        Ok(read) => read,
        Err(e) if e.kind == ErrorKind::Unsupported => return Ok(Run::Unsupported(e.message)),
        Err(e) => return Err(e.to_string()),
    };
    let stop_after_first = match scp.prob_type {
        ProbType::Enumerate => false,
        ProbType::Decide => true,
        ProbType::Minimize(x) => return optimum(&model, Objective::Minimize(x), config),
        ProbType::Maximize(x) => return optimum(&model, Objective::Maximize(x), config),
    };
    let count = solver::enumerate(&model, config, |_| {
        if stop_after_first {
            ControlFlow::Break(())
        } else {
            ControlFlow::Continue(())
        }
    })
    .map_err(|e| e.to_string())?;
    Ok(Run::Solutions(count))
}

fn optimum(model: &solver::Model, objective: Objective, config: &Config) -> Result<Run, String> {
    let var = match objective {
        Objective::Minimize(x) | Objective::Maximize(x) => x,
    };
    match solver::optimise(model, objective, config, |_| {}).map_err(|e| e.to_string())? {
        Outcome::Satisfiable(best) => Ok(Run::Optimum(Some(best.value(var)))),
        _ => Ok(Run::Optimum(None)),
    }
}

/// What happened to a document's proof.
pub enum Proof {
    /// Some constraint has no proof encoding yet.
    NotWritten,
    /// VeriPB isn't installed.
    NotChecked,
    /// VeriPB's verdict, e.g. `s VERIFIED UNSATISFIABLE`.
    Verified(String),
}

/// Solve again writing a proof to `stem.opb` and `stem.pbp`, and check it
/// with VeriPB (`$VERIPB`, or `veripb` on the PATH). A proof VeriPB
/// rejects is an error.
pub fn run_with_proof(text: &str, stem: &Path) -> Result<Proof, String> {
    let config = Config {
        proof: Some(stem.to_path_buf()),
        ..Config::default()
    };
    match run_with(text, &config) {
        Ok(Run::Solutions(_) | Run::Optimum(_)) => {}
        Ok(Run::Unsupported(_)) => return Ok(Proof::NotWritten),
        Err(e) if e.contains("no proof encoding") => return Ok(Proof::NotWritten),
        Err(e) => return Err(e),
    }
    let file = |ext: &str| format!("{}.{ext}", stem.display());
    let cmd = std::env::var("VERIPB").unwrap_or_else(|_| "veripb".into());
    let Ok(out) = Command::new(cmd)
        .arg("--force-checked-deletion")
        .arg(file("opb"))
        .arg(file("pbp"))
        .output()
    else {
        return Ok(Proof::NotChecked);
    };
    let output =
        String::from_utf8_lossy(&out.stdout).to_string() + &String::from_utf8_lossy(&out.stderr);
    // A proof with unchecked assertions (`a` steps, from linear for now) is
    // accepted as `s UNDER ASSERTIONS ...`, which newer VeriPB says for one.
    let proof = std::fs::read_to_string(file("pbp")).map_err(|e| e.to_string())?;
    let asserted = proof.lines().any(|l| l.starts_with("a "));
    let accepted =
        |l: &&str| l.starts_with("s VERIFIED") || (asserted && l.starts_with("s UNDER ASSERTIONS"));
    match output.lines().find(accepted) {
        Some(verdict) => Ok(Proof::Verified(verdict.to_string())),
        None => Err(format!("VeriPB rejected the proof:\n{output}")),
    }
}

/// The constraint keywords used in a document, for reporting coverage.
pub fn keywords(text: &str) -> Vec<String> {
    let Ok(top) = lang::sexpr::parse(text) else {
        return vec![];
    };
    let Some(cons) = top
        .as_list()
        .and_then(|sections| sections.get(2)?.as_list())
    else {
        return vec![];
    };
    cons.iter()
        .skip(1) // the `constraints` tag
        .filter_map(|c| c.as_list()?.get(1)?.as_atom().map(str::to_string))
        .collect()
}

/// Counts per category, printed at the end of a harness run.
#[derive(Default)]
pub struct Tally {
    pub passed: u64,
    pub unsupported: BTreeMap<String, u64>,
    pub skipped_rows: u64,
    pub failures: Vec<String>,
}

impl Tally {
    pub fn report(&self, what: &str) {
        let total =
            self.passed + self.unsupported.values().sum::<u64>() + self.failures.len() as u64;
        println!(
            "\n== {what}: {} / {total} documents solved correctly",
            self.passed
        );
        if self.skipped_rows > 0 {
            println!(
                "   {} skipped: incomplete rows in the input",
                self.skipped_rows
            );
        }
        if !self.unsupported.is_empty() {
            println!("   skipped as unsupported:");
            for (op, n) in &self.unsupported {
                println!("     {n:5}  {op}");
            }
        }
        for f in self.failures.iter().take(20) {
            println!("   FAIL {f}");
        }
        if self.failures.len() > 20 {
            println!("   ... and {} more failures", self.failures.len() - 20);
        }
    }
}
