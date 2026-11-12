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

use lang::{read_scp, ProbType, ScpError};
use solver::Config;

/// What happened to one document.
pub enum Run {
    /// Solved: this many solutions (all of them for `enumerate`; 0 or 1
    /// for `decide`).
    Solutions(u64),
    /// Uses a constraint keyword we don't support yet.
    Unsupported(String),
    /// An optimisation problem, which we can't solve yet.
    Optimisation,
}

/// Read and solve one document. A malformed document is an error, because
/// every corpus file should be valid.
pub fn run(text: &str) -> Result<Run, String> {
    run_with(text, &Config::default())
}

fn run_with(text: &str, config: &Config) -> Result<Run, String> {
    let (model, scp) = match read_scp(text) {
        Ok(read) => read,
        Err(ScpError::Unsupported(op)) => return Ok(Run::Unsupported(op)),
        Err(e) => return Err(e.to_string()),
    };
    let stop_after_first = match scp.prob_type {
        ProbType::Enumerate => false,
        ProbType::Decide => true,
        ProbType::Minimize(_) | ProbType::Maximize(_) => return Ok(Run::Optimisation),
    };
    let count = solver::enumerate(&model, config, |_| {
        if stop_after_first { ControlFlow::Break(()) } else { ControlFlow::Continue(()) }
    })
    .map_err(|e| e.to_string())?;
    Ok(Run::Solutions(count))
}

/// What happened to a document's proof.
pub enum Proof {
    /// Some constraint has no proof encoding yet, or it's an optimisation
    /// problem.
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
    let config = Config { proof: Some(stem.to_path_buf()), ..Config::default() };
    match run_with(text, &config) {
        Ok(Run::Solutions(_)) => {}
        Ok(_) => return Ok(Proof::NotWritten),
        Err(e) if e.contains("no proof encoding") => return Ok(Proof::NotWritten),
        Err(e) => return Err(e),
    }
    let file = |ext: &str| format!("{}.{ext}", stem.display());
    let cmd = std::env::var("VERIPB").unwrap_or_else(|_| "veripb".into());
    let Ok(out) = Command::new(cmd).arg(file("opb")).arg(file("pbp")).output() else {
        return Ok(Proof::NotChecked);
    };
    let output = String::from_utf8_lossy(&out.stdout).to_string() + &String::from_utf8_lossy(&out.stderr);
    // A proof with unchecked assertions (`a` steps, from linear for now) is
    // accepted as `s UNDER ASSERTIONS ...`, which newer VeriPB says for one.
    let proof = std::fs::read_to_string(file("pbp")).map_err(|e| e.to_string())?;
    let asserted = proof.lines().any(|l| l.starts_with("a "));
    let accepted = |l: &&str| l.starts_with("s VERIFIED") || (asserted && l.starts_with("s UNDER ASSERTIONS"));
    match output.lines().find(accepted) {
        Some(verdict) => Ok(Proof::Verified(verdict.to_string())),
        None => Err(format!("VeriPB rejected the proof:\n{output}")),
    }
}

/// The constraint keywords used in a document, for reporting coverage.
pub fn keywords(text: &str) -> Vec<String> {
    let Ok(lang::sexpr::SExpr::List(sections)) = lang::sexpr::parse(text) else {
        return vec![];
    };
    let Some(lang::sexpr::SExpr::List(cons)) = sections.get(2) else {
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
    pub optimisation: u64,
    pub skipped_rows: u64,
    pub failures: Vec<String>,
}

impl Tally {
    pub fn report(&self, what: &str) {
        let total = self.passed + self.unsupported.values().sum::<u64>() + self.optimisation + self.failures.len() as u64;
        println!("\n== {what}: {} / {total} documents solved correctly", self.passed);
        if self.optimisation > 0 {
            println!("   {} skipped: optimisation", self.optimisation);
        }
        if self.skipped_rows > 0 {
            println!("   {} skipped: incomplete rows in the input", self.skipped_rows);
        }
        if !self.unsupported.is_empty() {
            println!("   skipped as unsupported, by keyword:");
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
