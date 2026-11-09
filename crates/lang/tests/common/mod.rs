//! Shared by the corpus harnesses: run one `.scp` document and tally results.

use std::collections::BTreeMap;
use std::ops::ControlFlow;

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
    let count = solver::enumerate(&model, &Config::default(), |_| {
        if stop_after_first { ControlFlow::Break(()) } else { ControlFlow::Continue(()) }
    })
    .map_err(|e| e.to_string())?;
    Ok(Run::Solutions(count))
}

/// The constraint keywords used in a document, for reporting coverage.
#[allow(dead_code)] // each test binary uses a different part of this module
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
