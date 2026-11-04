//! Solver engine

use std::path::PathBuf;

mod domain;
mod model;
mod store;
mod trail;

pub use model::{Constraint, Model, Solution, VarId};

/// How to run the solver.
#[derive(Debug, Default)]
pub struct Config {
    /// Write a VeriPB proof (and its OPB model) using this path stem, if set.
    pub proof: Option<PathBuf>,
}

#[derive(Debug)]
pub enum Outcome {
    Satisfiable(Solution),
    Unsatisfiable,
    Unknown,
}

pub fn solve(_model: &Model, _config: &Config) -> std::io::Result<Outcome> {
    Ok(Outcome::Unknown)
}
