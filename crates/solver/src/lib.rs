//! Solver engine

use std::path::PathBuf;

/// A model built through the builder API
#[derive(Debug, Default)]
pub struct Model {}

impl Model {
    pub fn new() -> Self {
        Self::default()
    }
}

#[derive(Debug, Default)]
pub struct Config {
    /// Write a VeriPB proof using this path
    pub proof: Option<PathBuf>,
}

#[derive(Debug)]
pub enum Outcome {
    Satisfiable,
    Unsatisfiable,
    Unknown,
}

pub fn solve(_model: &Model, _config: &Config) -> std::io::Result<Outcome> {
    Ok(Outcome::Unknown)
}
