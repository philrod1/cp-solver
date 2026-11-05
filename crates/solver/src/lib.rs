//! Solver engine
//!
use std::io;
use std::path::PathBuf;

mod domain;
mod engine;
mod lit;
mod model;
mod proof;
mod propagators;
mod search;
mod store;
mod trail;

pub use model::{Constraint, Model, Solution, VarId};

use engine::Engine;
use proof::NullLogger;
use search::{InputOrder, SmallestDomain, VariableSelector};
use store::DomainStore;

/// Which variable to branch on next
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub enum VarOrder {
    InputOrder,
    #[default]
    SmallestDomain,
}

impl VarOrder {
    fn selector(self) -> Box<dyn VariableSelector> {
        match self {
            VarOrder::InputOrder => Box::new(InputOrder),
            VarOrder::SmallestDomain => Box::new(SmallestDomain),
        }
    }
}

/// How to run the solver.
#[derive(Debug, Default)]
pub struct Config {
    /// Write a VeriPB proof (and its OPB model) using this path stem, if set.
    pub proof: Option<PathBuf>,
    pub var_order: VarOrder,
}

#[derive(Debug)]
pub enum Outcome {
    Satisfiable(Solution),
    Unsatisfiable,
    Unknown,
}

/// Solve the given model with the given configuration. Returns an outcome.
pub fn solve(model: &Model, config: &Config) -> io::Result<Outcome> {
    if config.proof.is_some() {
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "proof logging is not implemented yet",
        ));
    }

    let mut store = DomainStore::new(model);
    let mut engine = Engine::new(model.num_vars());
    for constraint in model.constraints() {
        propagators::post(constraint, &mut engine);
    }
    let mut selector = config.var_order.selector();

    Ok(search::search(
        &mut store,
        &mut engine,
        selector.as_mut(),
        &mut NullLogger,
    ))
}
