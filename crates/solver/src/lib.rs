use std::io;
use std::path::PathBuf;

mod constraints;
mod domain;
mod engine;
mod lit;
mod model;
mod proof;
mod search;
mod store;
mod trail;

pub use constraints::{AllDifferent, Cell, Constraint, Linear, NotEqual, Table};
pub use model::{Model, Solution, VarId};

use engine::Engine;
use proof::NullLogger;
use search::{InputOrder, SmallestDomain, VariableSelector};
use store::DomainStore;

/// Which variable to branch on next
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub enum VarOrder {
    /// The first unfixed variable, in creation order.
    InputOrder,
    /// The unfixed variable with the fewest values.
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
        constraint.post(&mut engine);
    }
    let mut selector = config.var_order.selector();

    Ok(search::search(
        &mut store,
        &mut engine,
        selector.as_mut(),
        &mut NullLogger,
    ))
}
