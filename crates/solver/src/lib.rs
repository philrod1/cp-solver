//! A small proof-logging CP solver.

use std::io;
use std::ops::ControlFlow;
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
pub use model::{DuplicateName, Model, Solution, VarId};

use engine::Engine;
use proof::NullLogger;
use search::{InputOrder, SearchEnd, SmallestDomain, VariableSelector};
use store::DomainStore;

/// Which variable to branch on next. A closed set of choices, so a public
/// enum; each maps to a `VariableSelector` strategy inside the crate.
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

/// Find one solution.
pub fn solve(model: &Model, config: &Config) -> io::Result<Outcome> {
    let end = run(model, config, &mut |_| ControlFlow::Break(()))?;
    Ok(match end {
        Some(SearchEnd::Stopped(solution)) => Outcome::Satisfiable(solution),
        Some(SearchEnd::Exhausted) | None => Outcome::Unsatisfiable,
    })
}

/// Find every solution, calling `on_solution` for each. Return
/// `ControlFlow::Break(())` from the callback to stop early. Returns how
/// many solutions were found.
pub fn enumerate(
    model: &Model,
    config: &Config,
    mut on_solution: impl FnMut(&Solution) -> ControlFlow<()>,
) -> io::Result<u64> {
    let mut count = 0;
    run(model, config, &mut |solution| {
        count += 1;
        on_solution(solution)
    })?;
    Ok(count)
}

/// Set up and search. `None` means there was nothing to search: the model
/// declares an empty domain.
fn run(
    model: &Model,
    config: &Config,
    on_solution: &mut dyn FnMut(&Solution) -> ControlFlow<()>,
) -> io::Result<Option<SearchEnd>> {
    if config.proof.is_some() {
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "proof logging is not implemented yet",
        ));
    }
    if model.empty_domain {
        return Ok(None);
    }

    let mut store = DomainStore::new(model);
    let mut engine = Engine::new(model.num_vars());
    for constraint in model.constraints() {
        constraint.post(&mut engine);
    }
    let mut selector = config.var_order.selector();

    Ok(Some(search::search(
        &mut store,
        &mut engine,
        selector.as_mut(),
        &mut NullLogger,
        on_solution,
    )))
}
