//! The `Propagator` trait, the context propagators work through
//! Mapping from constraints to propagators.

mod not_equal;

use crate::domain::{Conflict, SparseDomain};
use crate::engine::Engine;
use crate::lit::Lit;
use crate::model::{Constraint, VarId};
use crate::proof::{Justification, ProofLogger};
use crate::store::{DomainStore, Event};

use not_equal::NotEqual;

pub(crate) trait Propagator {
    #[allow(dead_code)] // for tracing and stats
    fn name(&self) -> &'static str;

    /// Which variables wake this propagator, and on which event.
    /// Called when the propagator is added to the engine.
    fn watches(&self) -> Vec<(VarId, Event)>;

    /// Called when a watched variable changes
    fn propagate(&mut self, ctx: &mut PropagationContext<'_>) -> Result<(), Conflict>;
}

/// A propagator's only way to read and change domains.
pub(crate) struct PropagationContext<'a> {
    pub(crate) store: &'a mut DomainStore,
    pub(crate) proof: &'a mut dyn ProofLogger,
    pub(crate) changed: &'a mut Vec<(VarId, Event)>,
}

impl PropagationContext<'_> {
    pub(crate) fn domain(&self, var: VarId) -> &SparseDomain {
        self.store.domain(var)
    }

    pub(crate) fn fixed_value(&self, var: VarId) -> Option<i64> {
        self.store.domain(var).fixed_value()
    }

    /// Infer var != val
    pub(crate) fn remove(
        &mut self,
        var: VarId,
        val: i64,
        why: Justification,
    ) -> Result<(), Conflict> {
        if let Some(event) = self.store.remove(var, val)? {
            self.proof.inference(Lit::Neq(var, val), why);
            self.changed.push((var, event));
        }
        Ok(())
    }
}

/// Turn a model constraint into propagators.
pub(crate) fn post(constraint: &Constraint, engine: &mut Engine) {
    match *constraint {
        Constraint::NotEqual {
            x,
            x_offset,
            y,
            y_offset,
        } => engine.add(Box::new(NotEqual::new(x, x_offset, y, y_offset))),
    }
}
