//! Constraints and the propagators that enforce them.
//!
//! Everything about one constraint lives in its own file: the public type
//! users build, how it is posted, its propagator, and its tests. Adding a
//! constraint means writing that file and adding two lines here.

mod all_different;
mod linear;
mod not_equal;
mod table;

pub use all_different::AllDifferent;
pub use linear::Linear;
pub use not_equal::NotEqual;
pub use table::{Cell, Table};

use std::fmt::Debug;

use crate::domain::{Conflict, SparseDomain};
use crate::engine::Engine;
use crate::lit::Lit;
use crate::model::VarId;
use crate::proof::{Justification, ProofLogger};
use crate::store::{DomainStore, Event};

/// A constraint as stated in a model.
///
/// `Engine` is public but can't be named outside this crate, so only this
/// crate can implement `Constraint`; users just build and post them.
pub trait Constraint: Debug + Send {
    /// Add the propagators that enforce this constraint.
    fn post(&self, engine: &mut Engine);
}

/// Runtime enforcement of a constraint during search.
pub(crate) trait Propagator: Send {
    #[allow(dead_code)] // for tracing and statistics later
    fn name(&self) -> &'static str;

    /// Which variables wake this propagator, and on which event.
    /// Called once, when the propagator is added to the engine.
    fn watches(&self) -> Vec<(VarId, Event)>;

    fn propagate(&mut self, ctx: &mut PropagationContext<'_>) -> Result<(), Conflict>;
}

/// A propagator's only way to read and change domains. Every change goes
/// through here, so it is trailed, logged, and reported to the engine.
pub(crate) struct PropagationContext<'a> {
    pub(crate) store: &'a mut DomainStore,
    pub(crate) proof: &'a mut dyn ProofLogger,
    pub(crate) changed: &'a mut Vec<(VarId, Event)>,
}

impl PropagationContext<'_> {
    #[allow(dead_code)] // first user will be a bounds propagator
    pub(crate) fn domain(&self, var: VarId) -> &SparseDomain {
        self.store.domain(var)
    }

    pub(crate) fn fixed_value(&self, var: VarId) -> Option<i64> {
        self.store.domain(var).fixed_value()
    }

    /// Infer `var != val`.
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

    /// Infer `var >= k`.
    pub(crate) fn set_lower(
        &mut self,
        var: VarId,
        k: i64,
        why: Justification,
    ) -> Result<(), Conflict> {
        if let Some(event) = self.store.set_lower(var, k)? {
            self.proof.inference(Lit::Ge(var, k), why);
            self.changed.push((var, event));
        }
        Ok(())
    }

    /// Infer `var <= k`.
    pub(crate) fn set_upper(
        &mut self,
        var: VarId,
        k: i64,
        why: Justification,
    ) -> Result<(), Conflict> {
        if let Some(event) = self.store.set_upper(var, k)? {
            self.proof.inference(Lit::Lt(var, k + 1), why);
            self.changed.push((var, event));
        }
        Ok(())
    }
}

/// Shared helpers for propagator unit tests.
#[cfg(test)]
pub(crate) mod testing {
    use std::collections::BTreeSet;

    use crate::domain::Conflict;
    use crate::engine::Engine;
    use crate::model::{Model, VarId};
    use crate::proof::NullLogger;
    use crate::store::DomainStore;

    /// Post the model's constraints and propagate to a fixpoint at the root.
    pub(crate) fn propagate(model: &Model) -> (DomainStore, Result<(), Conflict>) {
        let mut store = DomainStore::new(model);
        let mut engine = Engine::new(model.num_vars());
        for c in model.constraints() {
            c.post(&mut engine);
        }
        let result = engine.propagate(&mut store, &mut NullLogger);
        (store, result)
    }

    pub(crate) fn values(store: &DomainStore, var: VarId) -> BTreeSet<i64> {
        store.domain(var).iter().collect()
    }
}
