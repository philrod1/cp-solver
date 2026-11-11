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
use crate::proof::{Justification, NotEncodable, OpbEncoder, ProofLogger, Reason};
use crate::store::{DomainStore, Event};

/// A constraint as stated in a model.
///
/// `Engine` is public but can't be named outside this crate, so only this
/// crate can implement `Constraint`; users just build and post them.
pub trait Constraint: Debug + Send {
    /// Add the propagators that enforce this constraint.
    fn post(&self, engine: &mut Engine);

    /// Write the pseudo-Boolean rows that define this constraint for the
    /// OPB model a proof is checked against.
    fn encode(&self, _opb: &mut OpbEncoder<'_>) -> Result<(), NotEncodable> {
        Err(NotEncodable)
    }
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
    pub(crate) fn domain(&self, var: VarId) -> &SparseDomain {
        self.store.domain(var)
    }

    pub(crate) fn fixed_value(&self, var: VarId) -> Option<i64> {
        self.store.domain(var).fixed_value()
    }

    /// Infer `var != val`.
    pub(crate) fn remove(&mut self, var: VarId, val: i64, why: Justification) -> Result<(), Conflict> {
        if !self.domain(var).contains(val) {
            return Ok(());
        }
        self.log(Some(Lit::Neq(var, val)), why);
        let event = self.store.remove(var, val)?;
        self.changed(var, event);
        Ok(())
    }

    /// Infer `var >= k`.
    pub(crate) fn set_lower(&mut self, var: VarId, k: i64, why: Justification) -> Result<(), Conflict> {
        if k <= self.domain(var).lower() {
            return Ok(());
        }
        self.log(Some(Lit::Ge(var, k)), why);
        let event = self.store.set_lower(var, k)?;
        self.changed(var, event);
        Ok(())
    }

    /// Infer `var <= k`.
    pub(crate) fn set_upper(&mut self, var: VarId, k: i64, why: Justification) -> Result<(), Conflict> {
        if k >= self.domain(var).upper() {
            return Ok(());
        }
        self.log(Some(Lit::Lt(var, k + 1)), why);
        let event = self.store.set_upper(var, k)?;
        self.changed(var, event);
        Ok(())
    }

    /// The constraint can't be satisfied, given `why`'s reason.
    pub(crate) fn fail(&mut self, why: Justification) -> Result<(), Conflict> {
        self.log(None, why);
        Err(Conflict)
    }

    fn changed(&mut self, var: VarId, event: Option<Event>) {
        if let Some(event) = event {
            self.changed.push((var, event));
        }
    }

    /// Log "reason => lit", or with no `lit` "not reason". Called before
    /// the change is made, so the reason describes the domains it used.
    fn log(&mut self, lit: Option<Lit>, why: Justification) {
        if !self.proof.is_logging() {
            return;
        }
        let reason = self.reason_lits(why.reason());
        match lit {
            Some(lit) => self.proof.inference(lit, why.rule(), &reason),
            None => self.proof.conflict(why.rule(), &reason),
        }
    }

    fn reason_lits(&self, reason: Reason) -> Vec<Lit> {
        match reason {
            Reason::Lits(lits) => lits.to_vec(),
            Reason::Domains(vars) => {
                let mut lits = Vec::new();
                for &x in vars {
                    let d = self.domain(x);
                    let (lo, hi) = (d.lower(), d.upper());
                    lits.push(Lit::Ge(x, lo));
                    lits.push(Lit::Lt(x, hi + 1));
                    lits.extend((lo + 1..hi).filter(|&v| !d.contains(v)).map(|v| Lit::Neq(x, v)));
                }
                lits
            }
        }
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
