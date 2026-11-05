//! Propagate to a fixpoint: wake the propagators watching each changed
//! variable, run them, repeat until nothing changes or there is a conflict.

use std::collections::VecDeque;

use crate::domain::Conflict;
use crate::model::VarId;
use crate::proof::ProofLogger;
use crate::propagators::{PropagationContext, Propagator};
use crate::store::{DomainStore, Event};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) struct PropId(u32);

impl PropId {
    fn index(self) -> usize {
        self.0 as usize
    }
}

pub(crate) struct Engine {
    props: Vec<Box<dyn Propagator>>,
    watches: Vec<Vec<(PropId, Event)>>,
    queue: VecDeque<PropId>,
    queued: Vec<bool>,
    /// Changes made by the current propagator
    changed: Vec<(VarId, Event)>,
}

impl Engine {
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            props: Vec::new(),
            watches: vec![Vec::new(); num_vars],
            queue: VecDeque::new(),
            queued: Vec::new(),
            changed: Vec::new(),
        }
    }

    /// Register a propagator
    pub(crate) fn add(&mut self, prop: Box<dyn Propagator>) {
        let id = PropId(self.props.len() as u32);
        for (var, event) in prop.watches() {
            self.watches[var.index()].push((id, event));
        }
        self.props.push(prop);
        self.queued.push(false);
        self.enqueue(id);
    }

    /// Tell the engine about a decision made outside of propagation
    pub(crate) fn notify(&mut self, var: VarId, event: Event) {
        for i in 0..self.watches[var.index()].len() {
            let (id, wanted) = self.watches[var.index()][i];
            if event >= wanted {
                self.enqueue(id);
            }
        }
    }

    pub(crate) fn propagate(
        &mut self,
        store: &mut DomainStore,
        proof: &mut dyn ProofLogger,
    ) -> Result<(), Conflict> {
        while let Some(id) = self.queue.pop_front() {
            self.queued[id.index()] = false;
            let mut ctx = PropagationContext {
                store: &mut *store,
                proof: &mut *proof,
                changed: &mut self.changed,
            };
            // Disjoint fields: the propagator and `changed` are borrowed
            // separately, which is why `changed` lives outside the context.
            // Thanks, Claude.
            let result = self.props[id.index()].propagate(&mut ctx);

            if let Err(conflict) = result {
                self.clear();
                return Err(conflict);
            }
            // Wake everything watching what changed, including this
            // propagator itself: not every propagator reaches a fixpoint
            // in one call.
            while let Some((var, event)) = self.changed.pop() {
                self.notify(var, event);
            }
        }
        Ok(())
    }

    fn enqueue(&mut self, id: PropId) {
        if !self.queued[id.index()] {
            self.queued[id.index()] = true;
            self.queue.push_back(id);
        }
    }

    /// Forget pending work after a conflict.
    fn clear(&mut self) {
        for id in self.queue.drain(..) {
            self.queued[id.index()] = false;
        }
        self.changed.clear();
    }
}
