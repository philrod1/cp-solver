//! Undo trail for domain changes.
//!
//! Each variable is saved at most once per decision level: the first change
//! at a level records the state it had when the level began.  Backtracking
//! pops entries in reverse order, so restoring them leaves every variable as
//! it was when the level was pushed.

use crate::domain::{DomainState, SparseDomain};
use crate::model::VarId;

#[derive(Debug)]
struct Level {
    /// `entries.len()` when the level began.
    mark: usize,
    /// The stamp of the level below, restored on backtrack.
    outer_stamp: u64,
}

#[derive(Debug)]
pub(crate) struct Trail {
    /// Saved states, oldest first.
    entries: Vec<(VarId, DomainState)>,
    levels: Vec<Level>,
    saved_at: Vec<u64>,
    stamp: u64,
    next_stamp: u64,
}

impl Trail {
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            entries: Vec::new(),
            levels: Vec::new(),
            saved_at: vec![0; num_vars],
            stamp: 0,
            next_stamp: 1,
        }
    }

    #[cfg(test)]
    pub(crate) fn level(&self) -> usize {
        self.levels.len()
    }

    pub(crate) fn push_level(&mut self) {
        self.levels.push(Level {
            mark: self.entries.len(),
            outer_stamp: self.stamp,
        });
        self.stamp = self.next_stamp;
        self.next_stamp += 1;
    }

    /// Record `state` for `var`
    /// Called before changing the domain of `var`.
    pub(crate) fn save(&mut self, var: VarId, state: DomainState) {
        if self.levels.is_empty() || self.saved_at[var.index()] == self.stamp {
            return;
        }
        self.saved_at[var.index()] = self.stamp;
        self.entries.push((var, state));
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Undo everything since the last `push_level`.
    pub(crate) fn backtrack(&mut self, domains: &mut [SparseDomain]) {
        let level = self.levels.pop().expect("backtrack at the root");
        for (var, state) in self.entries.drain(level.mark..).rev() {
            domains[var.index()].restore(state);
        }
        // Back on the outer level: variables saved there still have their
        // entries, and those saved only at the popped level don't match.
        self.stamp = level.outer_stamp;
    }
}
