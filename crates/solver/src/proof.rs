//! Proof logging for the solver.  Only it isn't implemented yet.
use crate::lit::Lit;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Justification {
    Rup,
    // Explicit(Box<dyn FnOnce(&mut ProofWriter)>), // Write `pol` steps
    Unchecked, // Trust me, bro.
}

pub(crate) trait ProofLogger {
    fn inference(&mut self, _lit: Lit, _why: Justification) {}
    fn backtrack(&mut self, _decision: &[Lit]) {}
    fn solution(&mut self, _values: &[i64]) {}
    fn unsat(&mut self) {}
}

pub(crate) struct NullLogger;

impl ProofLogger for NullLogger {}
