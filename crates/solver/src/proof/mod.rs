//! Proof logging.
//!
//! The solver talks to a [`ProofLogger`]: [`NullLogger`] when no proof is
//! wanted, [`VeriPb`] to write an OPB model and a VeriPB proof.
//!
//! Every inference is logged as a clause "reason => literal", which VeriPB
//! checks by reverse unit propagation. Every backtrack is logged as the
//! clause "not all of these decisions", also checked by RUP: under the
//! decisions, unit propagation replays the logged inferences to the same
//! conflict.

mod opb;
mod pb;
mod veripb;

pub use opb::{NotEncodable, OpbEncoder};
pub(crate) use pb::Ineq;
pub(crate) use veripb::VeriPb;

use std::io;

use crate::lit::Lit;
use crate::model::VarId;

/// Why an inference holds, for the proof.
#[derive(Copy, Clone, Debug)]
pub(crate) enum Justification<'a> {
    /// Follows from the reason by RUP on the constraint's encoding.
    Rup(Reason<'a>),
    /// Not justified yet. VeriPB accepts it with a warning. **Development only**
    Unchecked(Reason<'a>),
}

/// The facts an inference depends on, all true when it is made.
#[derive(Copy, Clone, Debug)]
pub(crate) enum Reason<'a> {
    /// Exactly these literals.
    Lits(&'a [Lit]),
    /// Everything currently known about these variables: their bounds and
    /// the values missing between them. Always enough, rarely the least.
    Domains(&'a [VarId]),
}

/// How a proof step is checked.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Rule {
    Rup,
    Assert,
}

impl Justification<'_> {
    pub(crate) fn rule(self) -> Rule {
        match self {
            Justification::Rup(_) => Rule::Rup,
            Justification::Unchecked(_) => Rule::Assert,
        }
    }

    pub(crate) fn reason(&self) -> Reason<'_> {
        match *self {
            Justification::Rup(r) | Justification::Unchecked(r) => r,
        }
    }
}

/// How the search ended
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Conclusion {
    /// Stopped at a solution.
    Satisfiable,
    /// No solutions.
    Unsatisfiable,
    /// Found every solution: this many (at least one).
    Enumerated(u64),
}

/// Receives everything the proof needs. Every method defaults to doing
/// nothing, so a logger only overrides what it cares about.
pub(crate) trait ProofLogger {
    /// Whether anything is being written. When it isn't, callers skip
    /// working out reasons.
    fn is_logging(&self) -> bool {
        false
    }

    /// A propagator is about to make `lit` true because of `reason`.
    fn inference(&mut self, _lit: Lit, _rule: Rule, _reason: &[Lit]) {}

    /// A propagator found that `reason` can't hold.
    fn conflict(&mut self, _rule: Rule, _reason: &[Lit]) {}

    /// The conjunction of `decisions` leads to a conflict or duplicate state.
    fn backtrack(&mut self, _decisions: &[Lit]) {}

    /// A solution, as the value of every variable.
    fn solution(&mut self, _values: &[i64]) {}

    /// `var` was declared with an empty domain.
    fn empty_domain(&mut self, _var: VarId) {}

    /// The end of the proof.
    fn conclude(&mut self, _conclusion: Conclusion) {}

    /// Flush, and report the first error writing the proof, if any.
    fn finish(&mut self) -> io::Result<()> {
        Ok(())
    }
}

pub(crate) struct NullLogger;

impl ProofLogger for NullLogger {}
