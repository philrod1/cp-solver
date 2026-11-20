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
pub(crate) use pb::{Ineq, PbLit};
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
    #[allow(dead_code)] // no propagator needs it at the moment
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

/// A row of the OPB model or a line of the proof, by its label (without
/// the `@`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Line(pub(crate) String);

impl Line {
    /// The row `@c[name][role]` a constraint's encoding wrote.
    pub(crate) fn row(constraint: &str, role: &str) -> Self {
        Line(format!("c[{constraint}][{role}]"))
    }
}

/// A flag fully reified against an inequality: true exactly when it holds.
#[derive(Clone, Debug)]
pub(crate) struct Flag {
    pub(crate) lit: PbLit,
    /// `flag ⇒ ineq`
    pub(crate) implies: Line,
    /// `¬flag ⇒ ¬ineq`, that is, `ineq ⇒ flag`
    pub(crate) implied_by: Line,
}

impl Flag {
    /// The flag named `name`, with its halves labelled `name[r]` and
    /// `name[f]`, as both the OPB encoder and the proof write them.
    pub(crate) fn named(lit: PbLit, name: &str) -> Self {
        Flag {
            lit,
            implies: Line(format!("{name}[r]")),
            implied_by: Line(format!("{name}[f]")),
        }
    }
}

/// The atom `x ≥ v` and the lines that define it.
#[derive(Clone, Debug)]
pub(crate) struct GeAtom {
    pub(crate) flag: Flag,
    /// The unit `x ≥ v`, when `v` is at or below `x`'s declared lower bound.
    pub(crate) pin: Option<Line>,
}

/// A cutting-planes derivation, in VeriPB's reverse Polish `pol` syntax:
/// each operand after the first is added to what came before.
#[derive(Clone, Debug, Default)]
pub(crate) struct Pol {
    items: Vec<PolItem>,
}

#[derive(Clone, Debug)]
enum PolItem {
    Line(Line, i128),
    Axiom(PbLit, i128),
    Weaken(PbLit),
    Divide(i128),
    Saturate,
}

impl Pol {
    /// Add `k` times a line.
    pub(crate) fn add(&mut self, line: &Line, k: i128) -> &mut Self {
        self.items.push(PolItem::Line(line.clone(), k));
        self
    }

    /// Add `k` times the axiom `lit ≥ 0`.
    pub(crate) fn axiom(&mut self, lit: PbLit, k: i128) -> &mut Self {
        self.items.push(PolItem::Axiom(lit, k));
        self
    }

    /// Drop `lit`'s variable, weakening the sum so far.
    pub(crate) fn weaken(&mut self, lit: PbLit) -> &mut Self {
        self.items.push(PolItem::Weaken(lit));
        self
    }

    pub(crate) fn divide(&mut self, k: i128) -> &mut Self {
        self.items.push(PolItem::Divide(k));
        self
    }

    pub(crate) fn saturate(&mut self) -> &mut Self {
        self.items.push(PolItem::Saturate);
        self
    }

    /// Append in VeriPB syntax, without the `pol` and the final `;`.
    pub(crate) fn write_to(&self, names: &pb::Names, out: &mut String) {
        use std::fmt::Write as _;
        let mut operands = 0;
        for item in &self.items {
            match item {
                PolItem::Line(line, k) => {
                    write!(out, " @{}", line.0).unwrap();
                    if *k != 1 {
                        write!(out, " {k} *").unwrap();
                    }
                }
                PolItem::Axiom(lit, k) => {
                    out.push(' ');
                    pb::write_lit(names, *lit, out);
                    if *k != 1 {
                        write!(out, " {k} *").unwrap();
                    }
                }
                PolItem::Weaken(lit) => {
                    out.push(' ');
                    out.push_str(names.name(lit.var()));
                    out.push_str(" w");
                    continue;
                }
                PolItem::Divide(k) => {
                    write!(out, " {k} d").unwrap();
                    continue;
                }
                PolItem::Saturate => {
                    out.push_str(" s");
                    continue;
                }
            }
            operands += 1;
            if operands > 1 {
                out.push_str(" +");
            }
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

    /// `reason` implies at least one of `clause`, by RUP. For constraints
    /// whose reasoning involves their own encoding's variables (flags), which
    /// a [`Lit`] can't name. Returns the line, labelled, if one was written.
    fn rup(&mut self, _reason: &[Lit], _clause: &[PbLit]) -> Option<Line> {
        None
    }

    // The rest are for constraints that derive facts about their own
    // encoding with no reason: lines true everywhere, written once and
    // cited from then on. Only called while logging.

    /// `Σ aᵢxᵢ` over the variables' bits.
    fn linear(&self, _terms: &[(i64, VarId)]) -> Vec<(i128, PbLit)> {
        unreachable!("only called while logging")
    }

    /// A new flag named `name`, fully reified against `ineq` by two `red`
    /// steps labelled `name[r]` and `name[f]`.
    fn define_flag(&mut self, _name: String, _ineq: &Ineq) -> Flag {
        unreachable!("only called while logging")
    }

    /// The atom `x ≥ v`, defined if it isn't yet.
    fn ge_atom(&mut self, _x: VarId, _v: i64) -> GeAtom {
        unreachable!("only called while logging")
    }

    /// The least and greatest values `x`'s bits can represent, which may
    /// go beyond its declared bounds.
    fn bit_range(&self, _x: VarId) -> (i64, i64) {
        unreachable!("only called while logging")
    }

    /// `ineq`, by RUP, as a labelled line.
    fn rup_line(&mut self, _ineq: &Ineq) -> Line {
        unreachable!("only called while logging")
    }

    /// A labelled `pol` line.
    fn pol(&mut self, _pol: &Pol) -> Line {
        unreachable!("only called while logging")
    }

    /// Delete lines nothing will cite again, such as a step's helpers once
    /// the step is logged, so the checker carries fewer constraints.
    fn delete(&mut self, _lines: &[Line]) {}

    /// A comment in the proof.
    fn comment(&mut self, _text: &str) {}

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
