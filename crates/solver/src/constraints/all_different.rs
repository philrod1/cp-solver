//! AllDifferent: the terms `xᵢ + aᵢ` take pairwise distinct values.
//!
//! The propagator removes a fixed term's value from the others, and keeps
//! a maximum matching of terms to values. When no matching covers every
//! term, some k terms share fewer than k values (a Hall violator), and it
//! fails. The proof of a failure adds up "each of these terms takes one of
//! its values" and "at most one term takes each value": see
//! [`justify_violator`].

use std::collections::{HashMap, HashSet};

use super::{Constraint, PropagationContext, Propagator};
use crate::domain::Conflict;
use crate::engine::Engine;
use crate::lit::Lit;
use crate::model::VarId;
use crate::proof::{
    Ineq, Justification, Line, NotEncodable, OpbEncoder, PbLit, Pol, ProofLogger, Reason,
};
use crate::store::Event;

#[derive(Clone, Debug)]
pub struct AllDifferent {
    terms: Vec<(VarId, i64)>,
}

impl AllDifferent {
    pub fn new(terms: &[VarId]) -> Self {
        Self {
            terms: terms.iter().map(|&v| (v, 0)).collect(),
        }
    }

    pub fn with_offsets(terms: &[(VarId, i64)]) -> Self {
        Self {
            terms: terms.to_vec(),
        }
    }
}

impl Constraint for AllDifferent {
    fn post(&self, engine: &mut Engine) {
        let n = self.terms.len();
        let repeated = (0..n).any(|j| self.terms[..j].contains(&self.terms[j]));
        engine.add(Box::new(Prop {
            terms: self.terms.clone(),
            repeated,
            matched: vec![None; n],
            owner: HashMap::new(),
            at_most_one: HashMap::new(),
        }));
    }

    /// As GCS writes it: for each pair of terms `i < j`, a flag
    /// `x[name][i_j]` choosing which is bigger.
    ///
    /// ```text
    /// @c[name][{i}lt{j}]  !flag => (xi + ai) - (xj + aj) <= -1
    /// @c[name][{i}gt{j}]   flag => (xi + ai) - (xj + aj) >= 1
    /// ```
    fn encode(&self, opb: &mut OpbEncoder<'_>) -> Result<(), NotEncodable> {
        for (i, &(xi, ai)) in self.terms.iter().enumerate() {
            for (j, &(xj, aj)) in self.terms.iter().enumerate().skip(i + 1) {
                let flag = opb.indexed_flag(&[i, j]);
                let diff = opb.linear(&[(1, xi), (-1, xj)]);
                let shift = i128::from(aj) - i128::from(ai);
                opb.row(
                    &format!("{i}lt{j}"),
                    &Ineq::le(diff.clone(), -1 + shift).implied_by(!flag),
                );
                opb.row(
                    &format!("{i}gt{j}"),
                    &Ineq::ge(diff, 1 + shift).implied_by(flag),
                );
            }
        }
        Ok(())
    }
}

struct Prop {
    terms: Vec<(VarId, i64)>,
    /// Some term appears twice, so it would have to differ from itself.
    repeated: bool,
    /// The value, offset included, each term is matched to.
    matched: Vec<Option<i64>>,
    /// The term each matched value belongs to.
    owner: HashMap<i64, usize>,
    /// "At most one term takes this value", once the proof has it.
    at_most_one: HashMap<i64, Line>,
}

/// The terms a failed search for an augmenting path visited, and the
/// values it tried.
struct Visited {
    terms: Vec<bool>,
    values: HashSet<i64>,
}

impl Propagator for Prop {
    fn name(&self) -> &'static str {
        "all_different"
    }

    fn watches(&self) -> Vec<(VarId, Event)> {
        self.terms
            .iter()
            .map(|(v, _)| (*v, Event::Domain))
            .collect()
    }

    fn propagate(&mut self, ctx: &mut PropagationContext<'_>) -> Result<(), Conflict> {
        // Both of the pair's rows fail, whatever its flag.
        if self.repeated {
            return ctx.fail(Justification::Rup(Reason::Lits(&[])));
        }
        self.remove_fixed_values(ctx)?;
        self.match_every_term(ctx)
    }
}

impl Prop {
    fn remove_fixed_values(&self, ctx: &mut PropagationContext<'_>) -> Result<(), Conflict> {
        // Each removal is "at most one" so justified by RUP.
        for (i, &(xi, ai)) in self.terms.iter().enumerate() {
            let Some(v) = ctx.fixed_value(xi) else {
                continue;
            };
            let value = v + ai;
            for (j, &(xj, aj)) in self.terms.iter().enumerate() {
                if j != i {
                    let why = Justification::Rup(Reason::Lits(&[Lit::Eq(xi, v)]));
                    ctx.remove(xj, value - aj, why)?;
                }
            }
        }
        Ok(())
    }

    /// Repair the matching after domains have changed, or fail if no
    /// matching covers every term.
    fn match_every_term(&mut self, ctx: &mut PropagationContext<'_>) -> Result<(), Conflict> {
        for (i, &(x, a)) in self.terms.iter().enumerate() {
            if let Some(u) = self.matched[i]
                && !ctx.domain(x).contains(u - a)
            {
                self.matched[i] = None;
                self.owner.remove(&u);
            }
        }
        for i in 0..self.terms.len() {
            if self.matched[i].is_some() {
                continue;
            }
            let mut visited = Visited {
                terms: vec![false; self.terms.len()],
                values: HashSet::new(),
            };
            if !self.augment(ctx, i, &mut visited) {
                return self.fail(ctx, &visited);
            }
        }
        Ok(())
    }

    /// Match term `i`, moving other terms along an augmenting path if
    /// need be (Kuhn's algorithm).
    fn augment(&mut self, ctx: &PropagationContext<'_>, i: usize, visited: &mut Visited) -> bool {
        visited.terms[i] = true;
        let (x, a) = self.terms[i];
        let values: Vec<i64> = ctx.domain(x).iter().map(|v| v + a).collect();
        let free = values.iter().find(|u| !self.owner.contains_key(u));
        if let Some(&u) = free {
            self.assign(i, u);
            return true;
        }
        for u in values {
            if !visited.values.insert(u) {
                continue;
            }
            let j = self.owner[&u];
            if !visited.terms[j] && self.augment(ctx, j, visited) {
                self.assign(i, u);
                return true;
            }
        }
        false
    }

    fn assign(&mut self, i: usize, u: i64) {
        self.matched[i] = Some(u);
        self.owner.insert(u, i);
    }

    /// Fail on the Hall violator a failed augmentation found: the terms it
    /// visited can only take the values it tried, and there is one value
    /// fewer than terms.
    fn fail(
        &mut self,
        ctx: &mut PropagationContext<'_>,
        visited: &Visited,
    ) -> Result<(), Conflict> {
        let hall: Vec<usize> = (0..self.terms.len())
            .filter(|&i| visited.terms[i])
            .collect();
        let mut vars: Vec<VarId> = hall.iter().map(|&i| self.terms[i].0).collect();
        vars.sort_unstable_by_key(|x| x.index());
        vars.dedup();
        if !ctx.is_logging() {
            return ctx.fail(Justification::Rup(Reason::Domains(&vars)));
        }
        let mut values: Vec<i64> = visited.values.iter().copied().collect();
        values.sort_unstable();
        let helpers = justify_violator(ctx, &self.terms, &mut self.at_most_one, &hall, &values);
        let result = ctx.fail(Justification::Rup(Reason::Domains(&vars)));
        ctx.proof.delete(&helpers);
        result
    }
}

/// Lines from which the failure on Hall violator `hall` (term indices),
/// whose terms can only take `values`, follows by RUP from the terms'
/// domains. Returns the lines to delete once the failure is logged.
///
/// Adds up, for each Hall term, "it takes some value between its bounds",
/// and, for each value, "at most one term takes it". The Hall terms'
/// values cancel, leaving a line that needs at least |hall| − |values| ≥ 1
/// from values the domains rule out.
fn justify_violator(
    ctx: &mut PropagationContext<'_>,
    terms: &[(VarId, i64)],
    cache: &mut HashMap<i64, Line>,
    hall: &[usize],
    values: &[i64],
) -> Vec<Line> {
    let mut helpers = Vec::new();
    let mut sum = Pol::default();
    for &i in hall {
        let (x, _) = terms[i];
        let (lo, hi) = (ctx.domain(x).lower(), ctx.domain(x).upper());
        let line = at_least_one(ctx.proof, x, lo, hi);
        sum.add(&line, 1);
        helpers.push(line);
    }
    for &u in values {
        let amo = cache
            .entry(u)
            .or_insert_with(|| at_most_one(ctx.proof, terms, u));
        sum.add(amo, 1);
    }
    helpers.push(ctx.proof.pol(&sum));
    helpers
}

/// `x < lo ∨ x ≥ hi + 1 ∨ x = lo ∨ … ∨ x = hi`, by RUP: the equality atoms'
/// definitions walk the `≥` atoms up from `lo`.
fn at_least_one(proof: &mut dyn ProofLogger, x: VarId, lo: i64, hi: i64) -> Line {
    let mut lits: Vec<PbLit> = (lo..=hi).map(|v| proof.eq_atom(x, v)).collect();
    lits.push(!proof.ge_atom(x, lo).flag.lit);
    lits.push(proof.ge_atom(x, hi + 1).flag.lit);
    proof.rup_line(&Ineq::clause(lits))
}

/// "At most one term takes `u`", over the terms whose bits can represent
/// it, as `Σ ¬[xᵢ = u − aᵢ] ≥ k − 1`. Each pair is a clause, by RUP from the
/// pair's rows. Then for k = 3, 4, …, the line for the first k terms is
/// ((k − 2)·(the line for k − 1) + (the pairs with term k)) / (k − 1),
/// which rounds up to k − 1. Every line but the last is deleted.
fn at_most_one(proof: &mut dyn ProofLogger, terms: &[(VarId, i64)], u: i64) -> Line {
    let candidates: Vec<(VarId, i64)> = terms
        .iter()
        .copied()
        .filter(|&(x, a)| {
            let (lo, hi) = proof.bit_range(x);
            (lo..=hi).contains(&(u - a))
        })
        .collect();
    let lits: Vec<PbLit> = candidates
        .iter()
        .map(|&(x, a)| !proof.eq_atom(x, u - a))
        .collect();
    // A Hall value was tried by one Hall term while another held it.
    assert!(lits.len() >= 2, "only one term can take {u}");
    let mut helpers = Vec::new();
    let mut line = proof.rup_line(&Ineq::clause([lits[0], lits[1]]));
    for k in 3..=lits.len() as i128 {
        let new = lits[k as usize - 1];
        let mut pol = Pol::default();
        pol.add(&line, k - 2);
        helpers.push(line);
        for &old in &lits[..k as usize - 1] {
            let pair = proof.rup_line(&Ineq::clause([old, new]));
            pol.add(&pair, 1);
            helpers.push(pair);
        }
        pol.divide(k - 1);
        line = proof.pol(&pol);
    }
    proof.delete(&helpers);
    line
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::AllDifferent;
    use crate::constraints::testing::{propagate, values};
    use crate::domain::Conflict;
    use crate::model::{Model, VarId};

    #[test]
    fn fixed_value_is_removed_from_all_others() {
        let mut m = Model::new();
        let x = m.int_var(2, 2);
        let others: Vec<_> = (0..3).map(|_| m.int_var(0, 4)).collect();
        m.post(AllDifferent::new(&[x, others[0], others[1], others[2]]));
        let (s, r) = propagate(&m);
        assert_eq!(r, Ok(()));
        for &v in &others {
            assert_eq!(values(&s, v), [0, 1, 3, 4].into());
        }
    }

    #[test]
    fn offsets_shift_the_removed_value() {
        // x + 0 = 3, so y + 2 != 3 means y != 1.
        let mut m = Model::new();
        let (x, y) = (m.int_var(3, 3), m.int_var(0, 3));
        m.post(AllDifferent::with_offsets(&[(x, 0), (y, 2)]));
        let (s, _) = propagate(&m);
        assert_eq!(values(&s, y), [0, 2, 3].into());
    }

    #[test]
    fn removals_cascade() {
        // x = 0 leaves y = 1, which leaves z = 2.
        let mut m = Model::new();
        let (x, y, z) = (m.int_var(0, 0), m.int_var(0, 1), m.int_var(0, 2));
        m.post(AllDifferent::new(&[x, y, z]));
        let (s, r) = propagate(&m);
        assert_eq!(r, Ok(()));
        assert_eq!(s.domain(y).fixed_value(), Some(1));
        assert_eq!(s.domain(z).fixed_value(), Some(2));
    }

    #[test]
    fn two_equal_fixed_values_conflict() {
        let mut m = Model::new();
        let (x, y, z) = (m.int_var(1, 1), m.int_var(0, 5), m.int_var(1, 1));
        m.post(AllDifferent::new(&[x, y, z]));
        assert_eq!(propagate(&m).1, Err(Conflict));
    }

    #[test]
    fn repeated_term_conflicts_at_root() {
        let mut m = Model::new();
        let (x, y) = (m.int_var(0, 4), m.int_var(0, 4));
        m.post(AllDifferent::new(&[x, y, x]));
        assert_eq!(propagate(&m).1, Err(Conflict));
    }

    #[test]
    fn repeated_variable_with_different_offsets_is_fine() {
        let mut m = Model::new();
        let x = m.int_var(0, 1);
        m.post(AllDifferent::with_offsets(&[(x, 0), (x, 1)]));
        assert_eq!(propagate(&m).1, Ok(()));
    }

    #[test]
    fn pigeonhole_fails_at_root() {
        let mut m = Model::new();
        let v: Vec<_> = (0..3).map(|_| m.int_var(0, 1)).collect();
        m.post(AllDifferent::new(&v));
        assert_eq!(propagate(&m).1, Err(Conflict));
    }

    #[test]
    fn violator_among_wider_domains_fails() {
        // x, y, z share {1, 2}; w could take anything.
        let mut m = Model::new();
        let w = m.int_var(1, 5);
        let v: Vec<_> = (0..3).map(|_| m.int_var(1, 2)).collect();
        m.post(AllDifferent::new(&[w, v[0], v[1], v[2]]));
        assert_eq!(propagate(&m).1, Err(Conflict));
    }

    #[test]
    fn offsets_can_make_a_pigeonhole() {
        // x ∈ {0, 1}, y + 1 ∈ {1, 2}, z + 2 ∈ {1, 2}: three terms, two values.
        let mut m = Model::new();
        let (x, y, z) = (m.int_var(0, 1), m.int_var(0, 1), m.int_var(-1, 0));
        m.post(AllDifferent::with_offsets(&[(x, 1), (y, 1), (z, 2)]));
        assert_eq!(propagate(&m).1, Err(Conflict));
    }

    #[test]
    fn a_full_matching_is_not_a_failure() {
        let mut m = Model::new();
        let (x, y, z) = (m.int_var(1, 2), m.int_var(1, 2), m.int_var(1, 3));
        m.post(AllDifferent::new(&[x, y, z]));
        let (s, r) = propagate(&m);
        assert_eq!(r, Ok(()));
        // Step 1 only fails: z = 3 is left to search.
        assert_eq!(values(&s, z), [1, 2, 3].into());
    }

    proptest! {
        #[test]
        fn fails_at_root_exactly_when_unsatisfiable(
            terms in prop::collection::vec(
                ((-2i64..=2, 0i64..=2).prop_map(|(lo, w)| (lo, lo + w)), -2i64..=2),
                2..=5,
            ),
        ) {
            // Distinct variables, so by Hall's theorem a matching exists
            // exactly when a solution does.
            let mut m = Model::new();
            let vars: Vec<(VarId, i64)> =
                terms.iter().map(|&((lo, hi), a)| (m.int_var(lo, hi), a)).collect();
            m.post(AllDifferent::with_offsets(&vars));
            let mut values: Vec<Vec<i64>> = vec![vec![]];
            for &((lo, hi), a) in &terms {
                values = values
                    .into_iter()
                    .flat_map(|p| (lo..=hi).map(move |v| [p.clone(), vec![v + a]].concat()))
                    .collect();
            }
            let satisfiable = values
                .iter()
                .any(|p| p.iter().enumerate().all(|(k, u)| !p[..k].contains(u)));
            prop_assert_eq!(propagate(&m).1.is_ok(), satisfiable);
        }
    }
}
