//! Minimum and maximum: `result` is the least, or the greatest, of some
//! variables.
//!
//! The propagator follows the Glasgow Constraint Solver's: bounds both
//! ways between `result` and the variables, values of `result` no variable
//! can take, a variable that is the only one left to supply `result`, and
//! values of a variable that can be neither the extremum nor beyond one
//! some other variable supplies. That makes it domain consistent. The
//! encoding is GCS's too; see [`MinMax::encode`].

use std::sync::{Arc, Mutex};

use super::{Constraint, PropagationContext, Propagator};
use crate::domain::Conflict;
use crate::engine::Engine;
use crate::lit::Lit;
use crate::model::VarId;
use crate::proof::{Ineq, Justification, Line, NotEncodable, OpbEncoder, PbLit, Pol, Reason};
use crate::store::Event;

/// What the encoding wrote, for the proof steps that cite it: shared by
/// the constraint, which writes it, and the propagator. Empty when no
/// proof is being written.
type Bridge = Arc<Mutex<Option<Encoded>>>;

#[derive(Debug)]
struct Encoded {
    /// Per variable, the row "it is on the far side of `result`".
    rows: Vec<Line>,
    /// Per variable, its selector: "it is `result`".
    selectors: Vec<PbLit>,
}

#[derive(Clone, Debug)]
pub struct MinMax {
    vars: Vec<VarId>,
    result: VarId,
    /// The least, rather than the greatest.
    min: bool,
    bridge: Bridge,
}

impl MinMax {
    /// `result` is the least of `vars`. With no variables, nothing is.
    pub fn min(vars: &[VarId], result: VarId) -> Self {
        Self::new(vars, result, true)
    }

    /// `result` is the greatest of `vars`. With no variables, nothing is.
    pub fn max(vars: &[VarId], result: VarId) -> Self {
        Self::new(vars, result, false)
    }

    fn new(vars: &[VarId], result: VarId, min: bool) -> Self {
        Self {
            vars: vars.to_vec(),
            result,
            min,
            bridge: Bridge::default(),
        }
    }
}

impl Constraint for MinMax {
    fn post(&self, engine: &mut Engine) {
        engine.add(Box::new(Prop {
            vars: self.vars.clone(),
            result: self.result,
            min: self.min,
            bridge: Arc::clone(&self.bridge),
        }));
    }

    /// As GCS writes it, for a minimum (a maximum swaps the signs):
    ///
    /// ```text
    /// @c[name][bound_i]   xᵢ − result ≥ 0           each variable is at least result
    /// @x[name][i][r]      x[name][i] ⇒ xᵢ − result ≤ 0
    /// @x[name][i][f]      ¬x[name][i] ⇒ xᵢ − result ≥ 1
    /// @c[name][al1]       Σ x[name][i] ≥ 1           some variable is result
    /// ```
    ///
    /// with the selectors `x[name][i]` named as CakePB-CP names them.
    fn encode(&self, opb: &mut OpbEncoder<'_>) -> Result<(), NotEncodable> {
        let sign = if self.min { 1 } else { -1 };
        let gap = |opb: &OpbEncoder<'_>, x: VarId| opb.linear(&[(sign, x), (-sign, self.result)]);
        let mut rows = Vec::new();
        for (i, &x) in self.vars.iter().enumerate() {
            let role = format!("bound_{i}");
            opb.row(&role, &Ineq::ge(gap(opb, x), 0));
            rows.push(Line::row(opb.constraint_name(), &role));
        }
        let selectors: Vec<PbLit> = self
            .vars
            .iter()
            .enumerate()
            .map(|(i, &x)| opb.reified_flag(&[i], Ineq::le(gap(opb, x), 0)))
            .collect();
        opb.row("al1", &Ineq::clause(selectors.iter().copied()));
        *self.bridge.lock().unwrap() = Some(Encoded { rows, selectors });
        Ok(())
    }
}

struct Prop {
    vars: Vec<VarId>,
    result: VarId,
    min: bool,
    bridge: Bridge,
}

impl Prop {
    /// Whether `a` is beyond `b` on the extremum's side: below it for a
    /// minimum, above it for a maximum.
    fn beyond(&self, a: i64, b: i64) -> bool {
        if self.min { a < b } else { a > b }
    }

    /// Every variable of the constraint, for a reason.
    fn scope(&self) -> Vec<VarId> {
        let mut scope = self.vars.clone();
        scope.push(self.result);
        scope
    }

    /// Rule 1: `result` is at least as far towards the extremum as each
    /// variable's near bound, and each variable at most as far as `result`'s.
    /// For a minimum: `result ≤ ub(xᵢ)` and `xᵢ ≥ lb(result)`. Each crosses
    /// variable i's row, so each is a `pol` of the row with the reason's
    /// bound, then RUP, as `Linear` does it.
    fn bounds(
        &self,
        ctx: &mut PropagationContext<'_>,
        enc: Option<&Encoded>,
    ) -> Result<(), Conflict> {
        for (i, &x) in self.vars.iter().enumerate() {
            let r = self.result;
            // result ≤ ub(x) for a minimum, ≥ lb(x) for a maximum.
            let (known, conclusion) = if self.min {
                let ub = ctx.domain(x).upper();
                (Lit::Lt(x, ub + 1), Lit::Lt(r, ub + 1))
            } else {
                let lb = ctx.domain(x).lower();
                (Lit::Ge(x, lb), Lit::Ge(r, lb))
            };
            self.step(ctx, enc, i, known, conclusion)?;
            // x ≥ lb(result) for a minimum, ≤ ub(result) for a maximum.
            let (known, conclusion) = if self.min {
                let lb = ctx.domain(r).lower();
                (Lit::Ge(r, lb), Lit::Ge(x, lb))
            } else {
                let ub = ctx.domain(r).upper();
                (Lit::Lt(r, ub + 1), Lit::Lt(x, ub + 1))
            };
            self.step(ctx, enc, i, known, conclusion)?;
        }
        Ok(())
    }

    /// Infer `conclusion` from `known` across variable i's row, if it
    /// tightens anything.
    fn step(
        &self,
        ctx: &mut PropagationContext<'_>,
        enc: Option<&Encoded>,
        i: usize,
        known: Lit,
        conclusion: Lit,
    ) -> Result<(), Conflict> {
        let tightens = match conclusion {
            Lit::Lt(y, v) => ctx.domain(y).upper() >= v,
            Lit::Ge(y, v) => ctx.domain(y).lower() < v,
            _ => unreachable!("bounds only"),
        };
        if !tightens {
            return Ok(());
        }
        let helper = enc.map(|enc| {
            let half = match known {
                Lit::Ge(y, v) => ctx.proof.ge_atom(y, v).flag.implies, // y ≥ v ⇒ Σ bits ≥ v
                Lit::Lt(y, v) => ctx.proof.ge_atom(y, v).flag.implied_by, // y < v ⇒ Σ bits ≤ v − 1
                _ => unreachable!("bounds only"),
            };
            let mut pol = Pol::default();
            pol.add(&enc.rows[i], 1).add(&half, 1);
            ctx.proof.pol(&pol)
        });
        let why = Justification::Rup(Reason::Lits(&[known]));
        let result = match conclusion {
            Lit::Lt(y, v) => ctx.set_upper(y, v - 1, why),
            Lit::Ge(y, v) => ctx.set_lower(y, v, why),
            _ => unreachable!("bounds only"),
        };
        ctx.proof.delete(helper.as_slice());
        result
    }

    /// Rule 2: remove each value of `result` no variable can take. Assume
    /// `result` is it: no selector can be true, one helper each, and `al1`
    /// fails.
    fn result_support(
        &self,
        ctx: &mut PropagationContext<'_>,
        enc: Option<&Encoded>,
    ) -> Result<(), Conflict> {
        let values: Vec<i64> = ctx.domain(self.result).iter().collect();
        for r in values {
            if self.vars.iter().any(|&x| ctx.domain(x).contains(r)) {
                continue;
            }
            let reason: Vec<Lit> = self.vars.iter().map(|&x| Lit::Neq(x, r)).collect();
            let mut helpers = Vec::new();
            if let Some(enc) = enc {
                let assumed = [reason.as_slice(), &[Lit::Eq(self.result, r)]].concat();
                for &selector in &enc.selectors {
                    helpers.extend(ctx.rup(&assumed, &[!selector]));
                }
            }
            let result = ctx.remove(self.result, r, Justification::Rup(Reason::Lits(&reason)));
            ctx.proof.delete(&helpers);
            result?;
        }
        Ok(())
    }

    /// Rule 3: if only one variable shares a value with `result`, it must
    /// be `result`, so it loses every value `result` doesn't have. Every
    /// other selector is false: for each value of `result`, one helper
    /// each, then the selector itself. Then `al1` makes the one variable
    /// equal to `result`.
    fn single_support(
        &self,
        ctx: &mut PropagationContext<'_>,
        enc: Option<&Encoded>,
    ) -> Result<(), Conflict> {
        let r = self.result;
        let meets = |ctx: &PropagationContext<'_>, x: VarId| {
            ctx.domain(x).iter().any(|v| ctx.domain(r).contains(v))
        };
        let supporters: Vec<usize> = (0..self.vars.len())
            .filter(|&i| meets(ctx, self.vars[i]))
            .collect();
        let [k] = supporters[..] else {
            return Ok(());
        };
        let x = self.vars[k];
        let unshared: Vec<i64> = ctx
            .domain(x)
            .iter()
            .filter(|&v| !ctx.domain(r).contains(v))
            .collect();
        if unshared.is_empty() {
            return Ok(());
        }
        let results: Vec<i64> = ctx.domain(r).iter().collect();
        let mut reason = ctx.reason_lits(Reason::Domains(&[r]));
        for (i, &y) in self.vars.iter().enumerate() {
            if i != k {
                reason.extend(results.iter().map(|&v| Lit::Neq(y, v)));
            }
        }
        let mut helpers = Vec::new();
        if let Some(enc) = enc {
            for (i, &selector) in enc.selectors.iter().enumerate() {
                if i == k {
                    continue;
                }
                for &v in &results {
                    let assumed = [reason.as_slice(), &[Lit::Eq(r, v)]].concat();
                    helpers.extend(ctx.rup(&assumed, &[!selector]));
                }
                helpers.extend(ctx.rup(&reason, &[!selector]));
            }
        }
        let mut result = Ok(());
        for w in unshared {
            result = ctx.remove(x, w, Justification::Rup(Reason::Lits(&reason)));
            if result.is_err() {
                break;
            }
        }
        ctx.proof.delete(&helpers);
        result
    }

    /// Rule 4: remove each value v of a variable that can neither be the
    /// extremum (`result` can't be v, or some other variable can't reach
    /// v) nor lie beyond one some other variable supplies. For each value
    /// r of `result` beyond v: with xᵢ = v and `result` = r, no selector can
    /// be true, one helper each, so they can't both hold. Then xᵢ = v leaves
    /// `result` only v, which fails.
    fn variable_support(
        &self,
        ctx: &mut PropagationContext<'_>,
        enc: Option<&Encoded>,
    ) -> Result<(), Conflict> {
        let r = self.result;
        for (i, &x) in self.vars.iter().enumerate() {
            // How far towards the extremum every other variable can reach.
            let limit = self
                .vars
                .iter()
                .enumerate()
                .filter(|&(k, _)| k != i)
                .map(|(_, &y)| {
                    if self.min {
                        ctx.domain(y).upper()
                    } else {
                        ctx.domain(y).lower()
                    }
                })
                .reduce(|a, b| if self.beyond(a, b) { a } else { b });
            let within = |v: i64| limit.is_none_or(|l| !self.beyond(l, v));
            // The furthest value of `result` some other variable can supply.
            let other_extreme = ctx
                .domain(r)
                .iter()
                .filter(|&v| within(v))
                .filter(|&v| {
                    self.vars
                        .iter()
                        .enumerate()
                        .any(|(k, &y)| k != i && ctx.domain(y).contains(v))
                })
                .reduce(|a, b| if self.beyond(a, b) { a } else { b });
            let values: Vec<i64> = ctx.domain(x).iter().collect();
            for v in values {
                let as_extreme = ctx.domain(r).contains(v) && within(v);
                let past_another = other_extreme.is_some_and(|e| self.beyond(e, v));
                if as_extreme || past_another || !ctx.domain(x).contains(v) {
                    continue;
                }
                let reason = ctx.reason_lits(Reason::Domains(&self.scope()));
                let mut helpers = Vec::new();
                if let Some(enc) = enc {
                    let beyond: Vec<i64> = ctx
                        .domain(r)
                        .iter()
                        .filter(|&w| self.beyond(w, v))
                        .collect();
                    for w in beyond {
                        let assumed = [reason.as_slice(), &[Lit::Eq(x, v), Lit::Eq(r, w)]].concat();
                        for &selector in &enc.selectors {
                            helpers.extend(ctx.rup(&assumed, &[!selector]));
                        }
                        helpers.extend(ctx.rup(&assumed, &[]));
                    }
                }
                let result = ctx.remove(x, v, Justification::Rup(Reason::Lits(&reason)));
                ctx.proof.delete(&helpers);
                result?;
            }
        }
        Ok(())
    }
}

impl Propagator for Prop {
    fn name(&self) -> &'static str {
        if self.min { "array_min" } else { "array_max" }
    }

    fn watches(&self) -> Vec<(VarId, Event)> {
        self.scope()
            .into_iter()
            .map(|x| (x, Event::Domain))
            .collect()
    }

    fn propagate(&mut self, ctx: &mut PropagationContext<'_>) -> Result<(), Conflict> {
        let bridge = Arc::clone(&self.bridge);
        let encoded = bridge.lock().unwrap();
        // No encoding means no proof is being written.
        let enc = encoded.as_ref().filter(|_| ctx.is_logging());
        if self.vars.is_empty() {
            // Nothing to be the extremum: the `al1` row is empty.
            return ctx.fail(Justification::Rup(Reason::Lits(&[])));
        }
        self.bounds(ctx, enc)?;
        self.result_support(ctx, enc)?;
        self.single_support(ctx, enc)?;
        self.variable_support(ctx, enc)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    use std::ops::ControlFlow;

    use proptest::prelude::*;

    use super::*;
    use crate::constraints::testing::{propagate, values};
    use crate::{Config, Model, enumerate};

    #[test]
    fn bounds_both_ways() {
        // r = min(x, y), x in 2..=5, y in 3..=9, r in 0..=9: r ≤ 5 and
        // r ≥ 2, so x, y ≥ 2 already; and r can only be 2..=5.
        let mut m = Model::new();
        let (x, y, r) = (m.int_var(2, 5), m.int_var(3, 9), m.int_var(0, 9));
        m.post(MinMax::min(&[x, y], r));
        let (store, result) = propagate(&m);
        assert!(result.is_ok());
        assert_eq!(values(&store, r), BTreeSet::from([2, 3, 4, 5]));
        // y can't be the minimum above 5, but can sit above x's minimum.
        assert_eq!(values(&store, y).len(), 7);
    }

    #[test]
    fn a_value_no_variable_has() {
        // r = max(x, y) with x, y in {1, 3}: r can't be 2.
        let mut m = Model::new();
        let (x, y) = (m.int_var(1, 3), m.int_var(1, 3));
        let r = m.int_var(0, 4);
        for v in [x, y] {
            let two = m.constant(2);
            m.post(crate::NotEqual::new(v, two));
        }
        m.post(MinMax::max(&[x, y], r));
        let (store, result) = propagate(&m);
        assert!(result.is_ok());
        assert_eq!(values(&store, r), BTreeSet::from([1, 3]));
    }

    #[test]
    fn the_only_support_must_be_the_result() {
        // r = min(x, y), r in {1, 2}, y in 5..=7 can't meet r: x = r.
        let mut m = Model::new();
        let (x, y, r) = (m.int_var(0, 4), m.int_var(5, 7), m.int_var(1, 2));
        m.post(MinMax::min(&[x, y], r));
        let (store, result) = propagate(&m);
        assert!(result.is_ok());
        assert_eq!(values(&store, x), BTreeSet::from([1, 2]));
    }

    #[test]
    fn no_variables_fails() {
        let mut m = Model::new();
        let r = m.int_var(0, 1);
        m.post(MinMax::min(&[], r));
        assert!(propagate(&m).1.is_err());
    }

    /// Every assignment to the variables, then `result`, as (vars, result).
    fn brute_force(domains: &[(i64, i64)], min: bool) -> Vec<Vec<i64>> {
        let mut all: Vec<Vec<i64>> = vec![vec![]];
        for &(lo, hi) in domains {
            all = all
                .into_iter()
                .flat_map(|a| (lo..=hi).map(move |v| [a.clone(), vec![v]].concat()))
                .collect();
        }
        all.into_iter()
            .filter(|a| {
                let (vars, r) = a.split_at(a.len() - 1);
                let extreme = if min {
                    vars.iter().min()
                } else {
                    vars.iter().max()
                };
                extreme == Some(&r[0])
            })
            .collect()
    }

    proptest! {
        #[test]
        fn finds_exactly_the_right_assignments(
            domains in prop::collection::vec((-2i64..=2, 0i64..=3).prop_map(|(lo, w)| (lo, lo + w)), 2..=4),
            min: bool,
        ) {
            // The last domain is result's.
            let mut m = Model::new();
            let all: Vec<VarId> = domains.iter().map(|&(lo, hi)| m.int_var(lo, hi)).collect();
            let (vars, result) = all.split_at(all.len() - 1);
            m.post(if min { MinMax::min(vars, result[0]) } else { MinMax::max(vars, result[0]) });
            let mut found = Vec::new();
            enumerate(&m, &Config::default(), |sol| {
                found.push(all.iter().map(|&v| sol.value(v)).collect::<Vec<i64>>());
                ControlFlow::Continue(())
            })
            .unwrap();
            found.sort();
            let mut expected = brute_force(&domains, min);
            expected.sort();
            prop_assert_eq!(found, expected);
        }

        #[test]
        fn propagation_is_domain_consistent(
            domains in prop::collection::vec((-2i64..=2, 0i64..=3).prop_map(|(lo, w)| (lo, lo + w)), 2..=4),
            min: bool,
        ) {
            // At the root, every value left takes part in some solution.
            let mut m = Model::new();
            let all: Vec<VarId> = domains.iter().map(|&(lo, hi)| m.int_var(lo, hi)).collect();
            let (vars, result) = all.split_at(all.len() - 1);
            m.post(if min { MinMax::min(vars, result[0]) } else { MinMax::max(vars, result[0]) });
            let solutions = brute_force(&domains, min);
            let (store, outcome) = propagate(&m);
            prop_assert_eq!(outcome.is_err(), solutions.is_empty());
            if outcome.is_ok() {
                for (j, &v) in all.iter().enumerate() {
                    for value in values(&store, v) {
                        prop_assert!(solutions.iter().any(|s| s[j] == value), "{} of variable {}", value, j);
                    }
                }
            }
        }
    }
}
