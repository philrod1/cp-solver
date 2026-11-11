//! Linear constraints `Σ aᵢxᵢ ≤ c`, `≥ c` and `= c`, by bounds propagation.
//!
//! Every relation becomes one or two `≤` propagators: `≥` negates
//! everything, and `=` is a `≤` plus a `≥`.

use std::collections::BTreeMap;

use super::{Constraint, PropagationContext, Propagator};
use crate::domain::Conflict;
use crate::engine::Engine;
use crate::model::VarId;
use crate::proof::{Ineq, Justification, NotEncodable, OpbEncoder, Reason};
use crate::store::Event;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Rel {
    Le,
    Eq,
}

/// `Σ aᵢxᵢ ≤ cof` or `Σ aᵢxᵢ = cof`, with terms as `(xᵢ, aᵢ)`, stored
/// normalised: each variable once, no zero coefficients, and coefficients
/// with no common factor.
#[derive(Clone, Debug)]
pub struct Linear {
    terms: Vec<(VarId, i64)>,
    rel: Rel,
    cof: i64,
}

impl Linear {
    /// `Σ aᵢxᵢ ≤ cof`, from `(xᵢ, aᵢ)` pairs.
    pub fn le(terms: &[(VarId, i64)], cof: i64) -> Self {
        Self::normalised(terms, Rel::Le, cof)
    }

    /// `Σ aᵢxᵢ ≥ cof`, stored as `Σ -aᵢxᵢ ≤ -cof`.
    pub fn ge(terms: &[(VarId, i64)], cof: i64) -> Self {
        let negated: Vec<(VarId, i64)> = terms.iter().map(|&(x, a)| (x, neg(a))).collect();
        Self::normalised(&negated, Rel::Le, neg(cof))
    }

    /// `Σ aᵢxᵢ = cof`
    pub fn eq(terms: &[(VarId, i64)], cof: i64) -> Self {
        Self::normalised(terms, Rel::Eq, cof)
    }

    fn normalised(terms: &[(VarId, i64)], rel: Rel, mut cof: i64) -> Self {
        // Merge repeated variables, `2x + 3x` to `5x`, then drop zeros.
        let mut by_var: BTreeMap<usize, (VarId, i64)> = BTreeMap::new();
        for &(x, a) in terms {
            let entry = by_var.entry(x.index()).or_insert((x, 0));
            entry.1 = entry.1.checked_add(a).expect("coefficient overflow");
        }
        let mut terms: Vec<(VarId, i64)> = by_var.into_values().filter(|&(_, a)| a != 0).collect();

        // Divide through by the common factor. For `≤` rounding down is
        // exact over the integers; for `=` a remainder means no solution.
        let g = terms.iter().fold(0, |g, &(_, a)| gcd(g, a.unsigned_abs()));
        if g > 1 {
            let g = i64::try_from(g).expect("coefficient overflow");
            match rel {
                Rel::Le => cof = floor_div(cof.into(), g.into()) as i64,
                Rel::Eq if cof % g != 0 => return Self::infeasible(),
                Rel::Eq => cof /= g,
            }
            for t in &mut terms {
                t.1 /= g;
            }
        }
        Self { terms, rel, cof }
    }

    /// `0 ≤ -1`, which fails as soon as it is propagated.
    fn infeasible() -> Self {
        Self {
            terms: Vec::new(),
            rel: Rel::Le,
            cof: -1,
        }
    }
}

impl Constraint for Linear {
    fn post(&self, engine: &mut Engine) {
        engine.add(Box::new(LessEqual::new(self.terms.clone(), self.cof)));
        if self.rel == Rel::Eq {
            let negated = self.terms.iter().map(|&(x, a)| (x, -a)).collect();
            engine.add(Box::new(LessEqual::new(negated, -self.cof)));
        }
    }

    /// As GCS writes it, in its normalised form:
    ///
    /// ```text
    /// @c[name][le]  sum ai xi <= cof
    /// @c[name][ge]  sum ai x1 >= cof   (equalities only)
    /// ```
    fn encode(&self, opb: &mut OpbEncoder<'_>) -> Result<(), NotEncodable> {
        let terms: Vec<(i64, VarId)> = self.terms.iter().map(|&(x, a)| (a, x)).collect();
        let sum = opb.linear(&terms);
        let cof = i128::from(self.cof);
        opb.row("le", &Ineq::le(sum.clone(), cof));
        if self.rel == Rel::Eq {
            opb.row("ge", &Ineq::ge(sum, cof));
        }
        Ok(())
    }
}

/// Bounds propagation for `Σ aᵢxᵢ ≤ cof`
struct LessEqual {
    terms: Vec<(VarId, i64)>,
    /// The variables of `terms`, for reasons.
    vars: Vec<VarId>,
    cof: i64,
    mins: Vec<i128>,
}

impl LessEqual {
    fn new(terms: Vec<(VarId, i64)>, cof: i64) -> Self {
        let mins = vec![0; terms.len()];
        let vars = terms.iter().map(|&(x, _)| x).collect();
        Self { terms, vars, cof, mins }
    }
}

impl Propagator for LessEqual {
    fn name(&self) -> &'static str {
        "linear_le"
    }

    fn watches(&self) -> Vec<(VarId, Event)> {
        self.terms
            .iter()
            .map(|&(x, _)| (x, Event::Bounds))
            .collect()
    }

    fn propagate(&mut self, ctx: &mut PropagationContext<'_>) -> Result<(), Conflict> {
        // i128 throughout because we can overflow i64
        let mut min_sum: i128 = 0;
        for (min, &(x, a)) in self.mins.iter_mut().zip(&self.terms) {
            let d = ctx.domain(x);
            let bound = if a > 0 { d.lower() } else { d.upper() };
            *min = i128::from(a) * i128::from(bound);
            min_sum += *min;
        }
        let why = Justification::Unchecked(Reason::Domains(&self.vars));
        let cof = i128::from(self.cof);
        if min_sum > cof {
            return ctx.fail(why);
        }

        // Under the direct encoding these need a `pol` derivation (sum the
        // constraint with the other variables' bounds), not plain RUP.
        // Unchecked until the proof writer can produce one.
        for (&min, &(x, a)) in self.mins.iter().zip(&self.terms) {
            let slack = cof - (min_sum - min); // the most aᵢxᵢ can be
            let a = i128::from(a);
            if a > 0 {
                ctx.set_upper(x, clamp(floor_div(slack, a)), why)?;
            } else {
                ctx.set_lower(x, clamp(ceil_div(slack, a)), why)?;
            }
        }
        Ok(())
    }
}

/// `⌊n / d⌋`. Rust's `/` rounds toward zero, which is wrong when the
/// signs differ: -7 / 2 is -3, but ⌊-3.5⌋ = -4.
fn floor_div(n: i128, d: i128) -> i128 {
    let q = n / d;
    if n % d != 0 && (n < 0) != (d < 0) {
        q - 1
    } else {
        q
    }
}

/// `⌈n / d⌉`
fn ceil_div(n: i128, d: i128) -> i128 {
    -floor_div(-n, d)
}

/// A bound outside i64 is beyond any domain, so clamping changes nothing.
fn clamp(v: i128) -> i64 {
    v.clamp(i64::MIN.into(), i64::MAX.into()) as i64
}

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

fn neg(v: i64) -> i64 {
    v.checked_neg().expect("coefficient overflow")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraints::testing::{propagate, values};
    use crate::model::Model;
    use proptest::prelude::*;

    #[test]
    fn division_rounds_the_right_way_for_every_sign() {
        assert_eq!((floor_div(7, 2), ceil_div(7, 2)), (3, 4));
        assert_eq!((floor_div(-7, 2), ceil_div(-7, 2)), (-4, -3));
        assert_eq!((floor_div(7, -2), ceil_div(7, -2)), (-4, -3));
        assert_eq!((floor_div(-7, -2), ceil_div(-7, -2)), (3, 4));
        assert_eq!((floor_div(6, -3), ceil_div(6, -3)), (-2, -2));
    }

    #[test]
    fn le_tightens_upper_bounds() {
        // x + y ≤ 5 with y ≥ 3 gives x ≤ 2; with x ≥ 0, y ≤ 5.
        let mut m = Model::new();
        let (x, y) = (m.int_var(0, 4), m.int_var(3, 9));
        m.post(Linear::le(&[(x, 1), (y, 1)], 5));
        let (s, r) = propagate(&m);
        assert_eq!(r, Ok(()));
        assert_eq!(values(&s, x), (0..=2).collect());
        assert_eq!(values(&s, y), (3..=5).collect());
    }

    #[test]
    fn negative_coefficients_tighten_lower_bounds() {
        // x - y ≤ -2 with x ≥ 0 gives y ≥ 2; with y ≤ 5, x ≤ 3.
        let mut m = Model::new();
        let (x, y) = (m.int_var(0, 9), m.int_var(0, 5));
        m.post(Linear::le(&[(x, 1), (y, -1)], -2));
        let (s, _) = propagate(&m);
        assert_eq!(values(&s, x), (0..=3).collect());
        assert_eq!(values(&s, y), (2..=5).collect());
    }

    #[test]
    fn bounds_round_inwards() {
        // 2x + 3y ≤ 10 gives x ≤ 5 and y ≤ 3 (not 3.33...).
        let mut m = Model::new();
        let (x, y) = (m.int_var(0, 9), m.int_var(0, 9));
        m.post(Linear::le(&[(x, 2), (y, 3)], 10));
        let (s, _) = propagate(&m);
        assert_eq!(s.domain(x).upper(), 5);
        assert_eq!(s.domain(y).upper(), 3);

        // 2x + 3y ≥ 7 with x ≤ 1 gives 3y ≥ 5, so y ≥ 2 (not 1.66...).
        let mut m = Model::new();
        let (x, y) = (m.int_var(0, 1), m.int_var(0, 9));
        m.post(Linear::ge(&[(x, 2), (y, 3)], 7));
        let (s, _) = propagate(&m);
        assert_eq!(s.domain(y).lower(), 2);
    }

    #[test]
    fn too_large_a_minimum_conflicts() {
        let mut m = Model::new();
        let (x, y) = (m.int_var(1, 5), m.int_var(1, 5));
        m.post(Linear::le(&[(x, 1), (y, 1)], 1));
        assert_eq!(propagate(&m).1, Err(Conflict));
    }

    #[test]
    fn eq_tightens_both_ways() {
        // x + y = 10 with x ≤ 4, y ≤ 7: x ≥ 3 and y ≥ 6.
        let mut m = Model::new();
        let (x, y) = (m.int_var(0, 4), m.int_var(0, 7));
        m.post(Linear::eq(&[(x, 1), (y, 1)], 10));
        let (s, r) = propagate(&m);
        assert_eq!(r, Ok(()));
        assert_eq!(values(&s, x), [3, 4].into());
        assert_eq!(values(&s, y), [6, 7].into());
    }

    #[test]
    fn normalising_merges_cancels_and_divides() {
        let mut m = Model::new();
        let (x, y) = (m.int_var(0, 5), m.int_var(0, 5));

        // x + x ≤ 3 is 2x ≤ 3, which divides to x ≤ 1.
        let c = Linear::le(&[(x, 1), (x, 1)], 3);
        assert_eq!((c.terms.as_slice(), c.cof), ([(x, 1)].as_slice(), 1));

        // x - x + y ≤ 2 is just y ≤ 2.
        let c = Linear::le(&[(x, 1), (x, -1), (y, 1)], 2);
        assert_eq!((c.terms.as_slice(), c.cof), ([(y, 1)].as_slice(), 2));

        m.post(Linear::le(&[(x, 1), (x, 1)], 3));
        let (s, _) = propagate(&m);
        assert_eq!(values(&s, x), [0, 1].into());
    }

    #[test]
    fn eq_with_indivisible_constant_is_infeasible() {
        // 2x + 4y = 5 has no integer solution.
        let mut m = Model::new();
        let (x, y) = (m.int_var(-9, 9), m.int_var(-9, 9));
        m.post(Linear::eq(&[(x, 2), (y, 4)], 5));
        assert_eq!(propagate(&m).1, Err(Conflict));
    }

    #[test]
    fn empty_sums() {
        let mut m = Model::new();
        m.post(Linear::le(&[], 0));
        assert_eq!(propagate(&m).1, Ok(()));
        let mut m = Model::new();
        m.post(Linear::le(&[], -1));
        assert_eq!(propagate(&m).1, Err(Conflict));
    }

    proptest! {
        /// Propagation must never remove a value that is part of a
        /// solution, and must only fail when there is no solution at all.
        /// Checked against brute force over every assignment.
        #[test]
        fn never_removes_a_solution(
            terms in prop::collection::vec((-3i64..=3, -3i64..=3, 0i64..=4), 1..=3),
            cof in -8i64..=8,
            is_eq in any::<bool>(),
        ) {
            let mut m = Model::new();
            let mut lin = Vec::new();
            let mut ranges = Vec::new();
            for &(a, lo, width) in &terms {
                let x = m.int_var(lo, lo + width);
                lin.push((x, a));
                ranges.push((x, lo, lo + width));
            }
            m.post(if is_eq { Linear::eq(&lin, cof) } else { Linear::le(&lin, cof) });
            let (s, result) = propagate(&m);

            // Odometer over every assignment of the original domains.
            let mut vals: Vec<i64> = ranges.iter().map(|&(_, lo, _)| lo).collect();
            loop {
                let sum: i64 = lin.iter().zip(&vals).map(|(&(_, a), &v)| a * v).sum();
                let satisfied = if is_eq { sum == cof } else { sum <= cof };
                if satisfied {
                    prop_assert!(result.is_ok(), "failed, but {vals:?} is a solution");
                    for (&(x, _, _), &v) in ranges.iter().zip(&vals) {
                        prop_assert!(s.domain(x).contains(v), "removed {v}, part of {vals:?}");
                    }
                }
                let Some(i) = (0..vals.len()).find(|&i| vals[i] < ranges[i].2) else {
                    break;
                };
                vals[i] += 1;
                for j in 0..i {
                    vals[j] = ranges[j].1;
                }
            }
        }

        /// The other direction: after propagating a single `≤`, the bound
        /// each term pushes on must be reachable, with the other terms at
        /// their smallest. Catches propagation that is correct but weak,
        /// such as rounding toward zero instead of inwards.
        #[test]
        fn le_bounds_are_tight(
            terms in prop::collection::vec((-3i64..=3, -3i64..=3, 0i64..=4), 1..=3),
            cof in -8i64..=8,
        ) {
            let mut m = Model::new();
            let lin: Vec<(VarId, i64)> = terms
                .iter()
                .map(|&(a, lo, width)| (m.int_var(lo, lo + width), a))
                .collect();
            let constraint = Linear::le(&lin, cof);
            let (norm, ncof) = (constraint.terms.clone(), constraint.cof);
            m.post(constraint);
            let (s, result) = propagate(&m);
            prop_assume!(result.is_ok());

            // Domains start as intervals and only lose bounds, so they stay
            // intervals: every value between the bounds is available.
            let min_of = |&(x, a): &(VarId, i64)| {
                let d = s.domain(x);
                a * if a > 0 { d.lower() } else { d.upper() }
            };
            let total: i64 = norm.iter().map(min_of).sum();
            for t @ &(x, a) in &norm {
                let rest = total - min_of(t);
                let d = s.domain(x);
                let pushed = if a > 0 { d.upper() } else { d.lower() };
                prop_assert!(a * pushed + rest <= ncof, "x{} = {pushed} is unreachable", x.index());
            }
        }
    }
}
