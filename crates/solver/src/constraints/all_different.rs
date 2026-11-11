use super::{Constraint, PropagationContext, Propagator};
use crate::domain::Conflict;
use crate::engine::Engine;
use crate::lit::Lit;
use crate::model::VarId;
use crate::proof::{Ineq, Justification, NotEncodable, OpbEncoder, Reason};
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
        engine.add(Box::new(Prop {
            terms: self.terms.clone(),
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
                opb.row(&format!("{i}lt{j}"), &Ineq::le(diff.clone(), -1 + shift).implied_by(!flag));
                opb.row(&format!("{i}gt{j}"), &Ineq::ge(diff, 1 + shift).implied_by(flag));
            }
        }
        Ok(())
    }
}

struct Prop {
    terms: Vec<(VarId, i64)>,
}

impl Propagator for Prop {
    fn name(&self) -> &'static str {
        "all_different"
    }

    fn watches(&self) -> Vec<(VarId, Event)> {
        self.terms.iter().map(|(v, _)| (*v, Event::Fix)).collect()
    }

    fn propagate(&mut self, ctx: &mut PropagationContext<'_>) -> Result<(), Conflict> {
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
}

#[cfg(test)]
mod tests {
    use super::AllDifferent;
    use crate::constraints::testing::{propagate, values};
    use crate::domain::Conflict;
    use crate::model::Model;

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
    fn repeated_variable_with_equal_offsets_conflicts_once_fixed() {
        let mut m = Model::new();
        let x = m.int_var(4, 4);
        m.post(AllDifferent::new(&[x, x]));
        assert_eq!(propagate(&m).1, Err(Conflict));
    }

    #[test]
    fn value_elimination_misses_pigeonhole_at_root() {
        // Three terms, two values: unsatisfiable, but nothing is fixed, so
        // value elimination does nothing. Search finds the conflict instead.
        // A matching-based propagator would fail here at the root: when it
        // does, flip this assertion.
        let mut m = Model::new();
        let v: Vec<_> = (0..3).map(|_| m.int_var(0, 1)).collect();
        m.post(AllDifferent::new(&v));
        assert_eq!(propagate(&m).1, Ok(()));
    }
}
