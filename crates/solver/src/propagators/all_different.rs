use super::{PropagationContext, Propagator};
use crate::domain::Conflict;
use crate::model::VarId;
use crate::proof::Justification;
use crate::store::Event;

pub struct AllDifferent {
    terms: Vec<(VarId, i64)>,
}

impl AllDifferent {
    pub fn new(terms: Vec<(VarId, i64)>) -> Self {
        Self { terms }
    }
}

impl Propagator for AllDifferent {
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
                    ctx.remove(xj, value - aj, Justification::Rup)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::domain::Conflict;
    use crate::engine::Engine;
    use crate::model::{Model, VarId};
    use crate::proof::NullLogger;
    use crate::propagators::post;
    use crate::store::DomainStore;
    use std::collections::BTreeSet;

    fn propagate(model: &Model) -> (DomainStore, Result<(), Conflict>) {
        let mut store = DomainStore::new(model);
        let mut engine = Engine::new(model.num_vars());
        for c in model.constraints() {
            post(c, &mut engine);
        }
        let result = engine.propagate(&mut store, &mut NullLogger);
        (store, result)
    }

    fn values(s: &DomainStore, v: VarId) -> BTreeSet<i64> {
        s.domain(v).iter().collect()
    }

    #[test]
    fn fixed_value_is_removed_from_all_others() {
        let mut m = Model::new();
        let x = m.int_var(2, 2);
        let others: Vec<_> = (0..3).map(|_| m.int_var(0, 4)).collect();
        m.all_different(&[x, others[0], others[1], others[2]]);
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
        m.all_different_offset(&[(x, 0), (y, 2)]);
        let (s, _) = propagate(&m);
        assert_eq!(values(&s, y), [0, 2, 3].into());
    }

    #[test]
    fn removals_cascade() {
        // x = 0 leaves y = 1, which leaves z = 2.
        let mut m = Model::new();
        let (x, y, z) = (m.int_var(0, 0), m.int_var(0, 1), m.int_var(0, 2));
        m.all_different(&[x, y, z]);
        let (s, r) = propagate(&m);
        assert_eq!(r, Ok(()));
        assert_eq!(s.domain(y).fixed_value(), Some(1));
        assert_eq!(s.domain(z).fixed_value(), Some(2));
    }

    #[test]
    fn two_equal_fixed_values_conflict() {
        let mut m = Model::new();
        let (x, y, z) = (m.int_var(1, 1), m.int_var(0, 5), m.int_var(1, 1));
        m.all_different(&[x, y, z]);
        assert_eq!(propagate(&m).1, Err(Conflict));
    }

    #[test]
    fn repeated_variable_with_equal_offsets_conflicts_once_fixed() {
        let mut m = Model::new();
        let x = m.int_var(4, 4);
        m.all_different(&[x, x]);
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
        m.all_different(&v);
        assert_eq!(propagate(&m).1, Ok(()));
    }
}
