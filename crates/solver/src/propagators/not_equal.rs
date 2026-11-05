use super::{PropagationContext, Propagator};
use crate::domain::Conflict;
use crate::model::VarId;
use crate::proof::Justification;
use crate::store::Event;

pub struct NotEqual {
    x: VarId,
    y: VarId,
    x_offset: i64,
    y_offset: i64,
}

impl NotEqual {
    pub fn new(x: VarId, x_offset: i64, y: VarId, y_offset: i64) -> Self {
        Self {
            x,
            y,
            x_offset,
            y_offset,
        }
    }
}

impl Propagator for NotEqual {
    fn name(&self) -> &'static str {
        "not_equal"
    }

    /// Wake the propagator when either variable becomes fixed
    fn watches(&self) -> Vec<(VarId, Event)> {
        vec![(self.x, Event::Fix), (self.y, Event::Fix)]
    }

    fn propagate(&mut self, ctx: &mut PropagationContext<'_>) -> Result<(), Conflict> {
        if self.x == self.y {
            return if self.x_offset == self.y_offset {
                Err(Conflict)
            } else {
                Ok(())
            };
        }
        // Each removal is unit propagation on one clause so it is justified by RUP.
        if let Some(vx) = ctx.fixed_value(self.x) {
            ctx.remove(
                self.y,
                vx + self.x_offset - self.y_offset,
                Justification::Rup,
            )?;
        }
        if let Some(vy) = ctx.fixed_value(self.y) {
            ctx.remove(
                self.x,
                vy + self.y_offset - self.x_offset,
                Justification::Rup,
            )?;
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

    /// Post the model's constraints and propagate to a fixpoint.
    fn setup(model: &Model) -> (DomainStore, Engine) {
        let store = DomainStore::new(model);
        let mut engine = Engine::new(model.num_vars());
        for c in model.constraints() {
            post(c, &mut engine);
        }
        (store, engine)
    }

    fn values(s: &DomainStore, v: VarId) -> BTreeSet<i64> {
        s.domain(v).iter().collect()
    }

    #[test]
    fn nothing_to_do_until_a_side_is_fixed() {
        let mut m = Model::new();
        let (x, y) = (m.int_var(0, 3), m.int_var(0, 3));
        m.not_equal(x, y);
        let (mut s, mut e) = setup(&m);
        assert_eq!(e.propagate(&mut s, &mut NullLogger), Ok(()));
        assert_eq!(values(&s, y), (0..=3).collect());
    }

    #[test]
    fn fixed_side_removes_value_from_other() {
        let mut m = Model::new();
        let (x, y) = (m.int_var(2, 2), m.int_var(0, 3));
        m.not_equal(x, y);
        let (mut s, mut e) = setup(&m);
        e.propagate(&mut s, &mut NullLogger).unwrap();
        assert_eq!(values(&s, y), [0, 1, 3].into());
    }

    #[test]
    fn offsets_shift_the_removed_value() {
        // x + 1 != y + 3 with x = 4 means y != 2.
        let mut m = Model::new();
        let (x, y) = (m.int_var(4, 4), m.int_var(0, 3));
        m.not_equal_offset(x, 1, y, 3);
        let (mut s, mut e) = setup(&m);
        e.propagate(&mut s, &mut NullLogger).unwrap();
        assert_eq!(values(&s, y), [0, 1, 3].into());
    }

    #[test]
    fn propagation_chains_through_several_constraints() {
        // x = 0, x != y, y != z, with y in {0, 1} and z in {1, 2}:
        // y must be 1, so z must be 2.
        let mut m = Model::new();
        let (x, y, z) = (m.int_var(0, 0), m.int_var(0, 1), m.int_var(1, 2));
        m.not_equal(x, y);
        m.not_equal(y, z);
        let (mut s, mut e) = setup(&m);
        e.propagate(&mut s, &mut NullLogger).unwrap();
        assert_eq!(s.domain(y).fixed_value(), Some(1));
        assert_eq!(s.domain(z).fixed_value(), Some(2));
    }

    #[test]
    fn equal_fixed_values_conflict() {
        let mut m = Model::new();
        let (x, y) = (m.int_var(1, 1), m.int_var(1, 1));
        m.not_equal(x, y);
        let (mut s, mut e) = setup(&m);
        assert_eq!(e.propagate(&mut s, &mut NullLogger), Err(Conflict));
    }
}
