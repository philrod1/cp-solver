use super::{Constraint, PropagationContext, Propagator};
use crate::domain::Conflict;
use crate::engine::Engine;
use crate::lit::Lit;
use crate::model::VarId;
use crate::proof::{Ineq, Justification, NotEncodable, OpbEncoder, Reason};
use crate::store::Event;

#[derive(Clone, Debug)]
pub struct NotEqual {
    x: VarId,
    y: VarId,
    x_offset: i64,
    y_offset: i64,
}

impl NotEqual {
    pub fn new(x: VarId, y: VarId) -> Self {
        Self::with_offsets(x, 0, y, 0)
    }

    pub fn with_offsets(x: VarId, x_offset: i64, y: VarId, y_offset: i64) -> Self {
        Self {
            x,
            y,
            x_offset,
            y_offset,
        }
    }
}

impl Constraint for NotEqual {
    fn post(&self, engine: &mut Engine) {
        engine.add(Box::new(Prop {
            x: self.x,
            y: self.y,
            x_offset: self.x_offset,
            y_offset: self.y_offset,
        }));
    }

    /// As GCS writes it: a flag `ne` choosing which side is bigger.
    ///
    /// ```text
    /// @c[name][gt]   ne ⇒ (x + a) - (y + b) ≥ 1
    /// @c[name][lt]  ¬ne ⇒ (x + a) - (y + b) ≤ -1
    /// ```
    fn encode(&self, opb: &mut OpbEncoder<'_>) -> Result<(), NotEncodable> {
        let NotEqual {
            x,
            y,
            x_offset,
            y_offset,
        } = *self;
        let ne = opb.flag("ne");
        // x - y, with the offsets moved to the right-hand side.
        let diff = opb.linear(&[(1, x), (-1, y)]);
        let shift = i128::from(y_offset) - i128::from(x_offset);
        opb.row("gt", &Ineq::ge(diff.clone(), 1 + shift).implied_by(ne));
        opb.row("lt", &Ineq::le(diff, -1 + shift).implied_by(!ne));
        Ok(())
    }
}

struct Prop {
    x: VarId,
    x_offset: i64,
    y: VarId,
    y_offset: i64,
}

impl Propagator for Prop {
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
                ctx.fail(Justification::Rup(Reason::Lits(&[])))
            } else {
                Ok(())
            };
        }
        // Each removal is unit propagation on one clause so it is justified by RUP.
        if let Some(vx) = ctx.fixed_value(self.x) {
            let why = Justification::Rup(Reason::Lits(&[Lit::Eq(self.x, vx)]));
            ctx.remove(self.y, vx + self.x_offset - self.y_offset, why)?;
        }
        if let Some(vy) = ctx.fixed_value(self.y) {
            let why = Justification::Rup(Reason::Lits(&[Lit::Eq(self.y, vy)]));
            ctx.remove(self.x, vy + self.y_offset - self.x_offset, why)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::NotEqual;
    use crate::constraints::testing::{propagate, values};
    use crate::domain::Conflict;
    use crate::model::Model;

    #[test]
    fn nothing_to_do_until_a_side_is_fixed() {
        let mut m = Model::new();
        let (x, y) = (m.int_var(0, 3), m.int_var(0, 3));
        m.post(NotEqual::new(x, y));
        let (s, r) = propagate(&m);
        assert_eq!(r, Ok(()));
        assert_eq!(values(&s, y), (0..=3).collect());
    }

    #[test]
    fn fixed_side_removes_value_from_other() {
        let mut m = Model::new();
        let (x, y) = (m.int_var(2, 2), m.int_var(0, 3));
        m.post(NotEqual::new(x, y));
        let (s, _) = propagate(&m);
        assert_eq!(values(&s, y), [0, 1, 3].into());
    }

    #[test]
    fn offsets_shift_the_removed_value() {
        // x + 1 != y + 3 with x = 4 means y != 2.
        let mut m = Model::new();
        let (x, y) = (m.int_var(4, 4), m.int_var(0, 3));
        m.post(NotEqual::with_offsets(x, 1, y, 3));
        let (s, _) = propagate(&m);
        assert_eq!(values(&s, y), [0, 1, 3].into());
    }

    #[test]
    fn propagation_chains_through_several_constraints() {
        // x = 0, x != y, y != z, with y in {0, 1} and z in {1, 2}:
        // y must be 1, so z must be 2.
        let mut m = Model::new();
        let (x, y, z) = (m.int_var(0, 0), m.int_var(0, 1), m.int_var(1, 2));
        m.post(NotEqual::new(x, y));
        m.post(NotEqual::new(y, z));
        let (s, r) = propagate(&m);
        assert_eq!(r, Ok(()));
        assert_eq!(s.domain(y).fixed_value(), Some(1));
        assert_eq!(s.domain(z).fixed_value(), Some(2));
    }

    #[test]
    fn equal_fixed_values_conflict() {
        let mut m = Model::new();
        let (x, y) = (m.int_var(1, 1), m.int_var(1, 1));
        m.post(NotEqual::new(x, y));
        assert_eq!(propagate(&m).1, Err(Conflict));
    }
}
