pub struct NotEqual {
    x: VarId,
    y: VarId,
}

impl Propagator for NotEqual {
    fn name(&self) -> &'static str {
        "not_equal"
    }

    fn watched(&self) -> Vec<VarId> {
        vec![self.x, self.y]
    }

    fn propagate(&mut self, ctx: &mut PropagationContext<'_>) -> Result<(), Conflict> {
        if let Some(v) = ctx.fixed_value(self.x) {
            ctx.remove(self.y, v, Justification::Rup)?;
        }
        if let Some(v) = ctx.fixed_value(self.y) {
            ctx.remove(self.x, v, Justification::Rup)?;
        }
        Ok(())
    }
}
