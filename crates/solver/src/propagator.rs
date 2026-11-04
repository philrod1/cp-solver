

pub trait Propagator {
    fn name(&self) -> &'static str;
    fn watched(&self) -> &[VarId];
    fn propagate(&mut self, ctx: &mut PropagationContext<'_>) -> Result<(), Conflict>;
}

pub struct PropagationContext<'a> {
    store: &'a mut DomainStore,
    proof: &'a mut dyn ProofLogger,
}

impl PropagationContext<'_> {
    pub fn set_lower(
        &mut self,
        var: VarId,
        val: i32,
        why: Justification,
    ) -> Result<(), Conflict> {
        self.store.set_lower(var, val, self.proof)
    }

    pub fn remove(&mut self, var: VarId, val: i32, why: Justification) -> Result<(), Conflict> {
        self.store.remove(var, val, self.proof)
    }   
}
