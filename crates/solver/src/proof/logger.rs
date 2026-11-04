pub enum Justification {
    Rup,
    Explicit(Box<dyn FnOnce(&mut ProofWriter)>), // Write `pol` steps
    Unchecked,                                   // Trust me, bro.
}

pub trait ProofLogger {
    fn log_inference(&mut self, lit: Lit, why: Justification);
    fn log_backtrack(&mut self, nogood: &[Lit]);
}
