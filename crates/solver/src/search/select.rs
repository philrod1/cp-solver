pub trait VariableSelector {
    fn select(&mut self, store: &DomainStore, vars: &[VarId]) -> Option<VarId>;
}

pub struct SmallestDomain;
pub struct DomWdeg { weights: Vec<u32> }

let search = Search::new(Box::new(DomWdeg::default()), Box::new(MinValue));
