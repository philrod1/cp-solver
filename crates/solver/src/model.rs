//! Builder API: the solver's public way of stating a problem.

use crate::constraints::Constraint;

/// An integer variable, as an index into the model's variable list.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct VarId(pub(crate) u32);

impl VarId {
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Default)]
pub struct Model {
    pub(crate) domains: Vec<(i64, i64)>,
    pub(crate) constraints: Vec<Box<dyn Constraint>>,
}

impl Model {
    pub fn new() -> Self {
        Self::default()
    }

    /// A new variable with domain `lo..=hi`.
    pub fn int_var(&mut self, lo: i64, hi: i64) -> VarId {
        assert!(lo <= hi, "empty domain {lo}..={hi}");
        let id = VarId(self.domains.len() as u32);
        self.domains.push((lo, hi));
        id
    }

    pub fn post(&mut self, constraint: impl Constraint + 'static) {
        self.constraints.push(Box::new(constraint));
    }

    pub fn num_vars(&self) -> usize {
        self.domains.len()
    }

    pub fn constraints(&self) -> &[Box<dyn Constraint>] {
        &self.constraints
    }
}

#[derive(Clone, Debug)]
pub struct Solution {
    pub(crate) values: Vec<i64>,
}

impl Solution {
    pub fn value(&self, var: VarId) -> i64 {
        self.values[var.index()]
    }
}
