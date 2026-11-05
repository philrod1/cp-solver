/// An integer variable as an index into the model's variable list.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VarId(pub(crate) u32);

impl VarId {
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone)]
pub enum Constraint {
    NotEqual {
        x: VarId,
        y: VarId,
        x_offset: i64,
        y_offset: i64,
    },
    AllDifferent {
        terms: Vec<(VarId, i64)>,
    },
}

/// A model built through the builder API
#[derive(Debug, Default)]
pub struct Model {
    pub(crate) constraints: Vec<Constraint>,
    pub(crate) domains: Vec<(i64, i64)>,
}

impl Model {
    pub fn new() -> Self {
        Self::default()
    }

    // Add a new integer variable with the given domain [lower..=upper]. Returns the variable's ID.
    pub fn int_var(&mut self, lower: i64, upper: i64) -> VarId {
        assert!(lower <= upper, "invalid domain [{lower}..={upper}]");
        let id = VarId(self.domains.len() as u32);
        self.domains.push((lower, upper));
        id
    }

    pub fn num_vars(&self) -> usize {
        self.domains.len()
    }

    pub fn constraints(&self) -> &[Constraint] {
        &self.constraints
    }

    pub fn domain(&self, var: VarId) -> (i64, i64) {
        self.domains[var.index()]
    }

    pub fn not_equal_offset(&mut self, x: VarId, x_offset: i64, y: VarId, y_offset: i64) {
        self.constraints.push(Constraint::NotEqual {
            x,
            y,
            x_offset,
            y_offset,
        });
    }

    pub fn not_equal(&mut self, x: VarId, y: VarId) {
        self.not_equal_offset(x, 0, y, 0);
    }

    pub fn all_different(&mut self, terms: &[VarId]) {
        self.constraints.push(Constraint::AllDifferent {
            terms: terms.iter().map(|&v| (v, 0)).collect(),
        });
    }

    pub fn all_different_offset(&mut self, terms: &[(VarId, i64)]) {
        self.constraints.push(Constraint::AllDifferent {
            terms: terms.to_vec(),
        });
    }
}

#[derive(Clone, Debug)]
pub struct Solution {
    pub values: Vec<i64>,
}

impl Solution {
    pub fn value(&self, var: VarId) -> i64 {
        self.values[var.index()]
    }
}
