//! Builder API: the solver's public way of stating a problem.

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::constraints::Constraint;

/// An integer variable, as an index into the model's variable list.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct VarId(pub(crate) u32);

impl VarId {
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

/// Posting a constraint under a name that is already taken.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DuplicateName(pub String);

impl fmt::Display for DuplicateName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "a constraint is already named '{}'", self.0)
    }
}

impl std::error::Error for DuplicateName {}

#[derive(Debug, Default)]
pub struct Model {
    /// Initial domain of each variable, as inclusive bounds.
    pub(crate) domains: Vec<(i64, i64)>,
    pub(crate) constraints: Vec<Box<dyn Constraint>>,
    /// The name of each constraint, in posting order. Proofs will refer to
    /// constraints by these names.
    names: Vec<String>,
    taken: HashSet<String>,
    /// Fixed variables standing for integer constants, one per value.
    constants: HashMap<i64, VarId>,
    constant_of: HashMap<VarId, i64>,
    /// Some variable was declared with `lo > hi`, so nothing can satisfy it.
    pub(crate) empty_domain: bool,
}

impl Model {
    pub fn new() -> Self {
        Self::default()
    }

    /// A new variable with domain `lo..=hi`. If `lo > hi` the domain is empty
    /// and the model has no solutions; that's not an error, just a fact
    /// about the problem.
    pub fn int_var(&mut self, lo: i64, hi: i64) -> VarId {
        let id = VarId(self.domains.len() as u32);
        if lo > hi {
            self.empty_domain = true;
            // Any value will do: the solver stops before looking at it.
            self.domains.push((lo, lo));
        } else {
            self.domains.push((lo, hi));
        }
        id
    }

    /// The variable fixed to `value`, created the first time it's asked for.
    /// Constants are recorded as such, so they can be told apart from
    /// variables that just happen to have a single value.
    pub fn constant(&mut self, value: i64) -> VarId {
        if let Some(&id) = self.constants.get(&value) {
            return id;
        }
        let id = self.int_var(value, value);
        self.constants.insert(value, id);
        self.constant_of.insert(id, value);
        id
    }

    /// The value of `var` if it was made by [`Model::constant`].
    pub fn constant_value(&self, var: VarId) -> Option<i64> {
        self.constant_of.get(&var).copied()
    }

    /// Add a constraint, e.g. `model.post(AllDifferent::new(&vars))`. It is
    /// named `_N`, with `N` the first number that gives an unused name.
    pub fn post(&mut self, constraint: impl Constraint + 'static) {
        let mut n = self.constraints.len() + 1;
        while self.taken.contains(&format!("_{n}")) {
            n += 1;
        }
        let name = format!("_{n}");
        self.post_named(&name, constraint).expect("the name was checked to be free");
    }

    /// Add a constraint under `name`, which must not already be in use.
    pub fn post_named(&mut self, name: &str, constraint: impl Constraint + 'static) -> Result<(), DuplicateName> {
        if !self.taken.insert(name.to_string()) {
            return Err(DuplicateName(name.to_string()));
        }
        self.names.push(name.to_string());
        self.constraints.push(Box::new(constraint));
        Ok(())
    }

    pub fn num_vars(&self) -> usize {
        self.domains.len()
    }

    pub fn constraints(&self) -> &[Box<dyn Constraint>] {
        &self.constraints
    }

    /// The name of each constraint, in the same order as [`Model::constraints`].
    pub fn constraint_names(&self) -> &[String] {
        &self.names
    }
}

/// A value for every variable in the model.
#[derive(Clone, Debug)]
pub struct Solution {
    pub(crate) values: Vec<i64>,
}

impl Solution {
    pub fn value(&self, var: VarId) -> i64 {
        self.values[var.index()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraints::NotEqual;

    #[test]
    fn constants_are_shared_and_recorded() {
        let mut m = Model::new();
        let x = m.int_var(0, 5);
        let three = m.constant(3);
        assert_eq!(m.constant(3), three);
        assert_ne!(m.constant(4), three);
        assert_eq!(m.constant_value(three), Some(3));
        assert_eq!(m.constant_value(x), None);
    }

    #[test]
    fn names_are_kept_in_order_and_must_be_unique() {
        let mut m = Model::new();
        let (x, y) = (m.int_var(0, 1), m.int_var(0, 1));
        m.post_named("c1", NotEqual::new(x, y)).unwrap();
        m.post(NotEqual::new(x, y));
        assert_eq!(m.post_named("c1", NotEqual::new(x, y)), Err(DuplicateName("c1".into())));
        assert_eq!(m.constraint_names(), ["c1", "_2"]);
    }

    #[test]
    fn automatic_names_avoid_taken_ones() {
        let mut m = Model::new();
        let (x, y) = (m.int_var(0, 1), m.int_var(0, 1));
        m.post_named("_1", NotEqual::new(x, y)).unwrap();
        m.post_named("_2", NotEqual::new(x, y)).unwrap();
        m.post(NotEqual::new(x, y)); // _3 is the first free one
        assert_eq!(m.constraint_names(), ["_1", "_2", "_3"]);
    }

    #[test]
    fn inconsistent_bounds_mean_no_solutions() {
        let mut m = Model::new();
        m.int_var(0, 3);
        assert!(!m.empty_domain);
        m.int_var(5, 2);
        assert!(m.empty_domain);
    }
}
