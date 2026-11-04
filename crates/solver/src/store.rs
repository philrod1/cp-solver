//! The domains of all variables, with every change trailed automatically.

use crate::domain::{Conflict, SparseDomain};
use crate::model::{Model, VarId};
use crate::trail::Trail;

#[derive(Debug)]
pub(crate) struct DomainStore {
    domains: Vec<SparseDomain>,
    trail: Trail,
}

impl DomainStore {
    pub(crate) fn new(model: &Model) -> Self {
        let domains: Vec<SparseDomain> = model
            .domains
            .iter()
            .map(|&(lo, hi)| SparseDomain::new(lo, hi))
            .collect();
        let trail = Trail::new(domains.len());
        Self { domains, trail }
    }

    pub(crate) fn domain(&self, var: VarId) -> &SparseDomain {
        &self.domains[var.index()]
    }

    pub(crate) fn num_vars(&self) -> usize {
        self.domains.len()
    }

    pub(crate) fn remove(&mut self, var: VarId, val: i64) -> Result<bool, Conflict> {
        let d = &mut self.domains[var.index()];
        if !d.contains(val) {
            return Ok(false); // no change, so nothing to trail
        }
        self.trail.save(var, d.snapshot());
        d.remove(val)
    }

    pub(crate) fn fix(&mut self, var: VarId, val: i64) -> Result<bool, Conflict> {
        let d = &mut self.domains[var.index()];
        if d.fixed_value() == Some(val) {
            return Ok(false);
        }
        self.trail.save(var, d.snapshot());
        d.fix(val)
    }

    pub(crate) fn level(&self) -> usize {
        self.trail.level()
    }

    pub(crate) fn push_level(&mut self) {
        self.trail.push_level();
    }

    pub(crate) fn backtrack(&mut self) {
        self.trail.backtrack(&mut self.domains);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    fn store(domains: &[(i64, i64)]) -> (DomainStore, Vec<VarId>) {
        let mut model = Model::new();
        let vars = domains
            .iter()
            .map(|&(lo, hi)| model.int_var(lo, hi))
            .collect();
        (DomainStore::new(&model), vars)
    }

    fn values(s: &DomainStore, v: VarId) -> BTreeSet<i64> {
        s.domain(v).iter().collect()
    }

    #[test]
    fn backtrack_restores_one_level() {
        let (mut s, v) = store(&[(0, 4)]);
        s.push_level();
        s.remove(v[0], 1).unwrap();
        s.remove(v[0], 0).unwrap();
        assert_eq!(values(&s, v[0]), [2, 3, 4].into());
        s.backtrack();
        assert_eq!(values(&s, v[0]), (0..=4).collect());
        assert_eq!(s.domain(v[0]).lower(), 0);
        assert_eq!(s.level(), 0);
    }

    #[test]
    fn backtrack_restores_each_level_in_turn() {
        let (mut s, v) = store(&[(0, 4), (0, 4)]);
        s.push_level();
        s.remove(v[0], 2).unwrap();
        s.push_level();
        s.remove(v[0], 3).unwrap();
        s.fix(v[1], 4).unwrap();

        s.backtrack();
        assert_eq!(values(&s, v[0]), [0, 1, 3, 4].into());
        assert_eq!(values(&s, v[1]), (0..=4).collect());
        s.backtrack();
        assert_eq!(values(&s, v[0]), (0..=4).collect());
    }

    #[test]
    fn one_entry_per_variable_per_level() {
        let (mut s, v) = store(&[(0, 9)]);
        s.push_level();
        for val in 0..5 {
            s.remove(v[0], val).unwrap();
        }
        assert_eq!(s.trail.len(), 1);
        s.backtrack();
        assert_eq!(values(&s, v[0]), (0..=9).collect());
    }

    #[test]
    fn re_entered_level_is_trailed_again() {
        let (mut s, v) = store(&[(0, 4)]);
        s.push_level(); //                   level 1
        s.push_level(); //                   level 2
        s.remove(v[0], 0).unwrap();
        s.backtrack(); //                    back to 1
        s.push_level(); //                   level 2 again, new decision
        s.remove(v[0], 4).unwrap(); //       must be trailed here
        s.backtrack();
        assert_eq!(values(&s, v[0]), (0..=4).collect());
    }

    #[test]
    fn changes_after_backtrack_belong_to_the_outer_level() {
        let (mut s, v) = store(&[(0, 4), (0, 4)]);
        s.push_level(); //                   level 1
        s.remove(v[1], 0).unwrap();
        s.push_level(); //                   level 2: decide x = 2
        s.fix(v[0], 2).unwrap();
        s.backtrack(); //                    back to 1
        s.remove(v[0], 2).unwrap(); //       assert x != 2 at level 1
        s.remove(v[1], 1).unwrap(); //       y already saved at level 1
        assert_eq!(s.trail.len(), 2);
        s.backtrack(); //                    back to the root
        assert_eq!(values(&s, v[0]), (0..=4).collect());
        assert_eq!(values(&s, v[1]), (0..=4).collect());
    }

    #[test]
    fn root_changes_are_permanent() {
        let (mut s, v) = store(&[(0, 4)]);
        s.remove(v[0], 0).unwrap();
        s.push_level();
        s.remove(v[0], 1).unwrap();
        s.backtrack();
        assert_eq!(values(&s, v[0]), [1, 2, 3, 4].into());
    }
}
