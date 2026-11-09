//! Depth-first search

use crate::engine::Engine;
use crate::lit::Lit;
use crate::model::{Solution, VarId};
use crate::proof::ProofLogger;
use crate::store::DomainStore;
use crate::Outcome;

/// Branching strategy for the search
pub(crate) trait VariableSelector {
    /// Select a variable to branch on, or None if all vars are fixed.
    fn select(&mut self, store: &DomainStore) -> Option<VarId>;
}

pub(crate) struct InputOrder;
impl VariableSelector for InputOrder {
    fn select(&mut self, store: &DomainStore) -> Option<VarId> {
        all_vars(store).find(|&var| store.domain(var).size() > 1)
    }
}

pub(crate) struct SmallestDomain;
impl VariableSelector for SmallestDomain {
    fn select(&mut self, store: &DomainStore) -> Option<VarId> {
        all_vars(store)
            .filter(|&var| store.domain(var).size() > 1)
            .min_by_key(|&var| store.domain(var).size())
    }
}

fn all_vars(store: &DomainStore) -> impl Iterator<Item = VarId> {
    (0..store.num_vars() as u32).map(VarId)
}

pub(crate) fn search(
    store: &mut DomainStore,
    engine: &mut Engine,
    selector: &mut dyn VariableSelector,
    proof: &mut dyn ProofLogger,
) -> Outcome {
    let mut decisions: Vec<Lit> = Vec::new();
    loop {
        if engine.propagate(store, proof).is_ok() {
            let Some(var) = selector.select(store) else {
                let values: Vec<i64> = all_vars(store)
                    .map(|var| store.domain(var).fixed_value().expect("all fixed"))
                    .collect();
                proof.solution(&values);
                return Outcome::Satisfiable(Solution { values });
            };
            let decision = Lit::Eq(var, store.domain(var).lower());
            store.push_level();
            decisions.push(decision);
            if let Some(event) = store.apply(decision).expect("decision value in domain") {
                engine.notify(var, event);
            }
            continue;
        }

        // Conflict
        loop {
            proof.backtrack(&decisions);
            let Some(decision) = decisions.pop() else {
                proof.unsat();
                return Outcome::Unsatisfiable;
            };
            store.backtrack();
            match store.apply(decision.negated()) {
                Ok(Some(event)) => {
                    engine.notify(decision.var(), event);
                    break;
                }
                Ok(None) => break,
                Err(_conflict) => continue,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{solve, Config, Model, NotEqual, Outcome, VarOrder};

    #[test]
    fn pigeonhole_is_unsatisfiable() {
        // Three pairwise-different variables, two values.
        for var_order in [VarOrder::InputOrder, VarOrder::SmallestDomain] {
            let mut m = Model::new();
            let v: Vec<_> = (0..3).map(|_| m.int_var(0, 1)).collect();
            m.post(NotEqual::new(v[0], v[1]));
            m.post(NotEqual::new(v[0], v[2]));
            m.post(NotEqual::new(v[1], v[2]));
            let config = Config {
                var_order,
                ..Config::default()
            };
            assert!(matches!(
                solve(&m, &config).unwrap(),
                Outcome::Unsatisfiable
            ));
        }
    }

    #[test]
    fn solution_satisfies_every_constraint() {
        // A permutation of 1..=3 with x > 1 and z != y + 1.
        let mut m = Model::new();
        let (x, y, z) = (m.int_var(2, 3), m.int_var(1, 3), m.int_var(1, 3));
        m.post(NotEqual::new(x, y));
        m.post(NotEqual::new(x, z));
        m.post(NotEqual::new(y, z));
        m.post(NotEqual::with_offsets(y, 1, z, 0));
        let Outcome::Satisfiable(sol) = solve(&m, &Config::default()).unwrap() else {
            panic!("expected a solution");
        };
        let (vx, vy, vz) = (sol.value(x), sol.value(y), sol.value(z));
        assert!(vx > 1 && vx != vy && vx != vz && vy != vz && vz != vy + 1);
    }
}
