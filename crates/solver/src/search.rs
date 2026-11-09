//! Depth-first search with two-way branching: try `x = v`; when that fails,
//! assert `x != v` one level up. Each backtrack is a nogood the proof can
//! justify by RUP.

use std::ops::ControlFlow;

use crate::engine::Engine;
use crate::lit::Lit;
use crate::model::{Solution, VarId};
use crate::proof::ProofLogger;
use crate::store::DomainStore;

/// Strategy for choosing the next variable to branch on.
pub(crate) trait VariableSelector {
    /// An unfixed variable, or `None` if every variable is fixed.
    fn select(&mut self, store: &DomainStore) -> Option<VarId>;
}

/// The first unfixed variable, in the order they were created.
pub(crate) struct InputOrder;

impl VariableSelector for InputOrder {
    fn select(&mut self, store: &DomainStore) -> Option<VarId> {
        all_vars(store).find(|&v| store.domain(v).size() > 1)
    }
}

/// The unfixed variable with the fewest values ("first fail"); ties go to
/// the earliest variable.
pub(crate) struct SmallestDomain;

impl VariableSelector for SmallestDomain {
    fn select(&mut self, store: &DomainStore) -> Option<VarId> {
        all_vars(store)
            .filter(|&v| store.domain(v).size() > 1)
            .min_by_key(|&v| store.domain(v).size())
    }
}

fn all_vars(store: &DomainStore) -> impl Iterator<Item = VarId> {
    (0..store.num_vars() as u32).map(VarId)
}

/// How a search ended.
pub(crate) enum SearchEnd {
    /// The callback asked to stop, at this solution.
    Stopped(Solution),
    /// Every branch has been explored.
    Exhausted,
}

/// Depth-first search, calling `on_solution` for each solution found. The
/// callback returns `Break` to stop at that solution, or `Continue` to keep
/// searching: the solution is then treated like a conflict, so search
/// backtracks and moves on to the next branch.
pub(crate) fn search(
    store: &mut DomainStore,
    engine: &mut Engine,
    selector: &mut dyn VariableSelector,
    proof: &mut dyn ProofLogger,
    on_solution: &mut dyn FnMut(&Solution) -> ControlFlow<()>,
) -> SearchEnd {
    // Decisions currently in force, one per level above the root.
    let mut decisions: Vec<Lit> = Vec::new();

    loop {
        if engine.propagate(store, proof).is_ok() {
            match selector.select(store) {
                Some(var) => {
                    // Value ordering: smallest value first.
                    let decision = Lit::Eq(var, store.domain(var).lower());
                    store.push_level();
                    decisions.push(decision);
                    if let Some(event) = store.apply(decision).expect("decision value is in the domain") {
                        engine.notify(var, event);
                    }
                    continue;
                }
                None => {
                    let values: Vec<i64> = all_vars(store)
                        .map(|v| store.domain(v).fixed_value().expect("all fixed"))
                        .collect();
                    proof.solution(&values);
                    let solution = Solution { values };
                    if on_solution(&solution).is_break() {
                        return SearchEnd::Stopped(solution);
                    }
                    // Otherwise fall through and backtrack, as for a conflict.
                }
            }
        }

        // Conflict, or a solution we're moving past: undo the most recent
        // decision and assert its negation one level up. If that conflicts
        // too, keep going.
        loop {
            proof.backtrack(&decisions);
            let Some(decision) = decisions.pop() else {
                proof.unsat();
                return SearchEnd::Exhausted;
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
            let config = Config { var_order, ..Config::default() };
            assert!(matches!(solve(&m, &config).unwrap(), Outcome::Unsatisfiable));
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
