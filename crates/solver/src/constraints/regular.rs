use std::fmt;

use crate::model::{DuplicateName, Model, VarId};

use super::{Cell, Table};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Automaton {
    transitions: Vec<Vec<(i64, usize)>>,
    accepting: Vec<bool>,
}

/// Excuses, excuses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AutomatonError {
    NoStates,
    NoSuchState(usize),
    NonDeterministic { state: usize, symbol: i64 },
}

impl fmt::Display for AutomatonError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AutomatonError::NoStates => write!(f, "No state for this automaton"),
            AutomatonError::NoSuchState(q) => write!(f, "No state {q}"),
            AutomatonError::NonDeterministic { state, symbol } => {
                write!(f, "State {state} has multiple transitions on {symbol}")
            }
        }
    }
}

impl std::error::Error for AutomatonError {}

impl Automaton {
    pub fn new(
        num_states: usize,
        transitions: &[(usize, i64, usize)],
        accepting: &[usize],
    ) -> Result<Self, AutomatonError> {
        if num_states == 0 {
            return Err(AutomatonError::NoStates);
        }
        let state = |q: usize| {
            if q < num_states {
                Ok(q)
            } else {
                Err(AutomatonError::NoSuchState(q))
            }
        };
        let mut table = vec![Vec::new(); num_states];
        for &(from, symbol, to) in transitions {
            table[state(from)?].push((symbol, state(to)?));
        }
        for (q, edges) in table.iter_mut().enumerate() {
            edges.sort_unstable();
            edges.dedup();
            if let Some(pair) = edges.windows(2).find(|w| w[0].0 == w[1].0) {
                return Err(AutomatonError::NonDeterministic {
                    state: q,
                    symbol: pair[0].0,
                });
            }
        }
        let mut is_accepting = vec![false; num_states];
        for &q in accepting {
            is_accepting[state(q)?] = true;
        }
        Ok(Automaton {
            transitions: table,
            accepting: is_accepting,
        })
    }

    pub fn num_states(&self) -> usize {
        self.transitions.len()
    }

    pub fn next(&self, state: usize, symbol: i64) -> Option<usize> {
        let edges = &self.transitions[state];
        edges
            .binary_search_by_key(&symbol, |&(s, _)| s)
            .ok()
            .map(|i| edges[i].1)
    }

    pub fn is_accepting(&self, state: usize) -> bool {
        self.accepting[state]
    }

    pub fn accepts(&self, word: &[i64]) -> bool {
        word.iter()
            .try_fold(0, |q, &symbol| self.next(q, symbol))
            .is_some_and(|q| self.is_accepting(q))
    }

    pub fn transitions(&self) -> impl Iterator<Item = (usize, i64, usize)> + '_ {
        self.transitions
            .iter()
            .enumerate()
            .flat_map(|(q, edges)| edges.iter().map(move |&(s, t)| (q, s, t)))
    }
}

/// "Temporary" regular-by-table-decomposition
pub fn regular_by_tables(
    model: &mut Model,
    name: &str,
    vars: &[VarId],
    automaton: &Automaton,
) -> Result<Vec<VarId>, DuplicateName> {
    let top = automaton.num_states() as i64 - 1;
    let states: Vec<VarId> = (0..=vars.len())
        .map(|i| {
            let hi = if i == 0 { 0 } else { top };
            model.int_var_named(&format!("{name}_q{i}"), 0, hi)
        })
        .collect();

    let rows: Vec<Vec<Cell>> = automaton
        .transitions()
        .map(|(q, symbol, target)| {
            vec![
                Cell::Val(q as i64),
                Cell::Val(symbol),
                Cell::Val(target as i64),
            ]
        })
        .collect();

    for (i, &x) in vars.iter().enumerate() {
        let scope = [states[i], x, states[i + 1]];
        model.post_named(&format!("{name}_t{i}"), Table::new(&scope, &rows))?;
    }

    let accepting: Vec<Vec<Cell>> = (0..automaton.num_states())
        .filter(|&q| automaton.is_accepting(q))
        .map(|q| vec![Cell::Val(q as i64)])
        .collect();

    let last = states[vars.len()];
    model.post_named(&format!("{name}_accept"), Table::new(&[last], &accepting))?;
    Ok(states)
}

#[cfg(test)]
mod tests {
    use std::ops::ControlFlow;

    use proptest::prelude::*;

    use super::*;
    use crate::{Config, enumerate};

    /// A row of a nonogram with the clue "3 2": `0* 111 0+ 11 0*`.
    fn three_two() -> Automaton {
        let edges = [
            (0, 0, 0),
            (0, 1, 1),
            (1, 1, 2),
            (2, 1, 3),
            (3, 0, 4),
            (4, 0, 4),
            (4, 1, 5),
            (5, 1, 6),
            (6, 0, 6),
        ];
        Automaton::new(7, &edges, &[6]).unwrap()
    }

    /// Even parity over {0, 1}: GCS's `regular_sat.scp`.
    fn even_parity() -> Automaton {
        Automaton::new(2, &[(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)], &[0]).unwrap()
    }

    #[test]
    fn accepting_words() {
        let a = three_two();
        assert!(a.accepts(&[1, 1, 1, 0, 1, 1]));
        assert!(a.accepts(&[0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0]));
        assert!(!a.accepts(&[1, 1, 1, 1, 1])); // no gap
        assert!(!a.accepts(&[1, 1, 0, 1, 1, 1])); // blocks the wrong way round
        assert!(!a.accepts(&[1, 1, 1, 0, 1])); // second block too short
        assert!(!a.accepts(&[])); // the start state isn't accepting
        assert!(!a.accepts(&[2])); // no transition on 2
        assert!(even_parity().accepts(&[]));
        assert!(even_parity().accepts(&[1, 0, 1]));
        assert!(!even_parity().accepts(&[1, 1, 1]));
    }

    #[test]
    fn building_checks_the_automaton() {
        assert_eq!(Automaton::new(0, &[], &[]), Err(AutomatonError::NoStates));
        assert_eq!(
            Automaton::new(2, &[(0, 5, 2)], &[]),
            Err(AutomatonError::NoSuchState(2))
        );
        assert_eq!(
            Automaton::new(2, &[], &[3]),
            Err(AutomatonError::NoSuchState(3))
        );
        assert_eq!(
            Automaton::new(2, &[(0, 5, 0), (0, 5, 1)], &[]),
            Err(AutomatonError::NonDeterministic {
                state: 0,
                symbol: 5
            })
        );
        // The same transition twice is fine.
        assert!(Automaton::new(1, &[(0, 5, 0), (0, 5, 0)], &[0]).is_ok());
    }

    /// Every solution of `vars` spelling a word of `automaton`, by search.
    fn solve_words(domains: &[(i64, i64)], automaton: &Automaton) -> Vec<Vec<i64>> {
        let mut m = Model::new();
        let vars: Vec<VarId> = domains.iter().map(|&(lo, hi)| m.int_var(lo, hi)).collect();
        regular_by_tables(&mut m, "r", &vars, automaton).unwrap();
        let mut words = Vec::new();
        enumerate(&m, &Config::default(), |sol| {
            words.push(vars.iter().map(|&v| sol.value(v)).collect());
            ControlFlow::Continue(())
        })
        .unwrap();
        words
    }

    /// Every word over `domains` that `automaton` accepts, by brute force.
    fn brute_force(domains: &[(i64, i64)], automaton: &Automaton) -> Vec<Vec<i64>> {
        let mut words = vec![vec![]];
        for &(lo, hi) in domains {
            words = words
                .into_iter()
                .flat_map(|w: Vec<i64>| (lo..=hi).map(move |v| [w.clone(), vec![v]].concat()))
                .collect();
        }
        words.retain(|w| automaton.accepts(w));
        words
    }

    fn same_words(mut a: Vec<Vec<i64>>, mut b: Vec<Vec<i64>>) {
        a.sort();
        b.sort();
        assert_eq!(a, b);
    }

    #[test]
    fn a_nonogram_row() {
        // Three spare 0s to share among three gaps: C(6, 2) = 15 words.
        let words = solve_words(&[(0, 1); 10], &three_two());
        assert_eq!(words.len(), 15);
        same_words(words, brute_force(&[(0, 1); 10], &three_two()));
    }

    #[test]
    fn parity() {
        let words = solve_words(&[(0, 1); 3], &even_parity());
        same_words(
            words,
            vec![vec![0, 0, 0], vec![0, 1, 1], vec![1, 0, 1], vec![1, 1, 0]],
        );
    }

    #[test]
    fn the_empty_sequence() {
        // Accepted exactly when the start state is accepting.
        assert_eq!(solve_words(&[], &even_parity()).len(), 1);
        assert_eq!(solve_words(&[], &three_two()).len(), 0);
    }

    #[test]
    fn symbols_outside_the_domains() {
        // The automaton reads 0, 1 and 2, but the variables only allow 1..=3:
        // words are runs of 1s and 2s that end with a 2. The 3 is never read.
        let a = Automaton::new(
            2,
            &[(0, 0, 0), (0, 1, 0), (0, 2, 1), (1, 1, 0), (1, 2, 1)],
            &[1],
        )
        .unwrap();
        let words = solve_words(&[(1, 3); 3], &a);
        assert_eq!(words.len(), 4); // ?? then 2, with ?? in {1, 2}²
        same_words(words, brute_force(&[(1, 3); 3], &a));
    }

    #[test]
    fn no_accepting_state() {
        let a = Automaton::new(1, &[(0, 0, 0), (0, 1, 0)], &[]).unwrap();
        assert!(solve_words(&[(0, 1); 3], &a).is_empty());
    }

    #[test]
    fn names_come_from_the_label() {
        let mut m = Model::new();
        let x = m.int_var(0, 1);
        let states = regular_by_tables(&mut m, "row", &[x], &even_parity()).unwrap();
        assert_eq!(m.var_name(states[0]), "row_q0");
        assert_eq!(m.var_name(states[1]), "row_q1");
        assert_eq!(m.constraint_names(), ["row_t0", "row_accept"]);
        // The same name again clashes.
        assert!(regular_by_tables(&mut m, "row", &[x], &even_parity()).is_err());
    }

    /// A random automaton over symbols -1..=2: each (state, symbol) has a
    /// transition with probability 2/3.
    fn random_automaton() -> impl Strategy<Value = Automaton> {
        (1usize..=4).prop_flat_map(|k| {
            let edge = prop::option::weighted(0.67, 0..k);
            let table = prop::collection::vec(prop::collection::vec(edge, 4), k);
            let accepting = prop::collection::vec(any::<bool>(), k);
            (table, accepting).prop_map(move |(table, accepting)| {
                let edges: Vec<(usize, i64, usize)> = table
                    .iter()
                    .enumerate()
                    .flat_map(|(q, row)| {
                        row.iter()
                            .enumerate()
                            .filter_map(move |(s, t)| t.map(|t| (q, s as i64 - 1, t)))
                    })
                    .collect();
                let finals: Vec<usize> = (0..k).filter(|&q| accepting[q]).collect();
                Automaton::new(k, &edges, &finals).unwrap()
            })
        })
    }

    proptest! {
        #[test]
        fn decomposition_finds_exactly_the_accepted_words(
            automaton in random_automaton(),
            domains in prop::collection::vec((-2i64..=2, 0i64..=2).prop_map(|(lo, w)| (lo, lo + w)), 0..=4),
        ) {
            same_words(solve_words(&domains, &automaton), brute_force(&domains, &automaton));
        }
    }
}
