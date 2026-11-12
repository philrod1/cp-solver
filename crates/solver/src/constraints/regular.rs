use std::collections::HashSet;
use std::fmt;
use std::sync::{Arc, Mutex};

use super::{Cell, Constraint, PropagationContext, Propagator, Table};
use crate::domain::Conflict;
use crate::engine::Engine;
use crate::lit::Lit;
use crate::model::{DuplicateName, Model, VarId};
use crate::proof::{Ineq, Justification, NotEncodable, OpbEncoder, PbLit, Reason};
use crate::store::Event;

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

    /// The `(symbol, target)` transitions leaving `state`, by symbol.
    pub(crate) fn edges(&self, state: usize) -> &[(i64, usize)] {
        &self.transitions[state]
    }

    pub fn transitions(&self) -> impl Iterator<Item = (usize, i64, usize)> + '_ {
        self.transitions
            .iter()
            .enumerate()
            .flat_map(|(q, edges)| edges.iter().map(move |&(s, t)| (q, s, t)))
    }
}

/// `flags[i][q]`: "after reading `i` values, the automaton is in state `q`".
type Flags = Arc<Mutex<Vec<Vec<PbLit>>>>;

#[derive(Clone, Debug)]
pub struct Regular {
    vars: Vec<VarId>,
    automaton: Automaton,
    flags: Flags,
}

impl Regular {
    pub fn new(vars: &[VarId], automaton: Automaton) -> Self {
        return Self {
            vars: vars.to_vec(),
            automaton,
            flags: Flags::default(),
        };
    }
}

impl Constraint for Regular {
    fn post(&self, engine: &mut Engine) {
        engine.add(Box::new(Prop {
            vars: self.vars.clone(),
            automaton: self.automaton.clone(),
            flags: Arc::clone(&self.flags),
        }));
    }

    /// As GCS writes it, with a flag `x[name][i_q]` for each layer `i` and
    /// state `q`:
    ///
    /// ```text
    /// @c[name][s{i}al1]     some state in layer i
    /// @c[name][s{i}am1]     at most one state in layer i
    /// @c[name][start]       state 0 in layer 0
    /// @c[name][accept]      an accepting state in layer n
    /// @c[name][t{i}_{q}_{v}]  in q at layer i ∧ xᵢ = v ⇒ in δ(q, v) at layer i + 1
    ///                       (or ⇒ false, when q has no transition on v)
    /// ```
    ///
    /// for every value `v` in `xᵢ`'s declared domain.
    fn encode(&self, opb: &mut OpbEncoder<'_>) -> Result<(), NotEncodable> {
        let (n, k) = (self.vars.len(), self.automaton.num_states());
        let flags: Vec<Vec<PbLit>> = (0..=n)
            .map(|i| (0..k).map(|q| opb.indexed_flag(&[i, q])).collect())
            .collect();

        for (i, layer) in flags.iter().enumerate() {
            opb.row(&format!("s{i}al1"), &Ineq::clause(layer.iter().copied()));
            let at_most_one = layer.iter().map(|&f| (1, f)).collect();
            opb.row(&format!("s{i}am1"), &Ineq::le(at_most_one, 1));
        }
        opb.row("start", &Ineq::clause([flags[0][0]]));
        let accepting = (0..k)
            .filter(|&q| self.automaton.is_accepting(q))
            .map(|q| flags[n][q]);
        opb.row("accept", &Ineq::clause(accepting));

        for (i, &x) in self.vars.iter().enumerate() {
            let (lo, hi) = opb.declared(x);
            for q in 0..k {
                for v in lo..=hi {
                    let is_v = opb.eq(x, v);
                    let mut clause = vec![!flags[i][q], !is_v];
                    if let Some(target) = self.automaton.next(q, v) {
                        clause.push(flags[i + 1][target]);
                    }
                    opb.row(&format!("t{i}_{q}_{v}"), &Ineq::clause(clause));
                }
            }
        }

        *self.flags.lock().unwrap() = flags;
        Ok(())
    }
}

struct Prop {
    vars: Vec<VarId>,
    automaton: Automaton,
    flags: Flags,
}

impl Prop {
    /// Log every dead state, as "reason => not in state q at layer i", in an
    /// order where each line is RUP given the ones before it.
    ///
    /// 1. Forward deaths (unreachable states), from the first layer on.
    ///    Unit propagation can't reason "whichever state the automaton was
    ///    in at the layer before", so each one is preceded by a helper per
    ///    reachable predecessor `p`: "in `t` at layer i + 1 => not in `p` at
    ///    layer i". Each helper is RUP: assume both, and every value of xi
    ///    leads from `p` somewhere other than `t`. The helpers are only
    ///    needed when layer i has two or more reachable states and xᵢ has two
    ///    or more values, but they are always correct.
    /// 2. Backward deaths (reachable states that can't finish), from the
    ///    last layer back. Assume the state: every value of xi leads to a
    ///    state already known to be dead.
    fn log_dead_states(
        &self,
        ctx: &mut PropagationContext<'_>,
        reason: &[Lit],
        reach: &[Vec<bool>],
        alive: &[Vec<bool>],
    ) {
        let flags = self.flags.lock().unwrap();
        if flags.is_empty() {
            return; // no encoding was written, so there are no flags to name
        }
        let k = self.automaton.num_states();
        for i in 0..reach.len() {
            for t in (0..k).filter(|&t| !reach[i][t]) {
                if i > 0 {
                    for p in (0..k).filter(|&p| reach[i - 1][p]) {
                        ctx.rup(reason, &[!flags[i][t], !flags[i - 1][p]]);
                    }
                }
                ctx.rup(reason, &[!flags[i][t]]);
            }
        }
        for i in (0..reach.len()).rev() {
            for q in (0..k).filter(|&q| reach[i][q] && !alive[i][q]) {
                ctx.rup(reason, &[!flags[i][q]]);
            }
        }
    }
}

impl Propagator for Prop {
    fn name(&self) -> &'static str {
        "regular"
    }

    fn watches(&self) -> Vec<(VarId, Event)> {
        self.vars.iter().map(|&x| (x, Event::Domain)).collect()
    }

    /// 1. Forward: which states can be reached from the start?
    /// 2. Backward: which of those can still reach an accepting state at
    ///    the end? An edge between two such states is on a full path, so
    ///    its value is supported at its position.
    /// 3. Remove every value with no support.
    fn propagate(&mut self, ctx: &mut PropagationContext<'_>) -> Result<(), Conflict> {
        let (n, k) = (self.vars.len(), self.automaton.num_states());

        let mut reach = vec![vec![false; k]; n + 1];
        reach[0][0] = true;
        for (i, &x) in self.vars.iter().enumerate() {
            for q in 0..k {
                if !reach[i][q] {
                    continue;
                }
                for &(v, target) in self.automaton.edges(q) {
                    if ctx.domain(x).contains(v) {
                        reach[i + 1][target] = true;
                    }
                }
            }
        }

        let mut alive = vec![vec![false; k]; n + 1];
        for q in 0..k {
            alive[n][q] = reach[n][q] && self.automaton.is_accepting(q);
        }
        let mut supported: Vec<HashSet<i64>> = vec![HashSet::new(); n];
        for (i, &x) in self.vars.iter().enumerate().rev() {
            for q in 0..k {
                if !reach[i][q] {
                    continue;
                }
                for &(v, target) in self.automaton.edges(q) {
                    if alive[i + 1][target] && ctx.domain(x).contains(v) {
                        alive[i][q] = true;
                        supported[i].insert(v);
                    }
                }
            }
        }

        let dead_end = !alive[0][0];
        let unsupported: Vec<Vec<i64>> = self
            .vars
            .iter()
            .zip(&supported)
            .map(|(&x, sup)| ctx.domain(x).iter().filter(|v| !sup.contains(v)).collect())
            .collect();
        if !dead_end && unsupported.iter().all(Vec::is_empty) {
            return Ok(());
        }

        // One reason for every step of this call, taken before anything
        // changes: everything known about the sequence now.
        let reason = if ctx.is_logging() {
            let reason = ctx.reason_lits(Reason::Domains(&self.vars));
            self.log_dead_states(ctx, &reason, &reach, &alive);
            reason
        } else {
            Vec::new()
        };
        // With the dead states logged, each step is RUP: assume the opposite
        // and every state in some layer is ruled out.
        let why = Justification::Rup(Reason::Lits(&reason));
        if dead_end {
            return ctx.fail(why);
        }
        for (&x, values) in self.vars.iter().zip(&unsupported) {
            for &v in values {
                ctx.remove(x, v, why)?;
            }
        }
        Ok(())
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
    use std::collections::BTreeSet;
    use std::ops::ControlFlow;

    use proptest::prelude::*;

    use super::*;
    use crate::constraints::testing::{propagate, values};
    use crate::{Config, NotEqual, enumerate};

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

    /// The two ways to post a Regular.
    #[derive(Clone, Copy, Debug)]
    enum How {
        Native,
        Tables,
    }

    fn post(m: &mut Model, how: How, vars: &[VarId], automaton: &Automaton) {
        match how {
            How::Native => m.post(Regular::new(vars, automaton.clone())),
            How::Tables => {
                regular_by_tables(m, "r", vars, automaton).unwrap();
            }
        }
    }

    /// Every solution, by search, as the values of `positions` (indices
    /// into `vars`, which may repeat).
    fn solve_words(
        how: How,
        domains: &[(i64, i64)],
        positions: &[usize],
        automaton: &Automaton,
    ) -> Vec<Vec<i64>> {
        let mut m = Model::new();
        let vars: Vec<VarId> = domains.iter().map(|&(lo, hi)| m.int_var(lo, hi)).collect();
        let sequence: Vec<VarId> = positions.iter().map(|&i| vars[i]).collect();
        post(&mut m, how, &sequence, automaton);
        let mut words = Vec::new();
        enumerate(&m, &Config::default(), |sol| {
            words.push(sequence.iter().map(|&v| sol.value(v)).collect());
            ControlFlow::Continue(())
        })
        .unwrap();
        words
    }

    /// Every word over the sequence that `automaton` accepts, by brute force
    /// over the variables (so a repeated variable has the same value at
    /// each of its positions).
    fn brute_force(
        domains: &[(i64, i64)],
        positions: &[usize],
        automaton: &Automaton,
    ) -> Vec<Vec<i64>> {
        let mut assignments = vec![vec![]];
        for &(lo, hi) in domains {
            assignments = assignments
                .into_iter()
                .flat_map(|a: Vec<i64>| (lo..=hi).map(move |v| [a.clone(), vec![v]].concat()))
                .collect();
        }
        assignments
            .into_iter()
            .map(|a| positions.iter().map(|&i| a[i]).collect::<Vec<i64>>())
            .filter(|w| automaton.accepts(w))
            .collect()
    }

    /// Both ways find exactly the brute-force words.
    fn check_words(domains: &[(i64, i64)], positions: &[usize], automaton: &Automaton) -> usize {
        let mut expected = brute_force(domains, positions, automaton);
        expected.sort();
        for how in [How::Native, How::Tables] {
            let mut found = solve_words(how, domains, positions, automaton);
            found.sort();
            assert_eq!(found, expected, "{how:?}");
        }
        expected.len()
    }

    fn sequence(n: usize) -> Vec<usize> {
        (0..n).collect()
    }

    #[test]
    fn a_nonogram_row() {
        // Three spare 0s to share among three gaps: C(6, 2) = 15 words.
        assert_eq!(check_words(&[(0, 1); 10], &sequence(10), &three_two()), 15);
    }

    #[test]
    fn parity() {
        assert_eq!(check_words(&[(0, 1); 3], &sequence(3), &even_parity()), 4);
    }

    #[test]
    fn the_empty_sequence() {
        // Accepted exactly when the start state is accepting.
        assert_eq!(check_words(&[], &[], &even_parity()), 1);
        assert_eq!(check_words(&[], &[], &three_two()), 0);
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
        assert_eq!(check_words(&[(1, 3); 3], &sequence(3), &a), 4); // ?? then 2, with ?? in {1, 2}²
    }

    #[test]
    fn no_accepting_state() {
        let a = Automaton::new(1, &[(0, 0, 0), (0, 1, 0)], &[]).unwrap();
        assert_eq!(check_words(&[(0, 1); 3], &sequence(3), &a), 0);
    }

    #[test]
    fn a_repeated_variable() {
        // x y x with even parity: x x is always even, so y must be 0.
        assert_eq!(check_words(&[(0, 1); 2], &[0, 1, 0], &even_parity()), 2);
    }

    #[test]
    fn propagation_on_the_worked_example() {
        // Parity with X1 = 1 and X2 = 0 forces X0 = 1: the only path to the
        // accepting state reads a 1 first.
        let mut m = Model::new();
        let x = [m.int_var(0, 1), m.int_var(1, 1), m.int_var(0, 0)];
        m.post(Regular::new(&x, even_parity()));
        let (store, result) = propagate(&m);
        assert!(result.is_ok());
        assert_eq!(values(&store, x[0]), BTreeSet::from([1]));
    }

    #[test]
    fn wakes_on_any_removal_not_just_fixing() {
        // "x1 repeats x0" over {0, 1, 2}: from the start, reading v goes to
        // state v + 1, which accepts only another v.
        let edges: Vec<(usize, i64, usize)> = (0..3)
            .flat_map(|v| [(0, v, v as usize + 1), (v as usize + 1, v, 4)])
            .collect();
        let repeat = Automaton::new(5, &edges, &[4]).unwrap();
        let mut m = Model::new();
        let x = [m.int_var(0, 2), m.int_var(0, 2)];
        // Posted first, so it runs first and finds nothing to do. Then
        // x0 != 0 leaves x0 with two values, which isn't fixing it, and
        // Regular must wake up to take 0 from x1.
        m.post(Regular::new(&x, repeat));
        let zero = m.constant(0);
        m.post(NotEqual::new(x[0], zero));
        let (store, result) = propagate(&m);
        assert!(result.is_ok());
        assert_eq!(values(&store, x[1]), BTreeSet::from([1, 2]));
    }

    #[test]
    fn a_dead_end_is_a_conflict() {
        // The 3-block needs three cells, and there are only two.
        let mut m = Model::new();
        let x = [m.int_var(0, 1), m.int_var(0, 1)];
        m.post(Regular::new(&x, three_two()));
        assert!(propagate(&m).1.is_err());
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

    /// Random domains: an interval each, with some values knocked out.
    fn random_domains(
        n: std::ops::RangeInclusive<usize>,
    ) -> impl Strategy<Value = Vec<((i64, i64), Vec<i64>)>> {
        let domain = (-2i64..=2, 0i64..=2).prop_flat_map(|(lo, w)| {
            (
                Just((lo, lo + w)),
                prop::collection::vec(lo..=lo + w, 0..=1),
            )
        });
        prop::collection::vec(domain, n)
    }

    /// Propagate `how`'s model once at the root, and return each sequence
    /// variable's domain, or `None` for a conflict.
    fn root_domains(
        how: How,
        domains: &[((i64, i64), Vec<i64>)],
        automaton: &Automaton,
    ) -> Option<Vec<BTreeSet<i64>>> {
        let mut m = Model::new();
        let vars: Vec<VarId> = domains
            .iter()
            .map(|&((lo, hi), _)| m.int_var(lo, hi))
            .collect();
        for (&x, (_, holes)) in vars.iter().zip(domains) {
            for &h in holes {
                let k = m.constant(h);
                m.post(NotEqual::new(x, k));
            }
        }
        post(&mut m, how, &vars, automaton);
        let (store, result) = propagate(&m);
        result
            .ok()
            .map(|()| vars.iter().map(|&x| values(&store, x)).collect())
    }

    proptest! {
        #[test]
        fn both_ways_find_exactly_the_accepted_words(
            automaton in random_automaton(),
            domains in prop::collection::vec((-2i64..=2, 0i64..=2).prop_map(|(lo, w)| (lo, lo + w)), 0..=4),
        ) {
            check_words(&domains, &sequence(domains.len()), &automaton);
        }

        #[test]
        fn both_ways_find_the_words_with_repeats(
            automaton in random_automaton(),
            domains in prop::collection::vec((-2i64..=2, 0i64..=2).prop_map(|(lo, w)| (lo, lo + w)), 1..=3),
            picks in prop::collection::vec(0usize..3, 0..=5),
        ) {
            let positions: Vec<usize> = picks.iter().map(|&p| p % domains.len()).collect();
            check_words(&domains, &positions, &automaton);
        }

        #[test]
        fn native_prunes_exactly_as_much_as_the_tables(
            automaton in random_automaton(),
            domains in random_domains(0..=5),
        ) {
            // With no repeated variables the tables form a chain, which is
            // fully propagated, so the two must agree value for value.
            prop_assert_eq!(root_domains(How::Native, &domains, &automaton), root_domains(How::Tables, &domains, &automaton));
        }
    }
}
