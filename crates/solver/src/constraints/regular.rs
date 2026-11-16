//! Regular: a sequence of variables spells a word that a finite automaton
//! accepts. The automaton may be nondeterministic: a state can have several
//! transitions on the same symbol, and a word is accepted when some run
//! over it ends in an accepting state.
//!
//! Two ways to post it:
//!
//! - [`Regular`], a constraint with its own propagator (Pesant 2004). It
//!   unrolls the automaton into layers, one per position, and keeps a value
//!   only if it labels an edge on some path from the start state to an
//!   accepting state. Its proofs work in terms of state flags; see
//!   [`Regular::encode`] and the propagator.
//! - [`regular_by_tables`], a decomposition into tables over new state
//!   variables q₀ … qₙ:
//!
//!   ```text
//!   q₀ = 0                       the start state
//!   Table(qᵢ, xᵢ, qᵢ₊₁)           one row per transition (q, v, t), t ∈ δ(q, v)
//!   qₙ ∈ accepting states
//!   ```
//!
//!   The variables form a chain, so propagating every table completely
//!   also propagates the whole constraint completely: it prunes exactly as
//!   much as `Regular` (when no variable repeats), only more slowly. That
//!   makes it the reference `Regular` is tested against. Tables have a
//!   proof encoding, so it is proof-logged too. The state variables hold
//!   one run, so with a nondeterministic automaton a word with several
//!   accepting runs is several solutions.

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
    /// Each state's `(symbol, target)` transitions, sorted. A symbol can
    /// have several targets.
    transitions: Vec<Vec<(i64, usize)>>,
    accepting: Vec<bool>,
}

/// Excuses, excuses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AutomatonError {
    NoStates,
    NoSuchState(usize),
}

impl fmt::Display for AutomatonError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AutomatonError::NoStates => write!(f, "no state for this automaton"),
            AutomatonError::NoSuchState(q) => write!(f, "no state {q}"),
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
        for edges in &mut table {
            edges.sort_unstable();
            edges.dedup();
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

    /// The states `state` moves to on `symbol`: none, one, or several.
    pub fn targets(&self, state: usize, symbol: i64) -> impl Iterator<Item = usize> + '_ {
        let edges = &self.transitions[state];
        let first = edges.partition_point(|&(s, _)| s < symbol);
        edges[first..]
            .iter()
            .take_while(move |&&(s, _)| s == symbol)
            .map(|&(_, t)| t)
    }

    pub fn is_accepting(&self, state: usize) -> bool {
        self.accepting[state]
    }

    /// Whether some run over `word` ends in an accepting state.
    pub fn accepts(&self, word: &[i64]) -> bool {
        let k = self.num_states();
        let mut current = vec![false; k];
        current[0] = true;
        for &symbol in word {
            let mut next = vec![false; k];
            for q in (0..k).filter(|&q| current[q]) {
                for t in self.targets(q, symbol) {
                    next[t] = true;
                }
            }
            current = next;
        }
        (0..k).any(|q| current[q] && self.is_accepting(q))
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

/// `flags[i][q]`: "after reading `i` values, the automaton can be in state
/// `q`".
type Flags = Arc<Mutex<Vec<Vec<PbLit>>>>;

#[derive(Clone, Debug)]
pub struct Regular {
    vars: Vec<VarId>,
    automaton: Automaton,
    /// The state flags, shared by the encoding and the propagator: `encode`
    /// creates them, and the propagator names them in its proof steps.
    /// Empty when no proof is being written. GCS calls this the bridge.
    flags: Flags,
}

impl Regular {
    pub fn new(vars: &[VarId], automaton: Automaton) -> Self {
        Self {
            vars: vars.to_vec(),
            automaton,
            flags: Flags::default(),
        }
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

    /// With a flag `x[name][i_q]` for each layer `i` and state `q`, true
    /// exactly when the automaton can be in `q` after reading `i` values:
    ///
    /// ```text
    /// @c[name][start]         state 0, and no other, in layer 0
    /// @c[name][accept]        an accepting state in layer n
    /// @c[name][f{i}_{q}_{v}]  in q at layer i ∧ xᵢ = v ⇒ in every state of δ(q, v)
    ///                         at layer i + 1
    /// @c[name][b{i}_{t}_{v}]  in t at layer i + 1 ∧ xᵢ = v ⇒ in some p at layer i
    ///                         with t ∈ δ(p, v)
    /// ```
    ///
    /// for every value `v` in `xᵢ`'s declared domain (`f` rows only where
    /// δ(q, v) isn't empty). Fixing the values fixes every flag, so each
    /// solution has exactly one assignment to them.
    fn encode(&self, opb: &mut OpbEncoder<'_>) -> Result<(), NotEncodable> {
        let (n, k) = (self.vars.len(), self.automaton.num_states());
        let flags: Vec<Vec<PbLit>> = (0..=n)
            .map(|i| (0..k).map(|q| opb.indexed_flag(&[i, q])).collect())
            .collect();

        let start = (0..k)
            .map(|q| (1, if q == 0 { flags[0][q] } else { !flags[0][q] }))
            .collect();
        opb.row("start", &Ineq::ge(start, k as i128));
        let accepting = (0..k)
            .filter(|&q| self.automaton.is_accepting(q))
            .map(|q| flags[n][q]);
        opb.row("accept", &Ineq::clause(accepting));

        for (i, &x) in self.vars.iter().enumerate() {
            let (lo, hi) = opb.declared(x);
            for v in lo..=hi {
                let is_v = opb.eq(x, v);
                let mut preds = vec![Vec::new(); k];
                for q in 0..k {
                    let targets: Vec<usize> = self.automaton.targets(q, v).collect();
                    if targets.is_empty() {
                        continue;
                    }
                    for &t in &targets {
                        preds[t].push(q);
                    }
                    let all = targets.iter().map(|&t| (1, flags[i + 1][t])).collect();
                    let row = Ineq::ge(all, targets.len() as i128)
                        .implied_by(flags[i][q])
                        .implied_by(is_v);
                    opb.row(&format!("f{i}_{q}_{v}"), &row);
                }
                for (t, ps) in preds.iter().enumerate() {
                    let some = ps.iter().map(|&p| flags[i][p]);
                    let row = Ineq::clause([!flags[i + 1][t], !is_v].into_iter().chain(some));
                    opb.row(&format!("b{i}_{t}_{v}"), &row);
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

/// The states marked in `layer`.
fn marked(layer: &[bool]) -> impl Iterator<Item = usize> + '_ {
    (0..layer.len()).filter(|&q| layer[q])
}

/// Log "reason => not in state t at layer i" for every unreachable state,
/// from layer 1 on (layer 0 is the `start` row). Each is RUP: assume it,
/// and its `b` rows rule out every value of xᵢ₋₁, since each one would
/// need a predecessor that is already ruled out.
fn log_unreachable(
    ctx: &mut PropagationContext<'_>,
    reason: &[Lit],
    flags: &[Vec<PbLit>],
    reach: &[Vec<bool>],
) {
    for i in 1..reach.len() {
        for t in (0..reach[i].len()).filter(|&t| !reach[i][t]) {
            ctx.rup(reason, &[!flags[i][t]]);
        }
    }
}

/// Log "reason => in some alive state at layer j", for each layer from the
/// one before last down to `lowest`. At the last layer this is the `accept`
/// row once the unreachable states are out.
///
/// A dead state can still be reachable, so its flag can be true in a
/// solution; the argument is about the alive states as a group. Before the
/// lemma for layer j, a helper for each alive t at layer j + 1: "in some
/// alive state at layer j, or not in t at layer j + 1". Each is RUP: assume
/// the opposite, and every value of xⱼ that leads into t from a reachable
/// state leads from an alive one, so its `b` row rules it out. The lemma is
/// then RUP from the helpers and the lemma for layer j + 1.
fn log_alive_layers(
    ctx: &mut PropagationContext<'_>,
    reason: &[Lit],
    flags: &[Vec<PbLit>],
    alive: &[Vec<bool>],
    lowest: usize,
) {
    let n = alive.len() - 1;
    for j in (lowest..n).rev() {
        let some_alive: Vec<PbLit> = marked(&alive[j]).map(|q| flags[j][q]).collect();
        for t in marked(&alive[j + 1]) {
            let mut clause = some_alive.clone();
            clause.push(!flags[j + 1][t]);
            ctx.rup(reason, &clause);
        }
        ctx.rup(reason, &some_alive);
    }
}

impl Propagator for Prop {
    fn name(&self) -> &'static str {
        "regular"
    }

    fn watches(&self) -> Vec<(VarId, Event)> {
        self.vars.iter().map(|&x| (x, Event::Domain)).collect()
    }

    /// Layer `i` holds the states the automaton could be in after reading
    /// `i` values, and an edge from layer `i` to `i + 1` is a transition
    /// on a value still in `xᵢ`'s domain.
    ///
    /// 1. Forward: which states can be reached from the start?
    /// 2. Backward: which of those can still reach an accepting state at
    ///    the end? An edge between two such states is on a full path, so
    ///    its value is supported at its position.
    /// 3. Remove every value with no support.
    ///
    /// A variable that appears at several positions loses a value as soon
    /// as one position doesn't support it, which can leave other positions
    /// short of support; the engine wakes this propagator again for its
    /// own removals, so the next call deals with them.
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
            ctx.reason_lits(Reason::Domains(&self.vars))
        } else {
            Vec::new()
        };
        let guard = self.flags.lock().unwrap();
        // No flags means no encoding was written, so there's nothing to name.
        let flags = (ctx.is_logging() && !guard.is_empty()).then_some(guard.as_slice());
        let why = Justification::Rup(Reason::Lits(&reason));

        if let Some(flags) = flags {
            log_unreachable(ctx, &reason, flags, &reach);
        }
        if dead_end {
            // No accepting state is reachable, so the `accept` row is empty.
            return ctx.fail(why);
        }
        if let Some(flags) = flags {
            let first = unsupported.iter().position(|u| !u.is_empty()).unwrap();
            log_alive_layers(ctx, &reason, flags, &alive, first + 1);
        }
        for (i, (&x, values)) in self.vars.iter().zip(&unsupported).enumerate() {
            for &v in values {
                if !ctx.domain(x).contains(v) {
                    continue; // already removed at an earlier position
                }
                // Assume xᵢ = v: then no alive state at layer i + 1 is
                // reachable, one helper each (RUP, as v leads into them only
                // from unreachable states), and the lemma for layer i + 1
                // fails.
                if let Some(flags) = flags {
                    let assumed = [reason.as_slice(), &[Lit::Eq(x, v)]].concat();
                    for t in marked(&alive[i + 1]) {
                        ctx.rup(&assumed, &[!flags[i + 1][t]]);
                    }
                }
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

    /// Words over {0, 1} whose third symbol from the end is 1: state 0
    /// guesses which 1 that is. A deterministic version needs 8 states.
    fn third_from_last_is_one() -> Automaton {
        let edges = [
            (0, 0, 0),
            (0, 1, 0),
            (0, 1, 1),
            (1, 0, 2),
            (1, 1, 2),
            (2, 0, 3),
            (2, 1, 3),
        ];
        Automaton::new(4, &edges, &[3]).unwrap()
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
        // The same transition twice is fine, and counts once.
        let a = Automaton::new(1, &[(0, 5, 0), (0, 5, 0)], &[0]).unwrap();
        assert_eq!(a.targets(0, 5).collect::<Vec<_>>(), [0]);
    }

    #[test]
    fn several_targets_on_one_symbol() {
        let a = third_from_last_is_one();
        assert_eq!(a.targets(0, 1).collect::<Vec<_>>(), [0, 1]);
        assert_eq!(a.targets(0, 0).collect::<Vec<_>>(), [0]);
        assert_eq!(a.targets(3, 0).count(), 0);
        assert!(a.accepts(&[1, 0, 0]));
        assert!(a.accepts(&[0, 1, 1, 1, 0, 1]));
        assert!(!a.accepts(&[1, 0, 1, 0, 0, 1]));
        assert!(!a.accepts(&[1, 1])); // too short
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
    /// into `vars`, which may repeat). Solutions that differ only in the
    /// tables' state variables (several runs over one word) count once.
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
        let mut assignments: Vec<Vec<i64>> = Vec::new();
        enumerate(&m, &Config::default(), |sol| {
            assignments.push(vars.iter().map(|&v| sol.value(v)).collect());
            ControlFlow::Continue(())
        })
        .unwrap();
        assignments.sort();
        assignments.dedup();
        assignments
            .iter()
            .map(|a| positions.iter().map(|&i| a[i]).collect())
            .collect()
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
    fn a_nondeterministic_automaton() {
        // Five symbols, the third from the end fixed: 2⁴ words.
        assert_eq!(
            check_words(&[(0, 1); 5], &sequence(5), &third_from_last_is_one()),
            16
        );
    }

    #[test]
    fn propagation_follows_every_run() {
        // Three cells: the first is the third from the end, so it must be
        // 1. The others are free, whichever run reads them.
        let mut m = Model::new();
        let x = [m.int_var(0, 1), m.int_var(0, 1), m.int_var(0, 1)];
        m.post(Regular::new(&x, third_from_last_is_one()));
        let (store, result) = propagate(&m);
        assert!(result.is_ok());
        assert_eq!(values(&store, x[0]), BTreeSet::from([1]));
        assert_eq!(values(&store, x[1]), BTreeSet::from([0, 1]));
        assert_eq!(values(&store, x[2]), BTreeSet::from([0, 1]));
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

    /// A random, usually nondeterministic, automaton over symbols -1..=2:
    /// each (state, symbol) has up to two targets.
    fn random_automaton() -> impl Strategy<Value = Automaton> {
        (1usize..=4).prop_flat_map(|k| {
            let targets = prop::collection::vec(0..k, 0..=2);
            let table = prop::collection::vec(prop::collection::vec(targets, 4), k);
            let accepting = prop::collection::vec(any::<bool>(), k);
            (table, accepting).prop_map(move |(table, accepting)| {
                let edges: Vec<(usize, i64, usize)> = table
                    .iter()
                    .enumerate()
                    .flat_map(|(q, row)| {
                        row.iter()
                            .enumerate()
                            .flat_map(move |(s, ts)| ts.iter().map(move |&t| (q, s as i64 - 1, t)))
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
