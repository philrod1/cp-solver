//! AllDifferent: the terms `xᵢ + aᵢ` take pairwise distinct values, except
//! that terms taking an excluded value are free to equal each other.
//!
//! The propagator achieves generalised arc consistency. It removes a fixed
//! term's value from the others, and keeps a maximum matching of terms to
//! values. A term that can still take an excluded value needs no match.
//! When no matching covers the rest, some k terms share fewer than k values
//! (a Hall violator), and it fails. Otherwise it removes every value no
//! such matching uses, each held by k terms with only k values between
//! them (a Hall set). The proofs add up "each of these terms takes one of
//! its values" and "at most one term takes each value": see
//! [`justify_hall_set`].

use std::collections::{BTreeMap, HashMap, HashSet};

use super::{Constraint, PropagationContext, Propagator};
use crate::domain::Conflict;
use crate::engine::Engine;
use crate::lit::Lit;
use crate::model::VarId;
use crate::proof::{
    Ineq, Justification, Line, NotEncodable, OpbEncoder, PbLit, Pol, ProofLogger, Reason,
};
use crate::store::Event;

#[derive(Clone, Debug)]
pub struct AllDifferent {
    terms: Vec<(VarId, i64)>,
    excluded: Vec<i64>,
}

impl AllDifferent {
    pub fn new(terms: &[VarId]) -> Self {
        Self {
            terms: terms.iter().map(|&v| (v, 0)).collect(),
            excluded: Vec::new(),
        }
    }

    pub fn with_offsets(terms: &[(VarId, i64)]) -> Self {
        Self {
            terms: terms.to_vec(),
            excluded: Vec::new(),
        }
    }

    /// Exempt terms that take one of `excluded`, as `all_different_except`
    /// does: e.g. `AllDifferent::new(&vars).except(&[0])`.
    pub fn except(mut self, excluded: &[i64]) -> Self {
        self.excluded = excluded.to_vec();
        self.excluded.sort_unstable();
        self.excluded.dedup();
        self
    }
}

impl Constraint for AllDifferent {
    fn post(&self, engine: &mut Engine) {
        let n = self.terms.len();
        let repeated = (0..n)
            .filter(|&j| self.terms[..j].contains(&self.terms[j]))
            .collect();
        engine.add(Box::new(Prop {
            terms: self.terms.clone(),
            excluded: self.excluded.clone(),
            repeated,
            matched: vec![None; n],
            owner: HashMap::new(),
            at_most_one: HashMap::new(),
        }));
    }

    /// As GCS writes it: for each pair of terms `i < j`, a flag
    /// `x[name][i_j]` choosing which is bigger.
    ///
    /// ```text
    /// @c[name][{i}lt{j}]  !flag => (xi + ai) - (xj + aj) <= -1
    /// @c[name][{i}gt{j}]   flag => (xi + ai) - (xj + aj) >= 1
    /// ```
    ///
    /// Each excluded value `s` adds `xi + ai ≠ s` and `xj + aj ≠ s` to both
    /// rows' conditions, as GCS's AllDifferentExcept does, so either term
    /// taking `s` lifts both rows.
    fn encode(&self, opb: &mut OpbEncoder<'_>) -> Result<(), NotEncodable> {
        for (i, &(xi, ai)) in self.terms.iter().enumerate() {
            for (j, &(xj, aj)) in self.terms.iter().enumerate().skip(i + 1) {
                let flag = opb.indexed_flag(&[i, j]);
                let diff = opb.linear(&[(1, xi), (-1, xj)]);
                let shift = i128::from(aj) - i128::from(ai);
                let mut lt = Ineq::le(diff.clone(), -1 + shift).implied_by(!flag);
                let mut gt = Ineq::ge(diff, 1 + shift).implied_by(flag);
                for &s in &self.excluded {
                    for (x, a) in [(xi, ai), (xj, aj)] {
                        let (lo, hi) = opb.declared(x);
                        if (lo..=hi).contains(&(s - a)) {
                            let exempt = opb.eq(x, s - a);
                            lt = lt.implied_by(!exempt);
                            gt = gt.implied_by(!exempt);
                        }
                    }
                }
                opb.row(&format!("{i}lt{j}"), &lt);
                opb.row(&format!("{i}gt{j}"), &gt);
            }
        }
        Ok(())
    }
}

struct Prop {
    terms: Vec<(VarId, i64)>,
    /// Sorted.
    excluded: Vec<i64>,
    /// Terms that appear earlier too, so must take an excluded value.
    repeated: Vec<usize>,
    /// The value, offset included, each term is matched to.
    matched: Vec<Option<i64>>,
    /// The term each matched value belongs to.
    owner: HashMap<i64, usize>,
    /// "At most one term takes this value", once the proof has it.
    at_most_one: HashMap<i64, Option<Line>>,
}

/// The terms a failed search for an augmenting path visited, and the
/// values it tried.
struct Visited {
    terms: Vec<bool>,
    values: HashSet<i64>,
}

impl Propagator for Prop {
    fn name(&self) -> &'static str {
        "all_different"
    }

    fn watches(&self) -> Vec<(VarId, Event)> {
        self.terms
            .iter()
            .map(|(v, _)| (*v, Event::Domain))
            .collect()
    }

    fn propagate(&mut self, ctx: &mut PropagationContext<'_>) -> Result<(), Conflict> {
        self.exempt_repeated_terms(ctx)?;
        self.remove_fixed_values(ctx)?;
        self.match_every_term(ctx)?;
        self.remove_unmatchable_values(ctx)
    }
}

impl Prop {
    /// A term that appears twice must take an excluded value. Without
    /// excluded values that's a conflict. Each step is RUP: both of the
    /// pair's rows fail, whatever its flag.
    fn exempt_repeated_terms(&self, ctx: &mut PropagationContext<'_>) -> Result<(), Conflict> {
        if self.excluded.is_empty() && !self.repeated.is_empty() {
            return ctx.fail(Justification::Rup(Reason::Lits(&[])));
        }
        for &i in &self.repeated {
            let (x, a) = self.terms[i];
            let doomed: Vec<i64> = ctx
                .domain(x)
                .iter()
                .filter(|v| !self.is_excluded(v + a))
                .collect();
            for v in doomed {
                ctx.remove(x, v, Justification::Rup(Reason::Lits(&[])))?;
            }
        }
        Ok(())
    }

    fn is_excluded(&self, u: i64) -> bool {
        self.excluded.binary_search(&u).is_ok()
    }

    /// Term `i` can still take an excluded value, so needs no match.
    fn exempt(&self, ctx: &PropagationContext<'_>, i: usize) -> bool {
        let (x, a) = self.terms[i];
        self.excluded.iter().any(|&s| ctx.domain(x).contains(s - a))
    }

    fn remove_fixed_values(&self, ctx: &mut PropagationContext<'_>) -> Result<(), Conflict> {
        // Each removal is "at most one" so justified by RUP.
        for (i, &(xi, ai)) in self.terms.iter().enumerate() {
            let Some(v) = ctx.fixed_value(xi) else {
                continue;
            };
            let value = v + ai;
            if self.is_excluded(value) {
                continue;
            }
            for (j, &(xj, aj)) in self.terms.iter().enumerate() {
                if j != i {
                    let why = Justification::Rup(Reason::Lits(&[Lit::Eq(xi, v)]));
                    ctx.remove(xj, value - aj, why)?;
                }
            }
        }
        Ok(())
    }

    /// Repair the matching after domains have changed, or fail if no
    /// matching covers every term that can't take an excluded value.
    fn match_every_term(&mut self, ctx: &mut PropagationContext<'_>) -> Result<(), Conflict> {
        for (i, &(x, a)) in self.terms.iter().enumerate() {
            if let Some(u) = self.matched[i]
                && (!ctx.domain(x).contains(u - a) || self.exempt(ctx, i))
            {
                self.matched[i] = None;
                self.owner.remove(&u);
            }
        }
        for i in 0..self.terms.len() {
            if self.matched[i].is_some() || self.exempt(ctx, i) {
                continue;
            }
            let mut visited = Visited {
                terms: vec![false; self.terms.len()],
                values: HashSet::new(),
            };
            if !self.augment(ctx, i, &mut visited) {
                return self.fail(ctx, &visited);
            }
        }
        Ok(())
    }

    /// Match term `i`, moving other terms along an augmenting path if
    /// need be (Kuhn's algorithm).
    fn augment(&mut self, ctx: &PropagationContext<'_>, i: usize, visited: &mut Visited) -> bool {
        visited.terms[i] = true;
        let (x, a) = self.terms[i];
        let values: Vec<i64> = ctx.domain(x).iter().map(|v| v + a).collect();
        let free = values.iter().find(|u| !self.owner.contains_key(u));
        if let Some(&u) = free {
            self.assign(i, u);
            return true;
        }
        for u in values {
            if !visited.values.insert(u) {
                continue;
            }
            let j = self.owner[&u];
            if !visited.terms[j] && self.augment(ctx, j, visited) {
                self.assign(i, u);
                return true;
            }
        }
        false
    }

    fn assign(&mut self, i: usize, u: i64) {
        self.matched[i] = Some(u);
        self.owner.insert(u, i);
    }

    /// Fail on the Hall violator a failed augmentation found: the terms it
    /// visited can only take the values it tried, and there is one value
    /// fewer than terms.
    fn fail(
        &mut self,
        ctx: &mut PropagationContext<'_>,
        visited: &Visited,
    ) -> Result<(), Conflict> {
        let hall: Vec<usize> = (0..self.terms.len())
            .filter(|&i| visited.terms[i])
            .collect();
        let vars = self.vars_of(&hall);
        if !ctx.is_logging() {
            return ctx.fail(Justification::Rup(Reason::Domains(&vars)));
        }
        let mut values: Vec<i64> = visited.values.iter().copied().collect();
        values.sort_unstable();
        let helpers = justify_hall_set(ctx, &self.terms, &mut self.at_most_one, &hall, &values);
        let result = ctx.fail(Justification::Rup(Reason::Domains(&vars)));
        ctx.proof.delete(&helpers);
        result
    }

    /// Remove every value no matching can give its term (Régin). With the
    /// matching complete, a value is kept if it is its term's match, if
    /// it can reach a free value, or if it lies on a cycle with its term.
    /// Any other value `u` is held by a Hall set: the terms reachable from
    /// `u` can only take the values reachable from `u`, and there are as
    /// many of each. One proof per component covers its removals.
    fn remove_unmatchable_values(
        &mut self,
        ctx: &mut PropagationContext<'_>,
    ) -> Result<(), Conflict> {
        let graph = Graph::new(&self.terms, &self.matched, ctx);
        let reaches_free = graph.reaches_free();
        let component = components(&graph.out);
        let mut doomed: BTreeMap<usize, Vec<(usize, VarId, i64)>> = BTreeMap::new();
        for (i, &(x, a)) in self.terms.iter().enumerate() {
            for v in ctx.domain(x).iter() {
                let u = v + a;
                // Values no matched term can take are free.
                let Some(&node) = graph.node.get(&u) else {
                    continue;
                };
                let kept = self.matched[i] == Some(u)
                    || reaches_free[node]
                    || component[i] == component[node];
                if !kept {
                    doomed
                        .entry(component[node])
                        .or_default()
                        .push((node, x, v));
                }
            }
        }
        for removals in doomed.into_values() {
            let (mut helpers, mut reason) = (Vec::new(), Vec::new());
            if ctx.is_logging() {
                let (hall, values) = graph.reach(removals[0].0);
                // Taken now: the removals may change these domains.
                reason = ctx.reason_lits(Reason::Domains(&self.vars_of(&hall)));
                helpers = justify_hall_set(ctx, &self.terms, &mut self.at_most_one, &hall, &values);
            }
            for &(_, x, v) in &removals {
                ctx.remove(x, v, Justification::Rup(Reason::Lits(&reason)))?;
            }
            if !helpers.is_empty() {
                ctx.proof.delete(&helpers);
            }
        }
        Ok(())
    }

    /// The variables of terms `hall`, each once.
    fn vars_of(&self, hall: &[usize]) -> Vec<VarId> {
        let mut vars: Vec<VarId> = hall.iter().map(|&i| self.terms[i].0).collect();
        vars.sort_unstable_by_key(|x| x.index());
        vars.dedup();
        vars
    }
}

/// The matching as a directed graph. Nodes `0..n` are the terms, and the
/// rest are values. Each matched term points to the other values it could
/// take, and each matched value to its term, so a path alternates between
/// "could take" and "is held by". Exempt terms are left out: they hold
/// nothing, and nothing needs them.
struct Graph {
    terms: usize,
    values: Vec<i64>,
    node: HashMap<i64, usize>,
    out: Vec<Vec<usize>>,
}

impl Graph {
    fn new(terms: &[(VarId, i64)], matched: &[Option<i64>], ctx: &PropagationContext<'_>) -> Self {
        let mut graph = Graph {
            terms: terms.len(),
            values: Vec::new(),
            node: HashMap::new(),
            out: vec![Vec::new(); terms.len()],
        };
        for (i, &(x, a)) in terms.iter().enumerate() {
            let Some(m) = matched[i] else {
                continue;
            };
            let held = graph.value_node(m);
            graph.out[held].push(i);
            for v in ctx.domain(x).iter() {
                if v + a != m {
                    let other = graph.value_node(v + a);
                    graph.out[i].push(other);
                }
            }
        }
        graph
    }

    fn value_node(&mut self, u: i64) -> usize {
        *self.node.entry(u).or_insert_with(|| {
            self.values.push(u);
            self.out.push(Vec::new());
            self.out.len() - 1
        })
    }

    /// Whether each node has a path to a value no term holds.
    fn reaches_free(&self) -> Vec<bool> {
        let mut into = vec![Vec::new(); self.out.len()];
        for (from, out) in self.out.iter().enumerate() {
            for &to in out {
                into[to].push(from);
            }
        }
        let mut reached = vec![false; self.out.len()];
        let mut todo: Vec<usize> = (self.terms..self.out.len())
            .filter(|&u| self.out[u].is_empty())
            .collect();
        for &u in &todo {
            reached[u] = true;
        }
        while let Some(to) = todo.pop() {
            for &from in &into[to] {
                if !reached[from] {
                    reached[from] = true;
                    todo.push(from);
                }
            }
        }
        reached
    }

    /// The terms and values reachable from `start`, sorted.
    fn reach(&self, start: usize) -> (Vec<usize>, Vec<i64>) {
        let mut seen = vec![false; self.out.len()];
        seen[start] = true;
        let mut todo = vec![start];
        while let Some(from) = todo.pop() {
            for &to in &self.out[from] {
                if !seen[to] {
                    seen[to] = true;
                    todo.push(to);
                }
            }
        }
        let terms = (0..self.terms).filter(|&i| seen[i]).collect();
        let mut values: Vec<i64> = (self.terms..self.out.len())
            .filter(|&u| seen[u])
            .map(|u| self.values[u - self.terms])
            .collect();
        values.sort_unstable();
        (terms, values)
    }
}

/// The strongly connected component of each node, by Tarjan's algorithm
/// without recursion.
fn components(out: &[Vec<usize>]) -> Vec<usize> {
    const UNSEEN: usize = usize::MAX;
    let mut index = vec![UNSEEN; out.len()];
    let mut low = vec![0; out.len()];
    let mut component = vec![UNSEEN; out.len()];
    let mut stack = Vec::new();
    let (mut next, mut count) = (0, 0);
    for root in 0..out.len() {
        if index[root] != UNSEEN {
            continue;
        }
        index[root] = next;
        low[root] = next;
        next += 1;
        stack.push(root);
        // Each call: a node, and how many of its edges it has followed.
        let mut calls = vec![(root, 0)];
        while let Some(call) = calls.last_mut() {
            let v = call.0;
            if let Some(&w) = out[v].get(call.1) {
                call.1 += 1;
                if index[w] == UNSEEN {
                    index[w] = next;
                    low[w] = next;
                    next += 1;
                    stack.push(w);
                    calls.push((w, 0));
                } else if component[w] == UNSEEN {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            calls.pop();
            if let Some(&(parent, _)) = calls.last() {
                low[parent] = low[parent].min(low[v]);
            }
            if low[v] == index[v] {
                loop {
                    let w = stack.pop().unwrap();
                    component[w] = count;
                    if w == v {
                        break;
                    }
                }
                count += 1;
            }
        }
    }
    component
}

/// Lines from which, with the domains of the terms in `hall` (indices)
/// whose values are all among `values`, the conclusion follows by RUP.
/// With more terms than values, that is a failure; with as many, it is
/// that no other term takes any of `values`. Returns the lines to delete
/// once the conclusions are logged.
///
/// Adds up, for each Hall term, "it takes some value between its bounds",
/// and, for each value, "at most one term takes it". The Hall terms'
/// values cancel, leaving a line that needs |hall| − |values| from values
/// the domains rule out, and from other terms not taking `values`.
fn justify_hall_set(
    ctx: &mut PropagationContext<'_>,
    terms: &[(VarId, i64)],
    cache: &mut HashMap<i64, Option<Line>>,
    hall: &[usize],
    values: &[i64],
) -> Vec<Line> {
    let mut helpers = Vec::new();
    let mut sum = Pol::default();
    for &i in hall {
        let (x, _) = terms[i];
        let (lo, hi) = (ctx.domain(x).lower(), ctx.domain(x).upper());
        let line = at_least_one(ctx.proof, x, lo, hi);
        sum.add(&line, 1);
        helpers.push(line);
    }
    for &u in values {
        let amo = cache
            .entry(u)
            .or_insert_with(|| at_most_one(ctx.proof, terms, u));
        if let Some(amo) = amo {
            sum.add(amo, 1);
        }
    }
    helpers.push(ctx.proof.pol(&sum));
    helpers
}

/// `x < lo ∨ x ≥ hi + 1 ∨ x = lo ∨ … ∨ x = hi`, by RUP: the equality atoms'
/// definitions walk the `≥` atoms up from `lo`.
fn at_least_one(proof: &mut dyn ProofLogger, x: VarId, lo: i64, hi: i64) -> Line {
    let mut lits: Vec<PbLit> = (lo..=hi).map(|v| proof.eq_atom(x, v)).collect();
    lits.push(!proof.ge_atom(x, lo).flag.lit);
    lits.push(proof.ge_atom(x, hi + 1).flag.lit);
    proof.rup_line(&Ineq::clause(lits))
}

/// "At most one term takes `u`", over the terms whose bits can represent
/// it, as `Σ ¬[xᵢ = u − aᵢ] ≥ k − 1`. Each pair is a clause, by RUP from the
/// pair's rows. Then for k = 3, 4, …, the line for the first k terms is
/// ((k − 2)·(the line for k − 1) + (the pairs with term k)) / (k − 1),
/// which rounds up to k − 1. Every line but the last is deleted.
///
/// None if only one term can take `u`. A Hall set needs no line for such a
/// value: the term's own "takes some value" keeps it.
fn at_most_one(proof: &mut dyn ProofLogger, terms: &[(VarId, i64)], u: i64) -> Option<Line> {
    let candidates: Vec<(VarId, i64)> = terms
        .iter()
        .copied()
        .filter(|&(x, a)| {
            let (lo, hi) = proof.bit_range(x);
            (lo..=hi).contains(&(u - a))
        })
        .collect();
    let lits: Vec<PbLit> = candidates
        .iter()
        .map(|&(x, a)| !proof.eq_atom(x, u - a))
        .collect();
    if lits.len() < 2 {
        return None;
    }
    let mut helpers = Vec::new();
    let mut line = proof.rup_line(&Ineq::clause([lits[0], lits[1]]));
    for k in 3..=lits.len() as i128 {
        let new = lits[k as usize - 1];
        let mut pol = Pol::default();
        pol.add(&line, k - 2);
        helpers.push(line);
        for &old in &lits[..k as usize - 1] {
            let pair = proof.rup_line(&Ineq::clause([old, new]));
            pol.add(&pair, 1);
            helpers.push(pair);
        }
        pol.divide(k - 1);
        line = proof.pol(&pol);
    }
    proof.delete(&helpers);
    Some(line)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use proptest::prelude::*;

    use super::AllDifferent;
    use crate::constraints::testing::{propagate, values};
    use crate::domain::Conflict;
    use crate::model::{Model, VarId};

    #[test]
    fn fixed_value_is_removed_from_all_others() {
        let mut m = Model::new();
        let x = m.int_var(2, 2);
        let others: Vec<_> = (0..3).map(|_| m.int_var(0, 4)).collect();
        m.post(AllDifferent::new(&[x, others[0], others[1], others[2]]));
        let (s, r) = propagate(&m);
        assert_eq!(r, Ok(()));
        for &v in &others {
            assert_eq!(values(&s, v), [0, 1, 3, 4].into());
        }
    }

    #[test]
    fn offsets_shift_the_removed_value() {
        // x + 0 = 3, so y + 2 != 3 means y != 1.
        let mut m = Model::new();
        let (x, y) = (m.int_var(3, 3), m.int_var(0, 3));
        m.post(AllDifferent::with_offsets(&[(x, 0), (y, 2)]));
        let (s, _) = propagate(&m);
        assert_eq!(values(&s, y), [0, 2, 3].into());
    }

    #[test]
    fn removals_cascade() {
        // x = 0 leaves y = 1, which leaves z = 2.
        let mut m = Model::new();
        let (x, y, z) = (m.int_var(0, 0), m.int_var(0, 1), m.int_var(0, 2));
        m.post(AllDifferent::new(&[x, y, z]));
        let (s, r) = propagate(&m);
        assert_eq!(r, Ok(()));
        assert_eq!(s.domain(y).fixed_value(), Some(1));
        assert_eq!(s.domain(z).fixed_value(), Some(2));
    }

    #[test]
    fn two_equal_fixed_values_conflict() {
        let mut m = Model::new();
        let (x, y, z) = (m.int_var(1, 1), m.int_var(0, 5), m.int_var(1, 1));
        m.post(AllDifferent::new(&[x, y, z]));
        assert_eq!(propagate(&m).1, Err(Conflict));
    }

    #[test]
    fn repeated_term_conflicts_at_root() {
        let mut m = Model::new();
        let (x, y) = (m.int_var(0, 4), m.int_var(0, 4));
        m.post(AllDifferent::new(&[x, y, x]));
        assert_eq!(propagate(&m).1, Err(Conflict));
    }

    #[test]
    fn repeated_variable_with_different_offsets_is_fine() {
        let mut m = Model::new();
        let x = m.int_var(0, 1);
        m.post(AllDifferent::with_offsets(&[(x, 0), (x, 1)]));
        assert_eq!(propagate(&m).1, Ok(()));
    }

    #[test]
    fn pigeonhole_fails_at_root() {
        let mut m = Model::new();
        let v: Vec<_> = (0..3).map(|_| m.int_var(0, 1)).collect();
        m.post(AllDifferent::new(&v));
        assert_eq!(propagate(&m).1, Err(Conflict));
    }

    #[test]
    fn violator_among_wider_domains_fails() {
        // x, y, z share {1, 2}; w could take anything.
        let mut m = Model::new();
        let w = m.int_var(1, 5);
        let v: Vec<_> = (0..3).map(|_| m.int_var(1, 2)).collect();
        m.post(AllDifferent::new(&[w, v[0], v[1], v[2]]));
        assert_eq!(propagate(&m).1, Err(Conflict));
    }

    #[test]
    fn offsets_can_make_a_pigeonhole() {
        // x ∈ {0, 1}, y + 1 ∈ {1, 2}, z + 2 ∈ {1, 2}: three terms, two values.
        let mut m = Model::new();
        let (x, y, z) = (m.int_var(0, 1), m.int_var(0, 1), m.int_var(-1, 0));
        m.post(AllDifferent::with_offsets(&[(x, 1), (y, 1), (z, 2)]));
        assert_eq!(propagate(&m).1, Err(Conflict));
    }

    #[test]
    fn a_hall_set_keeps_its_values_from_the_others() {
        // x and y need 1 and 2 between them, leaving z only 3.
        let mut m = Model::new();
        let (x, y, z) = (m.int_var(1, 2), m.int_var(1, 2), m.int_var(1, 3));
        m.post(AllDifferent::new(&[x, y, z]));
        let (s, r) = propagate(&m);
        assert_eq!(r, Ok(()));
        assert_eq!(values(&s, z), [3].into());
        assert_eq!(values(&s, x), [1, 2].into());
    }

    #[test]
    fn values_with_a_way_to_a_free_value_stay() {
        let mut m = Model::new();
        let (x, y) = (m.int_var(1, 2), m.int_var(1, 3));
        m.post(AllDifferent::new(&[x, y]));
        let (s, _) = propagate(&m);
        assert_eq!(values(&s, x), [1, 2].into());
        assert_eq!(values(&s, y), [1, 2, 3].into());
    }

    #[test]
    fn nested_hall_sets() {
        // {x, y} hold {1, 2}; then {x, y, z} hold {1, 2, 3}, so w is 4 or 5.
        let mut m = Model::new();
        let (x, y) = (m.int_var(1, 2), m.int_var(1, 2));
        let (z, w) = (m.int_var(1, 3), m.int_var(1, 5));
        m.post(AllDifferent::new(&[w, z, x, y]));
        let (s, _) = propagate(&m);
        assert_eq!(values(&s, z), [3].into());
        assert_eq!(values(&s, w), [4, 5].into());
    }

    #[test]
    fn a_hall_set_pushes_an_exempt_term_to_its_excluded_value() {
        let mut m = Model::new();
        let w = m.int_var(0, 2);
        let (x, y) = (m.int_var(1, 2), m.int_var(1, 2));
        m.post(AllDifferent::new(&[w, x, y]).except(&[0]));
        let (s, _) = propagate(&m);
        assert_eq!(values(&s, w), [0].into());
    }

    #[test]
    fn terms_may_share_an_excluded_value() {
        // Three terms, two values, but 0 is excluded.
        let mut m = Model::new();
        let v: Vec<_> = (0..3).map(|_| m.int_var(0, 1)).collect();
        m.post(AllDifferent::new(&v).except(&[0]));
        assert_eq!(propagate(&m).1, Ok(()));
    }

    #[test]
    fn a_fixed_excluded_value_stays_with_the_others() {
        let mut m = Model::new();
        let (x, y) = (m.int_var(0, 0), m.int_var(0, 2));
        m.post(AllDifferent::new(&[x, y]).except(&[0]));
        let (s, _) = propagate(&m);
        assert_eq!(values(&s, y), [0, 1, 2].into());
    }

    #[test]
    fn excluded_values_count_after_the_offset() {
        // x + 1 = 2 is excluded, so y can also be 2.
        let mut m = Model::new();
        let (x, y) = (m.int_var(1, 1), m.int_var(1, 3));
        m.post(AllDifferent::with_offsets(&[(x, 1), (y, 0)]).except(&[2]));
        let (s, _) = propagate(&m);
        assert_eq!(values(&s, y), [1, 2, 3].into());
    }

    #[test]
    fn a_repeated_term_must_take_an_excluded_value() {
        let mut m = Model::new();
        let (x, y) = (m.int_var(-4, 6), m.int_var(0, 2));
        m.post(AllDifferent::new(&[x, y, x]).except(&[-2, 3]));
        let (s, r) = propagate(&m);
        assert_eq!(r, Ok(()));
        assert_eq!(values(&s, x), [-2, 3].into());
    }

    #[test]
    fn a_repeated_term_without_its_excluded_values_conflicts() {
        let mut m = Model::new();
        let x = m.int_var(1, 4);
        m.post(AllDifferent::new(&[x, x]).except(&[0]));
        assert_eq!(propagate(&m).1, Err(Conflict));
    }

    #[test]
    fn terms_that_cant_be_exempt_still_make_a_pigeonhole() {
        // w could take 0; x, y and z can't, and share {1, 2}.
        let mut m = Model::new();
        let w = m.int_var(0, 2);
        let v: Vec<_> = (0..3).map(|_| m.int_var(1, 2)).collect();
        m.post(AllDifferent::new(&[w, v[0], v[1], v[2]]).except(&[0]));
        assert_eq!(propagate(&m).1, Err(Conflict));
    }

    proptest! {
        #[test]
        fn root_propagation_leaves_exactly_the_supported_values(
            terms in prop::collection::vec(
                ((-2i64..=2, 0i64..=3).prop_map(|(lo, w)| (lo, lo + w)), -2i64..=2),
                2..=5,
            ),
            excluded in prop::collection::vec(-2i64..=2, 0..=2),
        ) {
            // Distinct variables, so GAC leaves each term exactly the values
            // it takes in some solution, and fails when there are none.
            let mut m = Model::new();
            let vars: Vec<(VarId, i64)> =
                terms.iter().map(|&((lo, hi), a)| (m.int_var(lo, hi), a)).collect();
            m.post(AllDifferent::with_offsets(&vars).except(&excluded));
            let mut products: Vec<Vec<i64>> = vec![vec![]];
            for &((lo, hi), a) in &terms {
                products = products
                    .into_iter()
                    .flat_map(|p| (lo..=hi).map(move |v| [p.clone(), vec![v + a]].concat()))
                    .collect();
            }
            let distinct = |p: &Vec<i64>| {
                let p: Vec<i64> = p.iter().copied().filter(|u| !excluded.contains(u)).collect();
                p.iter().enumerate().all(|(k, u)| !p[..k].contains(u))
            };
            let solutions: Vec<&Vec<i64>> = products.iter().filter(|p| distinct(p)).collect();
            let (s, r) = propagate(&m);
            prop_assert_eq!(r.is_ok(), !solutions.is_empty());
            if r.is_ok() {
                for (k, &(x, a)) in vars.iter().enumerate() {
                    let supported: BTreeSet<i64> = solutions.iter().map(|p| p[k] - a).collect();
                    prop_assert_eq!(values(&s, x), supported, "term {}", k);
                }
            }
        }
    }
}
