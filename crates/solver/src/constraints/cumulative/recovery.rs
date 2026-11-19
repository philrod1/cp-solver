//! The per-time capacity rows, derived in the proof.
//!
//! The OPB says the capacity holds when each task starts (the
//! `scap_<j>` rows). Time-tabling reasons about single time points, so it
//! cites
//!
//! ```text
//! C_t:  Σ { hᵢ·cact(i, t) : t in task i's window } ≤ C
//! ```
//!
//! over per-time flags defined in the proof when first needed, each fully
//! reified (two `red` steps):
//!
//! ```text
//! v[name][i_t][cb]    sᵢ ≤ t                 started by t
//! v[name][i_t][ca]    sᵢ ≥ t − dᵢ + 1        not finished by t
//! v[name][i_t][cact]  cb ∧ ca                running at t
//! ```
//!
//! `C_t` comes from `C_{t−1}` by splitting on which task, if any, starts at
//! exactly t. If none does, every task running at t was running at t − 1,
//! and `C_{t−1}` bounds the load. If j does, every task running at t is
//! running when j starts, and j's checkpoint row bounds it. Below every
//! window there is no load at all, which starts the chain. Each row is
//! derived once, reason-free, and cited from then on. This follows the
//! Glasgow Constraint Solver's derivation step for step.

use std::collections::{BTreeMap, HashMap};

use super::Encoded;
use crate::proof::{Flag, Ineq, Line, PbLit, Pol, ProofLogger};

/// One task's flags at one time.
#[derive(Clone)]
pub(super) struct PerTime {
    pub(super) cb: Flag,
    pub(super) ca: Flag,
    pub(super) cact: Flag,
}

/// What has been defined and derived so far. Everything in it is a
/// reason-free line, so it stays valid whatever the search does.
#[derive(Default)]
pub(super) struct Recovery {
    flags: HashMap<(usize, i64), PerTime>,
    rows: BTreeMap<i64, Line>,
}

impl Recovery {
    /// Task k's flags at time t, defined if they aren't yet. t must be in
    /// k's window.
    pub(super) fn per_time(
        &mut self,
        proof: &mut dyn ProofLogger,
        enc: &Encoded,
        k: usize,
        t: i64,
    ) -> PerTime {
        if let Some(flags) = self.flags.get(&(k, t)) {
            return flags.clone();
        }
        let task = enc.tasks[k];
        let name = |which: &str| format!("v[{}][{}_{t}][{which}]", enc.name, task.index);
        let start = proof.linear(&[(1, task.start)]);
        let cb = proof.define_flag(name("cb"), &Ineq::le(start.clone(), t.into()));
        let started = Ineq::ge(start, (t - task.duration + 1).into());
        let ca = proof.define_flag(name("ca"), &started);
        let both = Ineq::ge(vec![(1, cb.lit), (1, ca.lit)], 2);
        let cact = proof.define_flag(name("cact"), &both);
        let flags = PerTime { cb, ca, cact };
        self.flags.insert((k, t), flags.clone());
        flags
    }

    /// The row `C_t`, derived if it hasn't been. t must be in some task's
    /// window.
    pub(super) fn row(&mut self, proof: &mut dyn ProofLogger, enc: &Encoded, t: i64) -> Line {
        if let Some(row) = self.rows.get(&t) {
            return row.clone();
        }
        // Chain up from the nearest row already derived, or from the point
        // below where no task can be running.
        let mut from = t - 1;
        while !self.rows.contains_key(&from) && !enc.candidates(from).is_empty() {
            from -= 1;
        }
        for u in from + 1..=t {
            let previous = self.rows.get(&(u - 1)).cloned();
            let row = self.derive(proof, enc, u, previous);
            self.rows.insert(u, row);
        }
        self.rows[&t].clone()
    }

    /// `C_t` over the per-time flags, as an inequality.
    fn target(&mut self, proof: &mut dyn ProofLogger, enc: &Encoded, t: i64) -> Ineq {
        let load = enc
            .candidates(t)
            .into_iter()
            .map(|k| {
                (
                    i128::from(enc.tasks[k].height),
                    self.per_time(proof, enc, k, t).cact.lit,
                )
            })
            .collect();
        Ineq::le(load, enc.capacity.into())
    }

    fn derive(
        &mut self,
        proof: &mut dyn ProofLogger,
        enc: &Encoded,
        t: i64,
        previous: Option<Line>,
    ) -> Line {
        let candidates = enc.candidates(t);
        let most: i64 = candidates.iter().map(|&k| enc.tasks[k].height).sum();
        if most <= enc.capacity {
            // Even every candidate at once fits.
            let target = self.target(proof, enc, t);
            return proof.rup_line(&target);
        }
        self.chain(proof, enc, t, &candidates, previous)
    }

    fn chain(
        &mut self,
        proof: &mut dyn ProofLogger,
        enc: &Encoded,
        t: i64,
        candidates: &[usize],
        previous: Option<Line>,
    ) -> Line {
        let had_window_before = |k: usize| enc.in_window(k, t - 1);
        let base = if previous.is_some() { "" } else { " base" };
        proof.comment(&format!(
            "cumulative {}: capacity row at {t} by chain{base}",
            enc.name
        ));

        // A task whose window opens at t has no flag at t − 1 to say it
        // starts no earlier than t. Its declared lower bound says so
        // instead: the atom sₖ ≥ t, its defining row, and the pin that
        // makes it a unit.
        let mut opening = HashMap::new();
        for &k in candidates {
            if !had_window_before(k) {
                let atom = proof.ge_atom(enc.tasks[k].start, t);
                let pin = atom.pin.clone().expect("a window opens at the lower bound");
                opening.insert(k, (atom.flag.implies.clone(), pin));
            }
        }

        // The target literalised: a flag for "C_t holds", so the split over
        // a row stays resolution.
        let target = self.target(proof, enc, t);
        let holds = proof.define_flag(format!("p[{}][ckpf_{t}]", enc.name), &target);

        // starts_at(k): sₖ = t, a flag over cb(k, t) ∧ ¬cb(k, t − 1), or just
        // cb(k, t) where k's window opens at t.
        let mut starts_at: HashMap<usize, PbLit> = HashMap::new();
        let mut starts_at_flag: HashMap<usize, Flag> = HashMap::new();
        for &k in candidates {
            let now = self.per_time(proof, enc, k, t).cb.lit;
            if had_window_before(k) {
                let before = self.per_time(proof, enc, k, t - 1).cb.lit;
                let index = enc.tasks[k].index;
                let says = Ineq::ge(vec![(1, now), (1, !before)], 2);
                let flag = proof.define_flag(format!("p[{}][ckps_{index}_{t}]", enc.name), &says);
                starts_at.insert(k, flag.lit);
                starts_at_flag.insert(k, flag);
            } else {
                starts_at.insert(k, now);
            }
        }

        // Nobody starts at t: each candidate's term at t is at most its term
        // at t − 1 unless it starts at t, and summed with C_{t−1} and the
        // target's reverse half the loads cancel, leaving
        //
        //     Σ hₖ·starts_at(k) + K·holds ≥ D,
        //
        // with D one in a chain and C + 1 at the base.
        let mut no_start = Pol::default();
        if let Some(previous) = &previous {
            no_start.add(previous, 1);
            // A task whose window closed at t − 1 is not in the target.
            for (k, _) in enc.tasks.iter().enumerate() {
                if had_window_before(k) && !enc.in_window(k, t) {
                    let gone = self.per_time(proof, enc, k, t - 1).cact.lit;
                    no_start.weaken(gone);
                }
            }
        }
        for &k in candidates {
            let height = i128::from(enc.tasks[k].height);
            let now = self.per_time(proof, enc, k, t);
            if let Some(flag) = starts_at_flag.get(&k) {
                let before = self.per_time(proof, enc, k, t - 1);
                // Still running at t means still running at t − 1: a bridge
                // between two thresholds on the same start, at degree two,
                // halved to a clause.
                let mut bridge = Pol::default();
                bridge
                    .add(&now.ca.implies, 1)
                    .add(&before.ca.implied_by, 1)
                    .saturate();
                let bridge = proof.pol(&bridge);
                // ¬cact(k, t) ∨ cact(k, t − 1) ∨ starts_at(k)
                let mut pin = Pol::default();
                pin.add(&bridge, 1)
                    .divide(2)
                    .add(&now.cact.implies, 1)
                    .add(&flag.implied_by, 1)
                    .add(&before.cact.implied_by, 1)
                    .saturate();
                no_start.add(&proof.pol(&pin), height);
            } else {
                // Opening at t: cact(k, t) ⇒ cb(k, t) is one of cact's own
                // conjuncts.
                let clause = Ineq::clause([!now.cact.lit, starts_at[&k]]);
                no_start.add(&proof.rup_line(&clause), height);
            }
        }
        no_start.add(&holds.implied_by, 1);
        let nobody = proof.pol(&no_start);

        // j starts at t: every candidate i running at t is running when j
        // starts, which is sb(i, j) ∧ sa(i, j), so j's checkpoint row bounds
        // the load. One case per j, each the clause ¬starts_at(j) ∨ holds,
        // added at j's coefficient in `nobody` so that starts_at(j) cancels.
        let mut finish = Pol::default();
        finish.add(&nobody, 1);
        for &j in candidates {
            let mut pinned = Vec::new();
            for &i in candidates {
                if i == j {
                    continue;
                }
                let pair = &enc.pairs[&(i, j)];
                let at_i = self.per_time(proof, enc, i, t);
                let at_j = self.per_time(proof, enc, j, t);

                // ¬cb(i, t) ∨ cb(j, t − 1) ∨ sb(i, j):  sᵢ ≤ t ≤ sⱼ
                let mut before = Pol::default();
                before.add(&at_i.cb.implies, 1);
                match opening.get(&j) {
                    None => {
                        let previous_j = self.per_time(proof, enc, j, t - 1);
                        before.add(&previous_j.cb.implied_by, 1)
                    }
                    Some((row, _)) => before.add(row, 1),
                };
                before.add(&pair.sb.implied_by, 1).saturate();
                let before = proof.pol(&before);

                // ¬ca(i, t) ∨ ¬cb(j, t) ∨ sa(i, j):  sᵢ + dᵢ ≥ t + 1 ≥ sⱼ + 1
                let mut after = Pol::default();
                after
                    .add(&at_i.ca.implies, 1)
                    .add(&at_j.cb.implies, 1)
                    .add(&pair.sa.implied_by, 1)
                    .saturate();
                let after = proof.pol(&after);

                // ¬starts_at(j) ∨ ¬cact(i, t) ∨ sact(i, j)
                let mut pin = Pol::default();
                pin.add(&before, 1)
                    .add(&after, 1)
                    .add(&pair.sact.implied_by, 1)
                    .add(&at_i.cact.implies, 1);
                match (starts_at_flag.get(&j), opening.get(&j)) {
                    (Some(flag), _) => pin.add(&flag.implies, 1),
                    (None, Some((_, opening_pin))) => pin.add(opening_pin, 1),
                    (None, None) => unreachable!("a candidate either continues or opens"),
                };
                pin.saturate();
                pinned.push((i, proof.pol(&pin)));
            }
            let case = self.case(proof, enc, t, j, starts_at[&j], &pinned, &holds);
            finish.add(&case, i128::from(enc.tasks[j].height));
        }
        // What is left is `holds` at some coefficient against degree D:
        // saturating brings both to D, and at the base dividing by D gives
        // the unit.
        finish.saturate();
        if previous.is_none() {
            finish.divide(i128::from(enc.capacity) + 1);
        }
        let holds_line = proof.pol(&finish);

        // And the target out from behind its flag.
        let mut unwrap = Pol::default();
        unwrap
            .add(&holds.implies, 1)
            .add(&holds_line, guard_coefficient(&target));
        proof.pol(&unwrap)
    }

    /// The case "j starts at t", as the clause `¬guard ∨ holds`: j's
    /// checkpoint row, each candidate's pair term swapped for its per-time
    /// one by its pin, j's own term added, and the load cancelled against
    /// the target's reverse half.
    #[allow(clippy::too_many_arguments)]
    fn case(
        &mut self,
        proof: &mut dyn ProofLogger,
        enc: &Encoded,
        t: i64,
        j: usize,
        guard: PbLit,
        pinned: &[(usize, Line)],
        holds: &Flag,
    ) -> Line {
        let mut pol = Pol::default();
        pol.add(
            &Line::row(&enc.name, &format!("scap_{}", enc.tasks[j].index)),
            1,
        );
        // A task with no flag at t is not in the target: weakened away.
        for (i, _) in enc.tasks.iter().enumerate() {
            if i != j && !enc.in_window(i, t) {
                pol.weaken(enc.pairs[&(i, j)].sact.lit);
            }
        }
        for (i, pin) in pinned {
            pol.add(pin, i128::from(enc.tasks[*i].height));
        }
        // j's own height is on the right of its checkpoint row, so its term
        // goes on as an axiom.
        let own = self.per_time(proof, enc, j, t).cact.lit;
        pol.axiom(!own, i128::from(enc.tasks[j].height));
        pol.add(&holds.implied_by, 1);
        // The guard, which the arithmetic gives only when there was another
        // task to pin.
        pol.axiom(!guard, 1);
        pol.saturate();
        proof.pol(&pol)
    }
}

/// The coefficient `flag ⇒ ineq` puts on `¬flag`, which is what cancels
/// it against the unit `flag`.
fn guard_coefficient(ineq: &Ineq) -> i128 {
    let min_lhs: i128 = ineq.terms.iter().map(|&(c, _)| c.min(0)).sum();
    (ineq.rhs - min_lhs).max(0)
}
