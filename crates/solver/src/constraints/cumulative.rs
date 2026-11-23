//! Cumulative: tasks share a resource of fixed capacity. Task i starts at
//! `sᵢ`, runs for `dᵢ` time steps and uses `rᵢ` of the resource while it
//! runs, and at every time t
//!
//! ```text
//! Σ { rᵢ : sᵢ ≤ t < sᵢ + dᵢ } ≤ C
//! ```
//!
//! Durations, heights and the capacity are constants. Propagation is by
//! time-tabling: a task whose latest start is before its earliest end must
//! be running in between (its *compulsory part*), and a task can't start
//! where it would overlap compulsory parts that leave too little room for
//! it. That prunes bounds only, and is not complete: deciding whether a
//! Cumulative can be satisfied at all is NP-hard.
//!
//! The proof encoding is the Glasgow Constraint Solver's and CakePB-CP's
//! start-checkpoint one (see [`Cumulative::encode`]). The rows time-tabling
//! cites, one per time point, are derived from it in the proof; see
//! [`recovery`].

mod recovery;

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use super::{Constraint, PropagationContext, Propagator};
use crate::domain::Conflict;
use crate::engine::Engine;
use crate::lit::Lit;
use crate::model::VarId;
use crate::proof::{Flag, Ineq, Justification, Line, NotEncodable, OpbEncoder, Reason};
use crate::store::Event;
use recovery::Recovery;

#[derive(Clone, Copy, Debug)]
struct Task {
    /// The task's position among all the tasks given, which names its
    /// flags and rows.
    index: usize,
    start: VarId,
    duration: i64,
    height: i64,
}

/// What the encoding wrote, for the proof steps that cite it: shared by
/// the constraint, which writes it, and the propagator. Empty when no
/// proof is being written.
type Bridge = Arc<Mutex<Option<Encoded>>>;

#[derive(Clone, Debug)]
pub struct Cumulative {
    tasks: Vec<Task>,
    capacity: i64,
    bridge: Bridge,
}

impl Cumulative {
    /// Task i starts at `starts[i]`, runs for `durations[i]` and uses
    /// `heights[i]`. Panics if the lengths differ or any duration, height
    /// or the capacity is negative.
    pub fn new(starts: &[VarId], durations: &[i64], heights: &[i64], capacity: i64) -> Self {
        assert!(
            starts.len() == durations.len() && starts.len() == heights.len(),
            "one duration and one height per task"
        );
        assert!(capacity >= 0, "negative capacity");
        let tasks = starts
            .iter()
            .zip(durations)
            .zip(heights)
            .enumerate()
            .map(|(index, ((&start, &duration), &height))| {
                assert!(duration >= 0 && height >= 0, "negative duration or height");
                Task {
                    index,
                    start,
                    duration,
                    height,
                }
            })
            // A task that takes no time or no resource constrains nothing.
            .filter(|t| t.duration > 0 && t.height > 0)
            .collect();
        Self {
            tasks,
            capacity,
            bridge: Bridge::default(),
        }
    }
}

impl Constraint for Cumulative {
    fn post(&self, engine: &mut Engine) {
        engine.add(Box::new(Prop {
            tasks: self.tasks.clone(),
            capacity: self.capacity,
            bridge: Arc::clone(&self.bridge),
            recovery: Recovery::default(),
        }));
    }

    /// As the Glasgow Constraint Solver and CakePB-CP write it: for each
    /// ordered pair (i, j) of tasks, with i, j their positions, flags fully
    /// reified (`[r]` flag ⇒ ineq, `[f]` ¬flag ⇒ ¬ineq)
    ///
    /// ```text
    /// v[name][i_j][sb]    sᵢ ≤ sⱼ              i started when j starts
    /// v[name][i_j][sa]    sᵢ + dᵢ ≥ sⱼ + 1     i not finished when j starts
    /// v[name][i_j][sact]  sb ∧ sa              i running when j starts
    /// ```
    ///
    /// and for each task j, the capacity when it starts:
    ///
    /// ```text
    /// @c[name][scap_j]    Σ { rᵢ·sact(i, j) : i ≠ j } ≤ C − rⱼ
    /// ```
    ///
    /// The load only rises when some task starts, so checking it at every
    /// start checks it everywhere. The size is quadratic in the number of
    /// tasks, whatever the length of the schedule. Tasks with no duration or
    /// no height get no flags and no row.
    fn encode(&self, opb: &mut OpbEncoder<'_>) -> Result<(), NotEncodable> {
        let mut pairs = HashMap::new();
        for (j, tj) in self.tasks.iter().enumerate() {
            let mut load = Vec::new();
            for (i, ti) in self.tasks.iter().enumerate() {
                if i == j {
                    continue;
                }
                let gap = opb.linear(&[(1, ti.start), (-1, tj.start)]);
                let values = [ti.index as i64, tj.index as i64];
                let sb = opb.value_flag(&values, "sb", Ineq::le(gap.clone(), 0));
                let sa = opb.value_flag(&values, "sa", Ineq::ge(gap, (1 - ti.duration).into()));
                let both = Ineq::ge(vec![(1, sb.lit), (1, sa.lit)], 2);
                let sact = opb.value_flag(&values, "sact", both);
                load.push((i128::from(ti.height), sact.lit));
                pairs.insert((i, j), Pair { sb, sa, sact });
            }
            let room = i128::from(self.capacity - tj.height);
            opb.row(&format!("scap_{}", tj.index), &Ineq::le(load, room));
        }
        let windows = self
            .tasks
            .iter()
            .map(|t| {
                let (lo, hi) = opb.declared(t.start);
                (lo, hi + t.duration - 1)
            })
            .collect();
        *self.bridge.lock().unwrap() = Some(Encoded {
            name: opb.constraint_name().to_string(),
            tasks: self.tasks.clone(),
            capacity: self.capacity,
            windows,
            pairs,
        });
        Ok(())
    }
}

/// One ordered pair's flags.
#[derive(Debug)]
struct Pair {
    sb: Flag,
    sa: Flag,
    sact: Flag,
}

#[derive(Debug)]
struct Encoded {
    name: String,
    tasks: Vec<Task>,
    capacity: i64,
    /// The times each task can be running, `[first, last]`, from its
    /// declared start domain.
    windows: Vec<(i64, i64)>,
    /// By positions in `tasks`.
    pairs: HashMap<(usize, usize), Pair>,
}

impl Encoded {
    fn in_window(&self, k: usize, t: i64) -> bool {
        let (first, last) = self.windows[k];
        first <= t && t <= last
    }

    /// The tasks that can be running at t.
    fn candidates(&self, t: i64) -> Vec<usize> {
        (0..self.tasks.len())
            .filter(|&k| self.in_window(k, t))
            .collect()
    }
}

struct Prop {
    tasks: Vec<Task>,
    capacity: i64,
    bridge: Bridge,
    recovery: Recovery,
}

/// A stretch of time `[from, to)` that a task can't overlap, because of
/// the compulsory parts of `tasks` (as indices).
struct Blocker {
    from: i64,
    to: i64,
    tasks: Vec<usize>,
}

/// Starts `[lo, hi]` of one task ruled out together: each would have it
/// running at time `at`, alongside the blocker's tasks.
struct Step<'a> {
    lo: i64,
    hi: i64,
    at: i64,
    blocker: &'a Blocker,
}

impl Prop {
    /// The bounds of the tasks in `blockers`, for a reason.
    fn reason_for(&self, bounds: &[(i64, i64)], blockers: &[&Blocker]) -> Vec<Lit> {
        let mut tasks: Vec<usize> = blockers.iter().flat_map(|b| b.tasks.clone()).collect();
        tasks.sort_unstable();
        tasks.dedup();
        tasks
            .iter()
            .flat_map(|&i| {
                let (lb, ub) = bounds[i];
                let s = self.tasks[i].start;
                [Lit::Ge(s, lb), Lit::Lt(s, ub + 1)]
            })
            .collect()
    }

    /// Log what the proof needs before "`reason` ⇒ the tasks running at
    /// `at` overflow" is RUP: the capacity row at `at`, and each task in
    /// `running` pinned as running there, under `reason`. Returns the pins,
    /// to delete once the inference is logged; the row stays, for whatever
    /// cites it next.
    fn log_running(
        &mut self,
        ctx: &mut PropagationContext<'_>,
        enc: &Encoded,
        reason: &[Lit],
        at: i64,
        running: &[usize],
    ) -> Vec<Line> {
        self.recovery.row(ctx.proof, enc, at);
        let mut pins = Vec::new();
        for &k in running {
            let flags = self.recovery.per_time(ctx.proof, enc, k, at);
            for flag in [flags.cb, flags.ca, flags.cact] {
                pins.extend(ctx.rup(reason, &[flag.lit]));
            }
        }
        pins
    }

    /// Log the proof of a push on task j's start: for each step, the tasks
    /// running at its time, and with more than one step, each step as
    /// "reason ∧ lo ≤ sⱼ ≤ hi ⇒ false". The new bound is then RUP from the
    /// steps in a chain, or from the one step's pins. Returns every line
    /// written, to delete once the push is logged.
    fn log_steps(
        &mut self,
        ctx: &mut PropagationContext<'_>,
        enc: &Encoded,
        reason: &[Lit],
        j: usize,
        steps: &[Step<'_>],
    ) -> Vec<Line> {
        let s = self.tasks[j].start;
        let mut helpers = Vec::new();
        for step in steps {
            let mut assumed = reason.to_vec();
            // The first and last steps start from a bound the reason has.
            for lit in [Lit::Ge(s, step.lo), Lit::Lt(s, step.hi + 1)] {
                if !reason.contains(&lit) {
                    assumed.push(lit);
                }
            }
            helpers.extend(self.log_running(ctx, enc, reason, step.at, &step.blocker.tasks));
            helpers.extend(self.log_running(ctx, enc, &assumed, step.at, &[j]));
            if steps.len() > 1 {
                helpers.extend(ctx.rup(&assumed, &[]));
            }
        }
        helpers
    }
}

impl Propagator for Prop {
    fn name(&self) -> &'static str {
        "cumulative"
    }

    fn watches(&self) -> Vec<(VarId, Event)> {
        self.tasks
            .iter()
            .map(|t| (t.start, Event::Bounds))
            .collect()
    }

    /// 1. Compulsory parts: a task with latest start `ub` before its
    ///    earliest end `lb + d` runs throughout `[ub, lb + d)`.
    /// 2. The profile: the stretches of time where compulsory parts
    ///    overlap, and how much they use. Too much is a conflict.
    /// 3. For each task, the stretches that leave it too little room
    ///    (without its own compulsory part) block it. Its earliest start
    ///    moves past every blocked time its earliest placement would cover,
    ///    and its latest start likewise back.
    ///
    /// The starts ruled out go in steps, each one every start that covers
    /// a single blocked time. Each is justified against the capacity row at
    /// that time, with the tasks there pinned as running (see
    /// [`Prop::log_steps`]).
    fn propagate(&mut self, ctx: &mut PropagationContext<'_>) -> Result<(), Conflict> {
        let bounds: Vec<(i64, i64)> = self
            .tasks
            .iter()
            .map(|t| (ctx.domain(t.start).lower(), ctx.domain(t.start).upper()))
            .collect();

        let parts: Vec<(usize, i64, i64)> = self
            .tasks
            .iter()
            .zip(&bounds)
            .enumerate()
            .filter(|(_, (t, (lb, ub)))| *ub < *lb + t.duration)
            .map(|(i, (t, &(lb, ub)))| (i, ub, lb + t.duration))
            .collect();
        let mut times: Vec<i64> = parts.iter().flat_map(|&(_, a, e)| [a, e]).collect();
        times.sort_unstable();
        times.dedup();
        let profile: Vec<Blocker> = times
            .windows(2)
            .map(|w| Blocker {
                from: w[0],
                to: w[1],
                tasks: parts
                    .iter()
                    .filter(|&&(_, a, e)| a <= w[0] && w[1] <= e)
                    .map(|&(i, _, _)| i)
                    .collect(),
            })
            .filter(|b| !b.tasks.is_empty())
            .collect();

        let bridge = Arc::clone(&self.bridge);
        let encoded = bridge.lock().unwrap();
        // No encoding means no proof is being written.
        let enc = encoded.as_ref().filter(|_| ctx.is_logging());

        let heights: Vec<i64> = self.tasks.iter().map(|t| t.height).collect();
        let capacity = self.capacity;
        let height = |tasks: &[usize]| -> i64 { tasks.iter().map(|&i| heights[i]).sum() };
        if let Some(over) = profile.iter().find(|b| height(&b.tasks) > capacity) {
            let reason = self.reason_for(&bounds, &[over]);
            let (at, running) = (over.from, over.tasks.clone());
            let pins = match enc {
                Some(enc) => self.log_running(ctx, enc, &reason, at, &running),
                None => Vec::new(),
            };
            let result = ctx.fail(Justification::Rup(Reason::Lits(&reason)));
            ctx.proof.delete(&pins);
            return result;
        }

        for j in 0..self.tasks.len() {
            let Task {
                start: s,
                duration: d,
                height: r,
                ..
            } = self.tasks[j];
            let (lb, ub) = bounds[j];
            let mut blockers: Vec<Blocker> = profile
                .iter()
                .map(|b| Blocker {
                    from: b.from,
                    to: b.to,
                    tasks: b.tasks.iter().copied().filter(|&i| i != j).collect(),
                })
                .filter(|b| height(&b.tasks) + r > capacity)
                .collect();
            if r > capacity {
                // Too tall to run at all: every placement is blocked.
                blockers.push(Blocker {
                    from: lb,
                    to: ub + d,
                    tasks: Vec::new(),
                });
            }

            // Earliest start: from `est`, find the latest blocked time a
            // start there would cover. Every start in [est, at] covers it,
            // so all of them go in one step.
            let (mut est, mut steps) = (lb, Vec::new());
            while est <= ub {
                let reach = est + d - 1;
                let Some((at, blocker)) = blockers
                    .iter()
                    .filter(|b| b.from <= reach && est < b.to)
                    .map(|b| ((b.to - 1).min(reach), b))
                    .max_by_key(|&(at, _)| at)
                else {
                    break;
                };
                steps.push(Step {
                    lo: est,
                    hi: at.min(ub),
                    at,
                    blocker,
                });
                est = at + 1;
            }
            if est > lb {
                let used: Vec<&Blocker> = steps.iter().map(|step| step.blocker).collect();
                let mut reason = self.reason_for(&bounds, &used);
                reason.push(Lit::Ge(s, lb));
                if est > ub {
                    reason.push(Lit::Lt(s, ub + 1));
                }
                let helpers = match enc {
                    Some(enc) => self.log_steps(ctx, enc, &reason, j, &steps),
                    None => Vec::new(),
                };
                let why = Justification::Rup(Reason::Lits(&reason));
                let result = if est > ub {
                    ctx.fail(why)
                } else {
                    ctx.set_lower(s, est, why)
                };
                // Logged even when it fails, so the helpers have served.
                ctx.proof.delete(&helpers);
                result?;
            }

            // Latest start, the mirror image: the earliest blocked time a
            // start at `lst` would cover rules out [at - d + 1, lst].
            let (mut lst, mut steps) = (ub, Vec::new());
            while lst >= lb {
                let reach = lst + d - 1;
                let Some((at, blocker)) = blockers
                    .iter()
                    .filter(|b| b.from <= reach && lst < b.to)
                    .map(|b| (b.from.max(lst), b))
                    .min_by_key(|&(at, _)| at)
                else {
                    break;
                };
                steps.push(Step {
                    lo: (at - d + 1).max(lb),
                    hi: lst,
                    at,
                    blocker,
                });
                lst = at - d;
            }
            if lst < ub {
                let used: Vec<&Blocker> = steps.iter().map(|step| step.blocker).collect();
                let mut reason = self.reason_for(&bounds, &used);
                reason.push(Lit::Lt(s, ub + 1));
                if lst < lb {
                    reason.push(Lit::Ge(s, lb));
                }
                let helpers = match enc {
                    Some(enc) => self.log_steps(ctx, enc, &reason, j, &steps),
                    None => Vec::new(),
                };
                let why = Justification::Rup(Reason::Lits(&reason));
                let result = if lst < lb {
                    ctx.fail(why)
                } else {
                    ctx.set_upper(s, lst, why)
                };
                ctx.proof.delete(&helpers);
                result?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    use std::ops::ControlFlow;

    use proptest::prelude::*;

    use super::*;
    use crate::constraints::testing::{propagate, values};
    use crate::{Config, Model, enumerate};

    /// Whether tasks starting at `starts` stay within `capacity`, checked
    /// time by time.
    fn fits(starts: &[i64], durations: &[i64], heights: &[i64], capacity: i64) -> bool {
        let first = starts.iter().copied().min().unwrap_or(0);
        let last = starts.iter().zip(durations).map(|(s, d)| s + d).max();
        (first..last.unwrap_or(first)).all(|t| {
            let used: i64 = (0..starts.len())
                .filter(|&i| starts[i] <= t && t < starts[i] + durations[i])
                .map(|i| heights[i])
                .sum();
            used <= capacity
        })
    }

    #[test]
    fn the_brute_force_checker_works() {
        assert!(fits(&[0, 2], &[2, 2], &[1, 1], 1));
        assert!(!fits(&[0, 1], &[2, 2], &[1, 1], 1));
        assert!(fits(&[0, 1], &[2, 2], &[1, 1], 2));
        assert!(fits(&[0, 0], &[0, 3], &[5, 1], 1)); // no duration, no use
        assert!(!fits(&[3], &[1], &[2], 1));
    }

    /// One task per `(lo, hi, duration, height)`, and their start variables.
    fn model(tasks: &[(i64, i64, i64, i64)], capacity: i64) -> (Model, Vec<VarId>) {
        let mut m = Model::new();
        let starts: Vec<VarId> = tasks
            .iter()
            .map(|&(lo, hi, _, _)| m.int_var(lo, hi))
            .collect();
        let durations: Vec<i64> = tasks.iter().map(|t| t.2).collect();
        let heights: Vec<i64> = tasks.iter().map(|t| t.3).collect();
        m.post(Cumulative::new(&starts, &durations, &heights, capacity));
        (m, starts)
    }

    #[test]
    fn overlapping_compulsory_parts_conflict() {
        let (m, _) = model(&[(0, 0, 2, 1), (1, 1, 2, 1)], 1);
        assert!(propagate(&m).1.is_err());
    }

    #[test]
    fn a_compulsory_part_pushes_the_earliest_start() {
        // The first task must run over [1, 3), so the second, which can't
        // start before 1, must wait until 3.
        let (m, s) = model(&[(0, 1, 3, 1), (1, 5, 1, 1)], 1);
        let (store, result) = propagate(&m);
        assert!(result.is_ok());
        assert_eq!(values(&store, s[1]), BTreeSet::from([3, 4, 5]));
    }

    #[test]
    fn a_compulsory_part_pulls_the_latest_start() {
        // Likewise the second task, which can't start after 2, must be
        // done by 1.
        let (m, s) = model(&[(0, 1, 3, 1), (0, 2, 1, 1)], 1);
        let (store, result) = propagate(&m);
        assert!(result.is_ok());
        assert_eq!(values(&store, s[1]), BTreeSet::from([0]));
    }

    #[test]
    fn a_long_block_takes_several_steps() {
        // [0, 6) is taken; a task of length 2 has three steps of starts
        // ruled out: [0, 1], [2, 3] and [4, 5].
        let (m, s) = model(&[(0, 0, 6, 1), (0, 9, 2, 1)], 1);
        let (store, result) = propagate(&m);
        assert!(result.is_ok());
        assert_eq!(values(&store, s[1]), BTreeSet::from([6, 7, 8, 9]));
    }

    #[test]
    fn room_for_both_when_the_capacity_allows() {
        let (m, s) = model(&[(0, 1, 3, 1), (1, 5, 1, 1)], 2);
        let (store, result) = propagate(&m);
        assert!(result.is_ok());
        assert_eq!(values(&store, s[1]).len(), 5);
    }

    #[test]
    fn a_task_too_tall_for_the_resource_fails() {
        let (m, _) = model(&[(0, 3, 1, 3)], 2);
        assert!(propagate(&m).1.is_err());
    }

    #[test]
    fn tasks_with_no_duration_or_height_are_ignored() {
        let (m, s) = model(&[(0, 0, 4, 1), (0, 3, 0, 9), (0, 3, 9, 0)], 1);
        let (store, result) = propagate(&m);
        assert!(result.is_ok());
        assert_eq!(values(&store, s[1]).len(), 4);
        assert_eq!(values(&store, s[2]).len(), 4);
    }

    /// Every assignment to the starts, from `(lo, hi)` domains.
    fn assignments(domains: &[(i64, i64)]) -> Vec<Vec<i64>> {
        domains.iter().fold(vec![vec![]], |acc, &(lo, hi)| {
            acc.into_iter()
                .flat_map(|a| (lo..=hi).map(move |v| [a.clone(), vec![v]].concat()))
                .collect()
        })
    }

    proptest! {
        #[test]
        fn finds_exactly_the_schedules_that_fit(
            tasks in prop::collection::vec((-2i64..=2, 0i64..=3, 0i64..=3, 0i64..=3), 1..=4),
            capacity in 0i64..=4,
        ) {
            let tasks: Vec<(i64, i64, i64, i64)> =
                tasks.iter().map(|&(lo, w, d, r)| (lo, lo + w, d, r)).collect();
            let durations: Vec<i64> = tasks.iter().map(|t| t.2).collect();
            let heights: Vec<i64> = tasks.iter().map(|t| t.3).collect();
            let domains: Vec<(i64, i64)> = tasks.iter().map(|t| (t.0, t.1)).collect();

            let mut expected: Vec<Vec<i64>> = assignments(&domains)
                .into_iter()
                .filter(|s| fits(s, &durations, &heights, capacity))
                .collect();
            expected.sort();

            let (m, starts) = model(&tasks, capacity);
            let mut found = Vec::new();
            enumerate(&m, &Config::default(), |sol| {
                found.push(starts.iter().map(|&s| sol.value(s)).collect::<Vec<i64>>());
                ControlFlow::Continue(())
            })
            .unwrap();
            found.sort();
            prop_assert_eq!(found, expected);
        }
    }
}
