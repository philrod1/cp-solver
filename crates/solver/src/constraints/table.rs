use std::collections::HashSet;

use super::{Constraint, PropagationContext, Propagator};
use crate::domain::Conflict;
use crate::engine::Engine;
use crate::model::VarId;
use crate::proof::{Ineq, Justification, NotEncodable, OpbEncoder, Reason};
use crate::store::Event;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Cell {
    /// `*`: matches every value.
    Any,
    Val(i64),
}

impl Cell {
    pub fn matches(self, v: i64) -> bool {
        match self {
            Cell::Any => true,
            Cell::Val(w) => w == v,
        }
    }
}

impl From<i64> for Cell {
    fn from(v: i64) -> Self {
        Cell::Val(v)
    }
}

#[derive(Clone, Debug)]
pub struct Table {
    vars: Vec<VarId>,
    rows: Vec<Vec<Cell>>, // Any = *
}

impl Table {
    pub fn new(vars: &[VarId], rows: &[Vec<Cell>]) -> Self {
        // A row of the wrong length makes the whole constraint unsatisfiable
        if rows.iter().any(|r| r.len() != vars.len()) {
            return Self {
                vars: vars.to_vec(),
                rows: Vec::new(),
            };
        }
        let mut seen = HashSet::new();
        let rows = rows
            .iter()
            .filter_map(|r| merge_repeats(vars, r))
            .filter(|r| seen.insert(r.clone()))
            .collect();
        Self {
            vars: vars.to_vec(),
            rows,
        }
    }
}

/// Make the cells of a repeated variable agree: `*` takes the other cell's
/// value, and two different values mean the row can never match.
fn merge_repeats(vars: &[VarId], row: &[Cell]) -> Option<Vec<Cell>> {
    let mut row = row.to_vec();
    for i in 0..vars.len() {
        for j in i + 1..vars.len() {
            if vars[i] != vars[j] {
                continue;
            }
            let merged = match (row[i], row[j]) {
                (Cell::Any, c) | (c, Cell::Any) => c,
                (Cell::Val(a), Cell::Val(b)) if a == b => Cell::Val(a),
                _ => return None,
            };
            row[i] = merged;
            row[j] = merged;
        }
    }
    Some(row)
}

impl Constraint for Table {
    fn post(&self, engine: &mut Engine) {
        engine.add(Box::new(Prop {
            vars: self.vars.clone(),
            rows: self.rows.clone(),
        }));
    }

    /// As GCS writes it: a flag `x[name][k]` for each row, true exactly
    /// when row `k` matches, and at least one of them true.
    ///
    /// ```text
    /// @x[name][k][r]   flag => x0 = v0 && x1 = v1 && ...
    /// @x[name][k][f]  !flag => !(x0 = v0 && x1 = v1 && ...)
    /// @c[name][al1]   some flag
    /// ```
    ///
    /// Each `x = v` is an atom the OPB defines, so that the proof can see
    /// a row ruled out as soon as one of its values is. Wildcards add
    /// nothing, and nor does a value a fixed variable always has. A value
    /// outside its variable's declared domain means the row never matches,
    /// so its flag is simply false.
    fn encode(&self, opb: &mut OpbEncoder<'_>) -> Result<(), NotEncodable> {
        let mut flags = Vec::new();
        for (k, row) in self.rows.iter().enumerate() {
            // A repeated variable has the same cell everywhere (see
            // `merge_repeats`), so only its first position counts.
            let cells: Vec<(VarId, i64)> = self
                .vars
                .iter()
                .zip(row)
                .enumerate()
                .filter(|&(i, (x, _))| !self.vars[..i].contains(x))
                .filter_map(|(_, (&x, &cell))| match cell {
                    Cell::Val(v) => Some((x, v)),
                    Cell::Any => None,
                })
                .collect();
            let possible = cells.iter().all(|&(x, v)| {
                let (lo, hi) = opb.declared(x);
                (lo..=hi).contains(&v)
            });
            let flag = if possible {
                let mut lits = Vec::new();
                for &(x, v) in &cells {
                    let (lo, hi) = opb.declared(x);
                    if lo < hi {
                        lits.push((1, opb.eq(x, v)));
                    }
                }
                let n = lits.len() as i128;
                opb.reified_flag(&[k], Ineq::ge(lits, n))
            } else {
                let flag = opb.indexed_flag(&[k]);
                opb.unlabelled(&Ineq::clause([!flag]));
                flag
            };
            flags.push(flag);
        }
        opb.row("al1", &Ineq::clause(flags));
        Ok(())
    }
}

struct Prop {
    vars: Vec<VarId>,
    rows: Vec<Vec<Cell>>,
}

impl Propagator for Prop {
    fn name(&self) -> &'static str {
        "table"
    }

    fn watches(&self) -> Vec<(VarId, Event)> {
        self.vars.iter().map(|&x| (x, Event::Domain)).collect()
    }

    fn propagate(&mut self, ctx: &mut PropagationContext<'_>) -> Result<(), Conflict> {
        let n = self.vars.len();
        let mut supported: Vec<HashSet<i64>> = vec![HashSet::new(); n];
        let mut wildcard = vec![false; n];
        let mut any_live = false;

        for row in &self.rows {
            let live = row.iter().zip(&self.vars).all(|(&cell, &x)| match cell {
                Cell::Any => true,
                Cell::Val(v) => ctx.domain(x).contains(v),
            });
            if !live {
                continue;
            }
            any_live = true;
            for (i, &cell) in row.iter().enumerate() {
                match cell {
                    Cell::Any => wildcard[i] = true,
                    Cell::Val(v) => {
                        supported[i].insert(v);
                    }
                }
            }
        }
        // Every row was ruled out by the current domains: RUP, with the
        // rows' encoding.
        let why = Justification::Rup(Reason::Domains(&self.vars));
        if !any_live {
            return ctx.fail(why);
        }

        for (i, &x) in self.vars.iter().enumerate() {
            if wildcard[i] {
                continue; // every value is supported
            }
            let values: Vec<i64> = ctx.domain(x).iter().collect();
            for v in values {
                if !supported[i].contains(&v) {
                    ctx.remove(x, v, why)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use proptest::prelude::*;

    use super::{Cell, Table};
    use crate::constraints::testing::{propagate, values};
    use crate::engine::Engine;
    use crate::model::{Model, VarId};
    use crate::proof::NullLogger;
    use crate::store::DomainStore;

    const ANY: Cell = Cell::Any;

    /// Rows from plain numbers, for tables without wildcards.
    fn rows(rs: &[&[i64]]) -> Vec<Vec<Cell>> {
        rs.iter()
            .map(|r| r.iter().map(|&v| v.into()).collect())
            .collect()
    }

    fn set(vs: &[i64]) -> BTreeSet<i64> {
        vs.iter().copied().collect()
    }

    /// All permutations of 1..=3, the worked example from the notes.
    fn permutations() -> Vec<Vec<Cell>> {
        rows(&[
            &[1, 2, 3],
            &[1, 3, 2],
            &[2, 1, 3],
            &[2, 3, 1],
            &[3, 1, 2],
            &[3, 2, 1],
        ])
    }

    // --- Propagation ---------------------------------------------------------

    #[test]
    fn nothing_to_prune_when_every_value_is_used() {
        let mut m = Model::new();
        let v: Vec<VarId> = (0..3).map(|_| m.int_var(1, 3)).collect();
        m.post(Table::new(&v, &permutations()));
        let (s, r) = propagate(&m);
        assert!(r.is_ok());
        for &x in &v {
            assert_eq!(values(&s, x), set(&[1, 2, 3]));
        }
    }

    #[test]
    fn worked_example_finds_the_hall_set() {
        // x and z can't be 3, so the rows left are (1,3,2) and (2,3,1):
        // y must be 3.
        let mut m = Model::new();
        let (x, y, z) = (m.int_var(1, 2), m.int_var(1, 3), m.int_var(1, 2));
        m.post(Table::new(&[x, y, z], &permutations()));
        let (s, r) = propagate(&m);
        assert!(r.is_ok());
        assert_eq!(values(&s, y), set(&[3]));
        assert_eq!(values(&s, x), set(&[1, 2]));
        assert_eq!(values(&s, z), set(&[1, 2]));
    }

    #[test]
    fn values_used_by_no_row_are_removed() {
        let mut m = Model::new();
        let (x, y) = (m.int_var(1, 3), m.int_var(1, 3));
        m.post(Table::new(&[x, y], &rows(&[&[1, 2], &[2, 1]])));
        let (s, _) = propagate(&m);
        assert_eq!(values(&s, x), set(&[1, 2]));
        assert_eq!(values(&s, y), set(&[1, 2]));
    }

    #[test]
    fn rows_with_values_outside_the_domain_are_dead() {
        // (5, 1) can never match x ∈ 1..3, so only (1, 2) is left.
        let mut m = Model::new();
        let (x, y) = (m.int_var(1, 3), m.int_var(1, 3));
        m.post(Table::new(&[x, y], &rows(&[&[5, 1], &[1, 2]])));
        let (s, _) = propagate(&m);
        assert_eq!(values(&s, x), set(&[1]));
        assert_eq!(values(&s, y), set(&[2]));
    }

    #[test]
    fn no_live_row_is_a_conflict() {
        let mut m = Model::new();
        let (x, y) = (m.int_var(1, 2), m.int_var(1, 2));
        m.post(Table::new(&[x, y], &rows(&[&[3, 3], &[1, 4]])));
        assert!(propagate(&m).1.is_err());
    }

    #[test]
    fn a_table_with_no_rows_is_unsatisfiable() {
        let mut m = Model::new();
        let x = m.int_var(1, 2);
        m.post(Table::new(&[x], &[]));
        assert!(propagate(&m).1.is_err());
    }

    // --- Wildcards -----------------------------------------------------------

    #[test]
    fn wildcard_supports_every_value() {
        // ( * 2 * ): the middle is fixed, the others are untouched.
        let mut m = Model::new();
        let v: Vec<VarId> = (0..3).map(|_| m.int_var(1, 3)).collect();
        m.post(Table::new(&v, &[vec![ANY, 2.into(), ANY]]));
        let (s, _) = propagate(&m);
        assert_eq!(values(&s, v[0]), set(&[1, 2, 3]));
        assert_eq!(values(&s, v[1]), set(&[2]));
        assert_eq!(values(&s, v[2]), set(&[1, 2, 3]));
    }

    #[test]
    fn wildcard_in_a_dead_row_supports_nothing() {
        // (*, 9) is dead because y can't be 9, so its wildcard doesn't
        // protect x: only (1, 2) is live.
        let mut m = Model::new();
        let (x, y) = (m.int_var(1, 3), m.int_var(1, 3));
        m.post(Table::new(
            &[x, y],
            &[vec![ANY, 9.into()], vec![1.into(), 2.into()]],
        ));
        let (s, _) = propagate(&m);
        assert_eq!(values(&s, x), set(&[1]));
    }

    #[test]
    fn wildcards_and_values_combine() {
        // (1 * 3) and (* 2 *): every value of x and z is supported by the
        // second row, and so is y = 2; y = 1 and y = 3 by the first.
        let mut m = Model::new();
        let v: Vec<VarId> = (0..3).map(|_| m.int_var(1, 3)).collect();
        m.post(Table::new(
            &v,
            &[vec![1.into(), ANY, 3.into()], vec![ANY, 2.into(), ANY]],
        ));
        let (s, r) = propagate(&m);
        assert!(r.is_ok());
        for &x in &v {
            assert_eq!(values(&s, x), set(&[1, 2, 3]));
        }
    }

    // --- Cleaning up rows when the constraint is built ----------------------

    #[test]
    fn a_row_of_the_wrong_length_makes_it_unsatisfiable() {
        // (1, 2) would fit, but (1) is the wrong length.
        let mut m = Model::new();
        let (x, y) = (m.int_var(1, 3), m.int_var(1, 3));
        m.post(Table::new(
            &[x, y],
            &[vec![1.into(), 2.into()], vec![1.into()]],
        ));
        assert!(propagate(&m).1.is_err());
    }

    #[test]
    fn repeated_variable_needs_matching_cells() {
        // Over (x, x): (1, 2) can never match; (*, 3) means x = 3.
        let mut m = Model::new();
        let x = m.int_var(1, 4);
        m.post(Table::new(
            &[x, x],
            &[vec![1.into(), 2.into()], vec![ANY, 3.into()]],
        ));
        let (s, r) = propagate(&m);
        assert!(r.is_ok());
        assert_eq!(values(&s, x), set(&[3]));
    }

    #[test]
    fn repeated_variable_three_times() {
        // (*, *, 1) over (x, x, x) means x = 1.
        let mut m = Model::new();
        let x = m.int_var(0, 3);
        m.post(Table::new(&[x, x, x], &[vec![ANY, ANY, 1.into()]]));
        let (s, _) = propagate(&m);
        assert_eq!(values(&s, x), set(&[1]));
    }

    #[test]
    fn repeated_variable_with_no_matching_row_conflicts() {
        let mut m = Model::new();
        let x = m.int_var(1, 4);
        m.post(Table::new(&[x, x], &rows(&[&[1, 2], &[3, 4]])));
        assert!(propagate(&m).1.is_err());
    }

    #[test]
    fn repeated_variable_rows_that_only_look_live() {
        // Over (x, x), (1, 2) and (2, 1) can never match. Without the
        // clean-up, both rows look live and every value of x looks
        // supported, so the conflict would be missed.
        let mut m = Model::new();
        let x = m.int_var(1, 2);
        m.post(Table::new(&[x, x], &rows(&[&[1, 2], &[2, 1]])));
        assert!(propagate(&m).1.is_err());
    }

    #[test]
    fn duplicate_rows_are_dropped_and_change_nothing() {
        let (x, y) = (VarId(0), VarId(1));
        let plain = Table::new(&[x, y], &rows(&[&[1, 2], &[2, 1]]));
        let doubled = Table::new(&[x, y], &rows(&[&[1, 2], &[2, 1], &[1, 2], &[2, 1]]));
        assert_eq!(doubled.rows, plain.rows);
    }

    #[test]
    fn zero_arity_tables() {
        // No variables: one empty row is "true", no rows is "false".
        let mut m = Model::new();
        m.post(Table::new(&[], &[vec![]]));
        assert!(propagate(&m).1.is_ok());
        let mut m = Model::new();
        m.post(Table::new(&[], &[]));
        assert!(propagate(&m).1.is_err());
    }

    // --- Backtracking --------------------------------------------------------

    #[test]
    fn rows_come_back_after_backtracking() {
        // Rows (1,1), (2,2), (2,3). Under x = 1 only (1,1) is live, so y = 1.
        // After backtracking and trying x = 2, the other two rows must be
        // live again. A propagator that deletes dead rows from its own
        // state would wrongly report a conflict here.
        let mut m = Model::new();
        let (x, y) = (m.int_var(1, 2), m.int_var(1, 3));
        m.post(Table::new(&[x, y], &rows(&[&[1, 1], &[2, 2], &[2, 3]])));

        let mut store = DomainStore::new(&m);
        let mut engine = Engine::new(m.num_vars());
        for c in m.constraints() {
            c.post(&mut engine);
        }
        engine.propagate(&mut store, &mut NullLogger).unwrap();

        store.push_level();
        let event = store.fix(x, 1).unwrap().unwrap();
        engine.notify(x, event);
        engine.propagate(&mut store, &mut NullLogger).unwrap();
        assert_eq!(values(&store, y), set(&[1]));

        store.backtrack();
        store.push_level();
        let event = store.fix(x, 2).unwrap().unwrap();
        engine.notify(x, event);
        assert!(engine.propagate(&mut store, &mut NullLogger).is_ok());
        assert_eq!(values(&store, y), set(&[2, 3]));
    }

    #[test]
    fn wakes_on_any_removal_not_just_fixing() {
        // Rows (1,1), (2,2), (3,3). Removing 1 from x leaves it unfixed,
        // but y must still lose 1. A table that only watches for fixed
        // variables would sleep through this.
        let mut m = Model::new();
        let (x, y) = (m.int_var(1, 3), m.int_var(1, 3));
        m.post(Table::new(&[x, y], &rows(&[&[1, 1], &[2, 2], &[3, 3]])));

        let mut store = DomainStore::new(&m);
        let mut engine = Engine::new(m.num_vars());
        for c in m.constraints() {
            c.post(&mut engine);
        }
        engine.propagate(&mut store, &mut NullLogger).unwrap();

        store.push_level();
        let event = store.remove(x, 1).unwrap().unwrap();
        engine.notify(x, event);
        engine.propagate(&mut store, &mut NullLogger).unwrap();
        assert_eq!(values(&store, y), set(&[2, 3]));
    }

    // --- Property test: exact against brute force ----------------------------

    fn cell() -> impl Strategy<Value = Cell> {
        prop_oneof![1 => Just(Cell::Any), 4 => (-3i64..=4).prop_map(Cell::Val)]
    }

    proptest! {
        /// Table propagation is exact: after propagating, each variable
        /// holds precisely the values it takes in some solution, and it
        /// fails precisely when there are no solutions. The scope may
        /// repeat variables, which exercises the row clean-up too.
        #[test]
        fn keeps_exactly_the_values_in_some_solution(
            domains in prop::collection::vec((-2i64..=2, 0i64..=3), 1..=3),
            scope_picks in prop::collection::vec(0usize..3, 1..=4),
            row_cells in prop::collection::vec(prop::collection::vec(cell(), 4), 0..=6),
        ) {
            let mut m = Model::new();
            let vars: Vec<VarId> = domains.iter().map(|&(lo, w)| m.int_var(lo, lo + w)).collect();
            let scope: Vec<VarId> = scope_picks.iter().map(|&i| vars[i % vars.len()]).collect();
            let table_rows: Vec<Vec<Cell>> =
                row_cells.iter().map(|r| r[..scope.len()].to_vec()).collect();
            m.post(Table::new(&scope, &table_rows));
            let (s, result) = propagate(&m);

            // Brute force: every assignment of the variables, and which
            // values appear in a solution.
            let mut in_a_solution: Vec<BTreeSet<i64>> = vec![BTreeSet::new(); vars.len()];
            let mut vals: Vec<i64> = domains.iter().map(|&(lo, _)| lo).collect();
            loop {
                let value_of = |x: VarId| vals[x.0 as usize];
                let solution = table_rows.iter().any(|row| {
                    row.iter().zip(&scope).all(|(&c, &x)| c.matches(value_of(x)))
                });
                if solution {
                    for (i, &v) in vals.iter().enumerate() {
                        in_a_solution[i].insert(v);
                    }
                }
                let Some(i) = (0..vals.len()).find(|&i| vals[i] < domains[i].0 + domains[i].1) else {
                    break;
                };
                vals[i] += 1;
                for j in 0..i {
                    vals[j] = domains[j].0;
                }
            }

            if in_a_solution[0].is_empty() {
                prop_assert!(result.is_err(), "no solutions, but propagation succeeded");
            } else {
                prop_assert!(result.is_ok(), "there are solutions, but propagation failed");
                for (i, &x) in vars.iter().enumerate() {
                    // A variable outside the scope is unconstrained.
                    let expected = if scope.contains(&x) {
                        in_a_solution[i].clone()
                    } else {
                        (domains[i].0..=domains[i].0 + domains[i].1).collect()
                    };
                    prop_assert_eq!(values(&s, x), expected, "variable {}", i);
                }
            }
        }
    }
}
