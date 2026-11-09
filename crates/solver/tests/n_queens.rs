use solver::{AllDifferent, Config, Model, NotEqual, Outcome, Solution, VarId};

/// Build the model: `q[i]` is the column of the queen in row `i`.
fn nqueens(n: usize) -> (Model, Vec<VarId>) {
    let mut model = Model::new();
    let q: Vec<VarId> = (0..n).map(|_| model.int_var(0, n as i64 - 1)).collect();

    for i in 0..n {
        for j in i + 1..n {
            let (di, dj) = (i as i64, j as i64);
            model.post(NotEqual::new(q[i], q[j])); // columns
            model.post(NotEqual::with_offsets(q[i], di, q[j], dj)); // / diagonals
            model.post(NotEqual::with_offsets(q[i], -di, q[j], -dj)); // \ diagonals
        }
    }
    (model, q)
}

/// Is `cols` (column of the queen in each row) a valid placement?
fn is_valid_placement(cols: &[i64]) -> bool {
    let n = cols.len() as i64;
    if cols.iter().any(|&c| c < 0 || c >= n) {
        return false;
    }
    for i in 0..cols.len() {
        for j in i + 1..cols.len() {
            let rows_apart = (j - i) as i64;
            let cols_apart = (cols[i] - cols[j]).abs();
            if cols_apart == 0 || cols_apart == rows_apart {
                return false;
            }
        }
    }
    true
}

fn solve(n: usize) -> (Outcome, Vec<VarId>) {
    let (model, q) = nqueens(n);
    let outcome = solver::solve(&model, &Config::default()).expect("solver I/O error");
    (outcome, q)
}

fn columns(solution: &Solution, q: &[VarId]) -> Vec<i64> {
    q.iter().map(|&v| solution.value(v)).collect()
}

// --- The checker itself, so we can trust it ---------------------------------

#[test]
fn checker_accepts_known_solutions() {
    assert!(is_valid_placement(&[0]));
    assert!(is_valid_placement(&[1, 3, 0, 2]));
    assert!(is_valid_placement(&[0, 4, 7, 5, 2, 6, 1, 3]));
}

#[test]
fn checker_rejects_bad_placements() {
    assert!(!is_valid_placement(&[0, 0, 0, 0])); //       same column
    assert!(!is_valid_placement(&[0, 1, 2, 3])); //       same diagonal
    assert!(!is_valid_placement(&[1, 3, 0, 4])); //       column out of range
    assert!(!is_valid_placement(&[2, 0, 3, 1, 0])); //    clash far apart
}

#[test]
fn model_has_expected_size() {
    let (model, q) = nqueens(8);
    assert_eq!(q.len(), 8);
    assert_eq!(model.num_vars(), 8);
    assert_eq!(model.constraints().len(), 3 * 8 * 7 / 2);
}

// --- The solver -------------------------------------------------------------

#[test]
fn finds_valid_solutions() {
    for n in [1, 4, 5, 6, 7, 8, 10, 12] {
        match solve(n) {
            (Outcome::Satisfiable(sol), q) => {
                let cols = columns(&sol, &q);
                assert!(
                    is_valid_placement(&cols),
                    "n={n}: invalid solution {cols:?}"
                );
            }
            (other, _) => panic!("n={n}: expected a solution, got {other:?}"),
        }
    }
}

#[test]
fn proves_no_solution_for_2_and_3() {
    for n in [2, 3] {
        let (outcome, _) = solve(n);
        assert!(
            matches!(outcome, Outcome::Unsatisfiable),
            "n={n}: expected UNSATISFIABLE, got {outcome:?}"
        );
    }
}

// --- The same problem with three all-different constraints ------------------

/// Columns, `/` diagonals and `\` diagonals each all different.
fn nqueens_alldiff(n: usize) -> (Model, Vec<VarId>) {
    let mut model = Model::new();
    let q: Vec<VarId> = (0..n).map(|_| model.int_var(0, n as i64 - 1)).collect();

    let columns: Vec<(VarId, i64)> = q.iter().map(|&v| (v, 0)).collect();
    let diag_up: Vec<(VarId, i64)> = q.iter().enumerate().map(|(i, &v)| (v, i as i64)).collect();
    let diag_down: Vec<(VarId, i64)> = q
        .iter()
        .enumerate()
        .map(|(i, &v)| (v, -(i as i64)))
        .collect();
    model.post(AllDifferent::with_offsets(&columns));
    model.post(AllDifferent::with_offsets(&diag_up));
    model.post(AllDifferent::with_offsets(&diag_down));
    (model, q)
}

#[test]
fn alldiff_model_finds_valid_solutions() {
    for n in [1, 4, 5, 6, 7, 8, 10, 12] {
        let (model, q) = nqueens_alldiff(n);
        match solver::solve(&model, &Config::default()).expect("solver I/O error") {
            Outcome::Satisfiable(sol) => {
                let cols = columns(&sol, &q);
                assert!(
                    is_valid_placement(&cols),
                    "n={n}: invalid solution {cols:?}"
                );
            }
            other => panic!("n={n}: expected a solution, got {other:?}"),
        }
    }
}

#[test]
fn alldiff_model_proves_no_solution_for_2_and_3() {
    for n in [2, 3] {
        let (model, _) = nqueens_alldiff(n);
        let outcome = solver::solve(&model, &Config::default()).expect("solver I/O error");
        assert!(
            matches!(outcome, Outcome::Unsatisfiable),
            "n={n}: expected UNSATISFIABLE, got {outcome:?}"
        );
    }
}
