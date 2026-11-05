//! Hard sudoku: 81 variables, 27 all-different constraints.
//!
//! Puzzles are 81-character strings, row by row, `.` for an empty cell.
//! Solutions are checked against the sudoku rules and the clues by an
//! independent checker, and against the known unique solution.

use solver::{Config, Model, Outcome, VarId, VarOrder};

/// Arto Inkala's "world's hardest sudoku" (2012). Value elimination alone
/// solves almost nothing here, so search does the work.
const INKALA: &str =
    "8..........36......7..9.2...5...7.......457.....1...3...1....68..85...1..9....4..";
const INKALA_SOLUTION: &str =
    "812753649943682175675491283154237896369845721287169534521974368438526917796318452";

/// Built to defeat naive backtracking: the first row's answer is 987654321,
/// the worst case for "first cell, smallest value first".
const ANTI_BRUTE_FORCE: &str =
    "..............3.85..1.2.......5.7.....4...1...9.......5......73..2.1........4...9";
const ANTI_BRUTE_FORCE_SOLUTION: &str =
    "987654321246173985351928746128537694634892157795461832519286473472319568863745219";

/// Inkala with an extra clue, a 2 in row 1 column 2. It breaks no rule
/// directly, but the unique solution has a 1 there, so there is no solution.
/// Proving that means exhausting the search tree.
const INKALA_UNSAT: &str =
    "82.........36......7..9.2...5...7.......457.....1...3...1....68..85...1..9....4..";

/// Build the model: one variable per cell, a clue's domain is just its value.
fn sudoku(puzzle: &str) -> (Model, Vec<VarId>) {
    assert_eq!(puzzle.len(), 81, "a puzzle has 81 cells");
    let mut model = Model::new();
    let cells: Vec<VarId> = puzzle
        .chars()
        .map(|ch| match ch {
            '.' | '0' => model.int_var(1, 9),
            d => {
                let v = d.to_digit(10).expect("digit or '.'") as i64;
                model.int_var(v, v)
            }
        })
        .collect();

    for i in 0..9 {
        let row: Vec<VarId> = (0..9).map(|j| cells[9 * i + j]).collect();
        let col: Vec<VarId> = (0..9).map(|j| cells[9 * j + i]).collect();
        let (br, bc) = (3 * (i / 3), 3 * (i % 3));
        let block: Vec<VarId> = (0..9)
            .map(|j| cells[9 * (br + j / 3) + bc + j % 3])
            .collect();
        model.all_different(&row);
        model.all_different(&col);
        model.all_different(&block);
    }
    (model, cells)
}

/// Does `grid` obey the rules and keep every clue of `puzzle`?
fn is_valid_solution(puzzle: &str, grid: &[i64]) -> bool {
    let is_permutation = |cells: [usize; 9]| {
        let mut seen = [false; 10];
        cells.iter().all(|&c| {
            let v = grid[c];
            (1..=9).contains(&v) && !std::mem::replace(&mut seen[v as usize], true)
        })
    };
    let clues_kept = puzzle
        .chars()
        .zip(grid)
        .all(|(ch, &v)| ch == '.' || ch.to_digit(10) == Some(v as u32));

    clues_kept
        && (0..9).all(|i| {
            let (br, bc) = (3 * (i / 3), 3 * (i % 3));
            is_permutation(std::array::from_fn(|j| 9 * i + j))
                && is_permutation(std::array::from_fn(|j| 9 * j + i))
                && is_permutation(std::array::from_fn(|j| 9 * (br + j / 3) + bc + j % 3))
        })
}

fn to_string(grid: &[i64]) -> String {
    grid.iter().map(|v| v.to_string()).collect()
}

fn solve(puzzle: &str, var_order: VarOrder) -> Option<Vec<i64>> {
    let (model, cells) = sudoku(puzzle);
    let config = Config {
        var_order,
        ..Config::default()
    };
    match solver::solve(&model, &config).expect("solver I/O error") {
        Outcome::Satisfiable(sol) => Some(cells.iter().map(|&c| sol.value(c)).collect()),
        Outcome::Unsatisfiable => None,
        Outcome::Unknown => panic!("solver gave up"),
    }
}

// --- The checker itself ------------------------------------------------------

#[test]
fn checker_accepts_known_solutions() {
    let grid = |s: &str| -> Vec<i64> { s.bytes().map(|b| (b - b'0') as i64).collect() };
    assert!(is_valid_solution(INKALA, &grid(INKALA_SOLUTION)));
    assert!(is_valid_solution(
        ANTI_BRUTE_FORCE,
        &grid(ANTI_BRUTE_FORCE_SOLUTION)
    ));
}

#[test]
fn checker_rejects_broken_grids() {
    let mut g: Vec<i64> = INKALA_SOLUTION.bytes().map(|b| (b - b'0') as i64).collect();
    g.swap(1, 2); // breaks two columns
    assert!(!is_valid_solution(INKALA, &g));
    // A valid grid that ignores a clue.
    let other: Vec<i64> = ANTI_BRUTE_FORCE_SOLUTION
        .bytes()
        .map(|b| (b - b'0') as i64)
        .collect();
    assert!(!is_valid_solution(INKALA, &other));
}

// --- The solver --------------------------------------------------------------

#[test]
fn solves_inkala() {
    for order in [VarOrder::SmallestDomain, VarOrder::InputOrder] {
        let grid = solve(INKALA, order).expect("Inkala has a solution");
        assert!(is_valid_solution(INKALA, &grid), "{order:?}: invalid grid");
        assert_eq!(to_string(&grid), INKALA_SOLUTION, "{order:?}");
    }
}

#[test]
fn solves_anti_brute_force() {
    // InputOrder is the case this puzzle was designed to punish; run it with
    // `cargo test --release -- --ignored` if you want to watch it suffer.
    let grid = solve(ANTI_BRUTE_FORCE, VarOrder::SmallestDomain).expect("has a solution");
    assert!(is_valid_solution(ANTI_BRUTE_FORCE, &grid));
    assert_eq!(to_string(&grid), ANTI_BRUTE_FORCE_SOLUTION);
}

#[test]
#[ignore = "slow: naive variable order on a puzzle built to defeat it"]
fn solves_anti_brute_force_in_input_order() {
    let grid = solve(ANTI_BRUTE_FORCE, VarOrder::InputOrder).expect("has a solution");
    assert_eq!(to_string(&grid), ANTI_BRUTE_FORCE_SOLUTION);
}

#[test]
fn proves_inkala_with_wrong_clue_unsatisfiable() {
    assert_eq!(solve(INKALA_UNSAT, VarOrder::SmallestDomain), None);
}
