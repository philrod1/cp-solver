//! `examples/nonogram_row.scp`: one row of a nonogram, solved through the
//! reader's `regular`.
//!
//! The row is ten cells long with the clue "3 2": a block of three filled
//! cells (1), then at least one empty cell (0), then a block of two. As a
//! pattern, `0* 111 0+ 11 0*`. The automaton's states follow the clue:
//!
//! ```text
//! 0  leading 0s, or start the 3-block     ((0 0) (1 1))
//! 1  one 1 of the 3-block                 ((1 2))
//! 2  two 1s                               ((1 3))
//! 3  3-block done: a 0 must follow        ((0 4))
//! 4  the gap, or start the 2-block        ((0 4) (1 5))
//! 5  one 1 of the 2-block                 ((1 6))
//! 6  done: trailing 0s only, accepting    ((0 6))
//! ```
//!
//! Three cells are left over beyond the blocks and the one gap they need,
//! to share among three gaps (before, between, after): C(6, 2) = 15
//! solutions, from 1110110000 to 0000111011.
//!
//! Solutions are checked against the clue directly, by their runs of 1s,
//! without trusting the automaton.

mod common;

use std::collections::HashSet;
use std::ops::ControlFlow;

use lang::{ProbType, read_scp};
use solver::Config;

const ROW: &str = include_str!("../../../examples/nonogram_row.scp");

/// The lengths of the runs of 1s in `cells`, in order.
fn runs(cells: &[i64]) -> Vec<usize> {
    cells
        .split(|&c| c == 0)
        .map(<[i64]>::len)
        .filter(|&n| n > 0)
        .collect()
}

#[test]
fn the_clue_checker_works() {
    assert_eq!(runs(&[1, 1, 1, 0, 1, 1, 0, 0, 0, 0]), [3, 2]);
    assert_eq!(runs(&[0, 0, 1, 1, 1, 0, 0, 0, 1, 1]), [3, 2]);
    assert_eq!(runs(&[1, 1, 1, 1, 1, 0, 0, 0, 0, 0]), [5]);
    assert_eq!(runs(&[0; 10]), Vec::<usize>::new());
}

#[test]
fn every_placement_of_the_clue() {
    let (model, scp) = read_scp(ROW).unwrap();
    assert_eq!(scp.prob_type, ProbType::Enumerate);
    let cells: Vec<_> = (0..10)
        .map(|i| scp.var(&format!("c{i}")).unwrap())
        .collect();

    let mut seen = HashSet::new();
    let count = solver::enumerate(&model, &Config::default(), |sol| {
        let row: Vec<i64> = cells.iter().map(|&c| sol.value(c)).collect();
        assert_eq!(runs(&row), [3, 2], "{row:?} doesn't fit the clue");
        assert!(seen.insert(row), "a solution was reported twice");
        ControlFlow::Continue(())
    })
    .unwrap();
    assert_eq!(count, 15);
}

#[test]
fn the_proof_checks() {
    let stem = std::path::PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("nonogram_row");
    match common::run_with_proof(ROW, &stem).unwrap() {
        common::Proof::Verified(verdict) => println!("{verdict}"),
        common::Proof::NotChecked => println!("veripb not found: proof written but not checked"),
        common::Proof::NotWritten => panic!("regular should be proof-logged, through its tables"),
    }
}
