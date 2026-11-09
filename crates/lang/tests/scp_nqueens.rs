//! N-Queens written as `.scp`, solved through the reader.
//!
//! SCP has no views, so `q[i] + i` can't appear inside a constraint. Instead
//! each diagonal gets an auxiliary variable, defined with `plus` / `minus`
//! and a constant: `u_i = q_i + i` and `d_i = q_i - i`. Then three
//! all-differents: columns, `/` diagonals and `\` diagonals.
//!
//! Solutions are checked by an independent checker that only looks at the
//! `q` values, and counted against the known totals.

use std::collections::HashSet;
use std::ops::ControlFlow;

use lang::{ProbType, read_scp};
use solver::Config;

/// The `.scp` text for `n` queens. `q_i` is the column of the queen in row `i`.
fn nqueens_scp(n: usize) -> String {
    let top = n as i64 - 1;
    let mut vars = Vec::new();
    let mut cons = Vec::new();
    for i in 0..n {
        let k = i as i64;
        vars.push(format!("(q{i} 0 {top})"));
        vars.push(format!("(u{i} {k} {})", top + k)); //   q_i + i
        vars.push(format!("(d{i} {} {})", -k, top - k)); // q_i - i
        cons.push(format!("(up{i} plus q{i} {i} u{i})"));
        cons.push(format!("(down{i} minus q{i} {i} d{i})"));
    }
    let names = |p: &str| {
        (0..n)
            .map(|i| format!("{p}{i}"))
            .collect::<Vec<_>>()
            .join(" ")
    };
    cons.push(format!("(columns all_different ({}))", names("q")));
    cons.push(format!("(up_diagonals all_different ({}))", names("u")));
    cons.push(format!("(down_diagonals all_different ({}))", names("d")));

    format!(
        "( (version 1)\n  (variables\n    {})\n  (constraints\n    {})\n  (prob_type enumerate) )\n",
        vars.join("\n    "),
        cons.join("\n    ")
    )
}

/// Is `cols` (the column of the queen in each row) a valid placement?
fn is_valid_placement(cols: &[i64]) -> bool {
    let n = cols.len() as i64;
    cols.iter().all(|&c| (0..n).contains(&c))
        && (0..cols.len()).all(|i| {
            (i + 1..cols.len()).all(|j| {
                let apart = (cols[i] - cols[j]).abs();
                apart != 0 && apart != (j - i) as i64
            })
        })
}

/// Known numbers of solutions for n = 1..=8 (OEIS A000170).
const COUNTS: [u64; 8] = [1, 0, 0, 2, 10, 4, 40, 92];

#[test]
fn counts_match_the_known_totals() {
    for (n, &expected) in (1..=8).zip(&COUNTS) {
        let (model, scp) = read_scp(&nqueens_scp(n)).unwrap();
        assert_eq!(scp.prob_type, ProbType::Enumerate);
        let q: Vec<_> = (0..n).map(|i| scp.var(&format!("q{i}")).unwrap()).collect();

        let mut seen = HashSet::new();
        let count = solver::enumerate(&model, &Config::default(), |sol| {
            let cols: Vec<i64> = q.iter().map(|&v| sol.value(v)).collect();
            assert!(is_valid_placement(&cols), "n={n}: invalid {cols:?}");
            assert!(seen.insert(cols), "n={n}: solution reported twice");
            ControlFlow::Continue(())
        })
        .unwrap();
        assert_eq!(count, expected, "n={n}");
    }
}

#[test]
fn the_example_file_is_what_the_generator_writes() {
    // examples/nqueens_8.scp is kept in step with the generator, so the file
    // in the repository is known to give 92 solutions.
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../examples/nqueens_8.scp");
    let file = std::fs::read_to_string(path).expect("examples/nqueens_8.scp");
    assert_eq!(file, nqueens_scp(8));
}

#[test]
fn checker_rejects_bad_placements() {
    assert!(is_valid_placement(&[1, 3, 0, 2]));
    assert!(!is_valid_placement(&[0, 1, 2, 3])); // diagonal
    assert!(!is_valid_placement(&[1, 1, 3, 0])); // column
}
