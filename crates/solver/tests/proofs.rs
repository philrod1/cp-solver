//! Proofs written by the solver, checked by VeriPB.
//!
//! Needs `veripb` on the PATH (or its path in `$VERIPB`); without it these
//! tests only check that the files are written. The proofs are written for
//! the VeriPB GCS uses, built from its git repository: VeriPB 3.0.2 from
//! crates.io is too old for them.

use std::ops::ControlFlow;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use proptest::prelude::*;
use solver::{
    AllDifferent, Automaton, Cell, Config, Cumulative, Linear, MinMax, Model, NotEqual, Objective,
    Outcome, Regular, Table, VarId, VarOrder, enumerate, optimise, solve,
};

/// The VeriPB command, if there is one.
fn veripb() -> Option<&'static str> {
    static FOUND: OnceLock<Option<String>> = OnceLock::new();
    FOUND
        .get_or_init(|| {
            let cmd = std::env::var("VERIPB").unwrap_or_else(|_| "veripb".into());
            let works = Command::new(&cmd)
                .arg("--version")
                .output()
                .is_ok_and(|o| o.status.success());
            if !works {
                eprintln!("veripb not found: proofs are written but not checked");
            }
            works.then_some(cmd)
        })
        .as_deref()
}

fn stem(name: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("proofs");
    std::fs::create_dir_all(&dir).unwrap();
    dir.join(name)
}

/// Run VeriPB on `stem.opb` and `stem.pbp`, and return its verdict line,
/// e.g. `s VERIFIED UNSATISFIABLE`. Panics if the proof doesn't check.
///
/// A proof with unchecked assertions (`a` steps) is accepted as
/// `s UNDER ASSERTIONS ...`, which is what newer VeriPB says for one;
/// VeriPB 3.0.2 says `s VERIFIED` with a warning instead. Any other proof
/// must be `s VERIFIED`. Deletions are checked strictly
/// (`--force-checked-deletion`), as GCS's chain checks them.
fn check(stem: &Path) -> Option<String> {
    let cmd = veripb()?;
    let (opb, pbp) = (stem.with_extension("opb"), stem.with_extension("pbp"));
    let out = Command::new(cmd)
        .arg("--force-checked-deletion")
        .arg(&opb)
        .arg(&pbp)
        .output()
        .unwrap();
    let output =
        String::from_utf8_lossy(&out.stdout).to_string() + &String::from_utf8_lossy(&out.stderr);
    let asserted = std::fs::read_to_string(&pbp)
        .unwrap()
        .lines()
        .any(|l| l.starts_with("a "));
    let accepted =
        |l: &&str| l.starts_with("s VERIFIED") || (asserted && l.starts_with("s UNDER ASSERTIONS"));
    match output.lines().find(accepted) {
        Some(verdict) => Some(verdict.to_string()),
        None => panic!("VeriPB rejected {}:\n{output}", pbp.display()),
    }
}

fn config(name: &str) -> Config {
    Config {
        proof: Some(stem(name)),
        ..Config::default()
    }
}

fn solx_lines(name: &str) -> usize {
    let text = std::fs::read_to_string(stem(name).with_extension("pbp")).unwrap();
    text.lines().filter(|l| l.starts_with("solx")).count()
}

/// Enumerate with a proof, check it, and return the number of solutions.
fn enumerate_checked(name: &str, model: &Model, var_order: VarOrder) -> u64 {
    let config = Config {
        var_order,
        ..config(name)
    };
    let count = enumerate(model, &config, |_| ControlFlow::Continue(())).unwrap();
    assert_eq!(solx_lines(name) as u64, count, "one solx per solution");
    if let Some(verdict) = check(&stem(name)) {
        if count == 0 {
            assert!(verdict.ends_with("UNSATISFIABLE"), "{name}: {verdict}");
        }
        // Newer VeriPB checks the count, and says it: "... ENUMERATION OF 24 SOLUTIONS".
        if verdict.contains("ENUMERATION OF") {
            assert!(
                verdict.ends_with(&format!("ENUMERATION OF {count} SOLUTIONS")),
                "{name}: {verdict}"
            );
        }
    }
    count
}

#[test]
fn two_equal_constants_are_unsatisfiable() {
    // GCS's not_equals_unsat.scp: X = Y = 1, X != Y.
    let mut m = Model::new();
    let (x, y) = (m.int_var_named("X", 1, 1), m.int_var_named("Y", 1, 1));
    m.post(NotEqual::new(x, y));
    assert!(matches!(
        solve(&m, &config("ne_unsat")).unwrap(),
        Outcome::Unsatisfiable
    ));
    if let Some(verdict) = check(&stem("ne_unsat")) {
        assert_eq!(verdict, "s VERIFIED UNSATISFIABLE");
    }
}

fn pigeonhole(pigeons: usize, holes: i64) -> Model {
    let mut m = Model::new();
    let p: Vec<VarId> = (0..pigeons)
        .map(|i| m.int_var_named(&format!("p{i}"), 1, holes))
        .collect();
    for i in 0..pigeons {
        for j in i + 1..pigeons {
            m.post_named(&format!("p{i}p{j}"), NotEqual::new(p[i], p[j]))
                .unwrap();
        }
    }
    m
}

#[test]
fn pigeonhole_needs_search_and_backtracking() {
    for (pigeons, holes) in [(3, 2), (4, 3), (5, 4)] {
        for order in [VarOrder::InputOrder, VarOrder::SmallestDomain] {
            let name = format!("php_{pigeons}_{holes}_{order:?}");
            assert_eq!(
                enumerate_checked(&name, &pigeonhole(pigeons, holes), order),
                0
            );
        }
    }
}

#[test]
fn enumerating_permutations() {
    // n pigeons, n holes: n! solutions.
    assert_eq!(
        enumerate_checked("perm_3", &pigeonhole(3, 3), VarOrder::InputOrder),
        6
    );
    assert_eq!(
        enumerate_checked("perm_4", &pigeonhole(4, 4), VarOrder::SmallestDomain),
        24
    );
}

#[test]
fn stopping_at_the_first_solution_proves_satisfiable() {
    let m = pigeonhole(3, 3);
    assert!(matches!(
        solve(&m, &config("perm_decide")).unwrap(),
        Outcome::Satisfiable(_)
    ));
    if let Some(verdict) = check(&stem("perm_decide")) {
        assert_eq!(verdict, "s VERIFIED SATISFIABLE");
    }
}

#[test]
fn negative_values_and_offsets() {
    // x + 2 != y, y - 1 != z, x != z over domains with negative values:
    // exercises the sign bit and the offsets in the encoding.
    let mut m = Model::new();
    let (x, y, z) = (
        m.int_var_named("x", -3, 0),
        m.int_var_named("y", -2, 1),
        m.int_var_named("z", -1, -1),
    );
    m.post(NotEqual::with_offsets(x, 2, y, 0));
    m.post(NotEqual::with_offsets(y, -1, z, 0));
    m.post(NotEqual::new(x, z));
    let expected = count(&[(-3, 0), (-2, 1), (-1, -1)], &|v| {
        v[0] + 2 != v[1] && v[1] - 1 != v[2] && v[0] != v[2]
    });
    assert_eq!(
        enumerate_checked("negative", &m, VarOrder::InputOrder),
        expected
    );
}

#[test]
fn a_variable_different_from_itself() {
    let mut m = Model::new();
    let x = m.int_var_named("x", 0, 3);
    m.post(NotEqual::new(x, x));
    assert_eq!(enumerate_checked("self", &m, VarOrder::InputOrder), 0);
}

#[test]
fn an_empty_domain() {
    let mut m = Model::new();
    let (x, y) = (m.int_var_named("x", 0, 3), m.int_var_named("y", 5, 2));
    m.post(NotEqual::new(x, y));
    assert_eq!(enumerate_checked("empty", &m, VarOrder::InputOrder), 0);
}

// ---- all-different ----

#[test]
fn all_different_pigeonhole() {
    for n in 3..=5 {
        for order in [VarOrder::InputOrder, VarOrder::SmallestDomain] {
            let mut m = Model::new();
            let v: Vec<VarId> = (0..n)
                .map(|i| m.int_var_named(&format!("p{i}"), 1, n as i64 - 1))
                .collect();
            m.post_named("holes", AllDifferent::new(&v)).unwrap();
            assert_eq!(
                enumerate_checked(&format!("ad_php_{n}_{order:?}"), &m, order),
                0
            );
        }
    }
}

/// The labelled helper lines `name`'s proof never deletes.
fn kept_helpers(name: &str) -> Vec<String> {
    let pbp = std::fs::read_to_string(stem(name).with_extension("pbp")).unwrap();
    let deleted = deleted_labels(&pbp);
    pbp.lines()
        .filter(|l| l.starts_with("@pl"))
        .filter(|l| !deleted.contains(&l.split_whitespace().next().unwrap()))
        .map(str::to_string)
        .collect()
}

#[test]
fn all_different_pigeonhole_fails_at_the_root() {
    // Six pigeons, five holes: one Hall argument, no search.
    let mut m = Model::new();
    let v: Vec<VarId> = (0..6)
        .map(|i| m.int_var_named(&format!("p{i}"), 1, 5))
        .collect();
    m.post_named("holes", AllDifferent::new(&v)).unwrap();
    assert_eq!(enumerate_checked("ad_php_6", &m, VarOrder::InputOrder), 0);
    let pbp = std::fs::read_to_string(stem("ad_php_6").with_extension("pbp")).unwrap();
    assert!(!pbp.lines().any(|l| l.starts_with("a ")));
    // The failure and the final empty clause; nothing from search.
    assert_eq!(pbp.lines().filter(|l| l.starts_with("rup ")).count(), 2);
    // What stays is one "at most one pigeon" line per hole.
    let kept = kept_helpers("ad_php_6");
    assert_eq!(kept.len(), 5, "{kept:#?}");
    assert!(kept.iter().all(|l| l.contains(" pol ")), "{kept:#?}");
}

#[test]
fn all_different_violators_during_search() {
    // z comes first and takes 0, 1 or 2, leaving the three other terms two
    // values between them: z = 1 leaves {0, 2}, with a hole. Only z = 3
    // works. The offsets put every term in 0..=2.
    let mut m = Model::new();
    let z = m.int_var_named("z", 0, 3);
    let d = [(0, 2), (-1, 1), (-2, 0)];
    let y: Vec<(VarId, i64)> = d
        .iter()
        .enumerate()
        .map(|(i, &(lo, hi))| (m.int_var_named(&format!("y{i}"), lo, hi), i as i64))
        .collect();
    let terms = [vec![(z, 0)], y].concat();
    m.post_named("ad", AllDifferent::with_offsets(&terms))
        .unwrap();
    for order in [VarOrder::InputOrder, VarOrder::SmallestDomain] {
        let name = format!("ad_search_{order:?}");
        assert_eq!(enumerate_checked(&name, &m, order), 6);
    }
    // Three Hall arguments, one per value, each kept for the next.
    let kept = kept_helpers("ad_search_InputOrder");
    assert_eq!(kept.len(), 3, "{kept:#?}");
    assert!(kept.iter().all(|l| l.contains(" pol ")), "{kept:#?}");
}

#[test]
fn all_different_permutations() {
    let mut m = Model::new();
    let v: Vec<VarId> = (0..4)
        .map(|i| m.int_var_named(&format!("v{i}"), 1, 4))
        .collect();
    m.post(AllDifferent::new(&v));
    assert_eq!(
        enumerate_checked("ad_perm_4", &m, VarOrder::SmallestDomain),
        24
    );
}

// ---- table ----

#[test]
fn table_with_wildcards_and_a_repeated_variable() {
    // (x, y, x) with rows that only match when both x cells agree.
    let mut m = Model::new();
    let (x, y) = (m.int_var_named("x", 0, 2), m.int_var_named("y", -1, 1));
    let rows = vec![
        vec![Cell::Val(0), Cell::Any, Cell::Val(0)],
        vec![Cell::Val(1), Cell::Val(-1), Cell::Val(2)], // x can't be 1 and 2
        vec![Cell::Any, Cell::Val(1), Cell::Val(2)],
        vec![Cell::Val(7), Cell::Val(0), Cell::Any], // 7 is outside x's domain
    ];
    m.post_named("t", Table::new(&[x, y, x], &rows)).unwrap();
    m.post(NotEqual::new(x, y));
    // x = 0 with y ∈ {-1, 1}, or x = 2 with y = 1.
    assert_eq!(
        enumerate_checked("table_fixed", &m, VarOrder::InputOrder),
        3
    );
}

#[test]
fn a_table_with_no_rows() {
    let mut m = Model::new();
    let x = m.int_var_named("x", 0, 2);
    m.post(Table::new(&[x], &[]));
    assert_eq!(
        enumerate_checked("table_empty", &m, VarOrder::InputOrder),
        0
    );
}

// ---- linear ----

/// The proof for `name` has no unchecked assertions, and some `pol` steps,
/// each deleted once it has been used.
fn fully_checked(name: &str) {
    let pbp = std::fs::read_to_string(stem(name).with_extension("pbp")).unwrap();
    assert!(
        !pbp.lines().any(|l| l.starts_with("a ")),
        "{name}: unchecked steps"
    );
    // The helpers' labels; an atom's pin is a `pol` too, and stays.
    let pols: Vec<&str> = pbp
        .lines()
        .filter(|l| l.starts_with("@pl") && l.contains(" pol "))
        .filter_map(|l| l.split_whitespace().next())
        .collect();
    assert!(!pols.is_empty(), "{name}: no pol steps");
    assert_eq!(
        pols,
        deleted_labels(&pbp),
        "{name}: each pol line deleted after use"
    );
}

#[test]
fn linear_inferences_are_checked() {
    // x + 2y = 7, x - y <= 1 over 0..=5: (1, 3) and (3, 2).
    let mut m = Model::new();
    let (x, y) = (m.int_var_named("x", 0, 5), m.int_var_named("y", 0, 5));
    m.post(Linear::eq(&[(x, 1), (y, 2)], 7));
    m.post(Linear::le(&[(x, 1), (y, -1)], 1));
    assert_eq!(
        enumerate_checked("linear_small", &m, VarOrder::InputOrder),
        2
    );
    fully_checked("linear_small");
}

#[test]
fn linear_bounds_that_jump_several_values() {
    // 3x + 5y ≤ 17 and x - 2y = 1, with negative values and wide steps:
    // the cases RUP alone can't justify. Count against brute force.
    let mut m = Model::new();
    let (x, y) = (m.int_var_named("x", -6, 9), m.int_var_named("y", -4, 7));
    m.post(Linear::le(&[(x, 3), (y, 5)], 17));
    m.post(Linear::eq(&[(x, 1), (y, -2)], 1));
    let expected = count(&[(-6, 9), (-4, 7)], &|v| {
        3 * v[0] + 5 * v[1] <= 17 && v[0] - 2 * v[1] == 1
    });
    for order in [VarOrder::InputOrder, VarOrder::SmallestDomain] {
        let name = format!("linear_wide_{order:?}");
        assert_eq!(enumerate_checked(&name, &m, order), expected);
        fully_checked(&name);
    }
}

// ---- regular ----

/// Every label a `del id` line in `pbp` names, in order.
fn deleted_labels(pbp: &str) -> Vec<&str> {
    pbp.lines()
        .filter_map(|l| l.strip_prefix("del id "))
        .flat_map(|l| l.split_whitespace().filter(|w| w.starts_with('@')))
        .collect()
}

/// The proof for `name` deletes every labelled line it writes: for a
/// constraint whose labelled lines are all helpers for one propagation.
fn every_helper_deleted(name: &str) {
    let pbp = std::fs::read_to_string(stem(name).with_extension("pbp")).unwrap();
    let mut written: Vec<&str> = pbp
        .lines()
        .filter(|l| l.starts_with("@pl"))
        .filter_map(|l| l.split_whitespace().next())
        .collect();
    let mut deleted = deleted_labels(&pbp);
    assert!(!written.is_empty(), "{name}: no helpers");
    written.sort_unstable();
    deleted.sort_unstable();
    assert_eq!(written, deleted, "{name}: helpers not deleted");
}

/// `0* 111 0+ 11 0*`: a nonogram row with the clue "3 2".
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

#[test]
fn regular_nonogram_row() {
    let mut m = Model::new();
    let cells: Vec<VarId> = (0..10)
        .map(|i| m.int_var_named(&format!("c{i}"), 0, 1))
        .collect();
    m.post_named("row", Regular::new(&cells, three_two()))
        .unwrap();
    assert_eq!(
        enumerate_checked("regular_row", &m, VarOrder::InputOrder),
        15
    );
}

#[test]
fn regular_with_several_states_in_a_layer() {
    // The hand-checked example: A goes to B or C on 0 or 1; B and C loop on
    // 0 and 1 and go to D on 2; D (accepting) loops on 0. Over {0, 1, 2},
    // reaching D at layer 2 needs X1 = 2, with two states behind it.
    let edges = [
        (0, 0, 1),
        (0, 1, 2),
        (1, 0, 1),
        (1, 1, 1),
        (1, 2, 3),
        (2, 0, 2),
        (2, 1, 2),
        (2, 2, 3),
        (3, 0, 3),
    ];
    let a = Automaton::new(4, &edges, &[3]).unwrap();
    for order in [VarOrder::InputOrder, VarOrder::SmallestDomain] {
        let mut m = Model::new();
        let x: Vec<VarId> = (0..4)
            .map(|i| m.int_var_named(&format!("x{i}"), 0, 2))
            .collect();
        m.post_named("r", Regular::new(&x, a.clone())).unwrap();
        let expected = count(&[(0, 2); 4], &|v| a.accepts(v));
        let name = format!("regular_helpers_{order:?}");
        assert_eq!(enumerate_checked(&name, &m, order), expected);
        every_helper_deleted(&name);
    }
}

#[test]
fn regular_nondeterministic() {
    // The third symbol from the end is 1: state 0 guesses which 1 it is.
    let edges = [
        (0, 0, 0),
        (0, 1, 0),
        (0, 1, 1),
        (1, 0, 2),
        (1, 1, 2),
        (2, 0, 3),
        (2, 1, 3),
    ];
    let a = Automaton::new(4, &edges, &[3]).unwrap();
    for order in [VarOrder::InputOrder, VarOrder::SmallestDomain] {
        let mut m = Model::new();
        let x: Vec<VarId> = (0..5)
            .map(|i| m.int_var_named(&format!("x{i}"), 0, 1))
            .collect();
        m.post_named("r", Regular::new(&x, a.clone())).unwrap();
        let name = format!("regular_nfa_{order:?}");
        assert_eq!(enumerate_checked(&name, &m, order), 16);
        every_helper_deleted(&name);
    }
}

#[test]
fn regular_with_a_repeated_variable() {
    // x y x y with "no two equal neighbours" over {0, 1, 2}.
    let edges: Vec<(usize, i64, usize)> = (0..4)
        .flat_map(|q| {
            (0..3)
                .filter(move |&v| q == 0 || v + 1 != q as i64)
                .map(move |v| (q, v, v as usize + 1))
        })
        .collect();
    let a = Automaton::new(4, &edges, &[1, 2, 3]).unwrap();
    let mut m = Model::new();
    let (x, y) = (m.int_var_named("x", 0, 2), m.int_var_named("y", 0, 2));
    m.post(Regular::new(&[x, y, x, y], a.clone()));
    let expected = count(&[(0, 2); 2], &|v| a.accepts(&[v[0], v[1], v[0], v[1]]));
    assert_eq!(
        enumerate_checked("regular_repeated", &m, VarOrder::InputOrder),
        expected
    );
}

// ---- cumulative ----

/// Whether tasks starting at `starts` stay within `capacity` at every time.
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
fn cumulative_disjunctive() {
    // Three tasks of length 2 on a machine that runs one at a time, all
    // starting in 0..=5: 3! orders, and 4 ways to place the one spare step
    // before, between or after them.
    let mut m = Model::new();
    let s: Vec<VarId> = (0..3)
        .map(|i| m.int_var_named(&format!("s{i}"), 0, 5))
        .collect();
    m.post_named("c", Cumulative::new(&s, &[2, 2, 2], &[1, 1, 1], 1))
        .unwrap();
    for order in [VarOrder::InputOrder, VarOrder::SmallestDomain] {
        let name = format!("cumulative_disjunctive_{order:?}");
        assert_eq!(enumerate_checked(&name, &m, order), 24);
    }
}

#[test]
fn cumulative_needs_several_steps() {
    // A long fixed task leaves a short one three steps of starts to rule
    // out, then a third task shares what is left.
    let mut m = Model::new();
    let domains = [(0, 0), (0, 9), (0, 9)];
    let s: Vec<VarId> = domains
        .iter()
        .enumerate()
        .map(|(i, &(lo, hi))| m.int_var_named(&format!("s{i}"), lo, hi))
        .collect();
    let (durations, heights) = ([6, 2, 3], [2, 1, 1]);
    m.post_named("c", Cumulative::new(&s, &durations, &heights, 2))
        .unwrap();
    let expected = count(&domains, &|v| fits(v, &durations, &heights, 2));
    for order in [VarOrder::InputOrder, VarOrder::SmallestDomain] {
        let name = format!("cumulative_steps_{order:?}");
        assert_eq!(enumerate_checked(&name, &m, order), expected);
        // The pins and steps are deleted once their push is logged; the
        // recovered capacity rows, which are cited again, are not.
        let pbp = std::fs::read_to_string(stem(&name).with_extension("pbp")).unwrap();
        let deleted = deleted_labels(&pbp);
        assert!(!deleted.is_empty(), "{name}: nothing deleted");
        for label in deleted {
            let written = pbp.lines().find(|l| l.starts_with(&format!("{label} ")));
            assert!(
                written.is_some_and(|l| l.contains(" rup ")),
                "{name}: {label} is not a helper"
            );
        }
    }
}

// ---- min and max ----

#[test]
fn array_min_and_max_like_gcs_cases() {
    // GCS's array_min_sat, array_max_sat (X, Y, Z, R in 0..=2) and
    // array_min_unsat (R in 3..=5, out of every variable's reach).
    let cases = [
        ("min_sat", true, (0, 2)),
        ("max_sat", false, (0, 2)),
        ("min_unsat", true, (3, 5)),
    ];
    for (name, min, (lo, hi)) in cases {
        let mut m = Model::new();
        let xs: Vec<VarId> = ["X", "Y", "Z"]
            .iter()
            .map(|n| m.int_var_named(n, 0, 2))
            .collect();
        let r = m.int_var_named("R", lo, hi);
        m.post_named(
            "_1",
            if min {
                MinMax::min(&xs, r)
            } else {
                MinMax::max(&xs, r)
            },
        )
        .unwrap();
        let expected = count(&[(0, 2), (0, 2), (0, 2), (lo, hi)], &|v| {
            let extreme = if min {
                v[..3].iter().min()
            } else {
                v[..3].iter().max()
            };
            extreme == Some(&v[3])
        });
        for order in [VarOrder::InputOrder, VarOrder::SmallestDomain] {
            let name = format!("array_{name}_{order:?}");
            assert_eq!(enumerate_checked(&name, &m, order), expected);
        }
    }
}

/// A min/max model: a name, the variables' domains, the result's domain,
/// and values knocked out as (variable index, value), the result last.
type MinMaxCase = (
    &'static str,
    &'static [(i64, i64)],
    (i64, i64),
    &'static [(usize, i64)],
);

#[test]
fn each_min_max_rule_is_justified() {
    // Models where each rule must remove something at the root, so its
    // helpers are in the proof.
    let cases: [MinMaxCase; 3] = [
        // A value of r no variable has: x, y in {1, 3}, r in 0..=4.
        (
            "result_support",
            &[(1, 3), (1, 3)],
            (0, 4),
            &[(0, 2), (1, 2)],
        ),
        // Only x can meet r in {1, 2}: x loses 0, 3 and 4.
        ("single_support", &[(0, 4), (5, 7)], (1, 2), &[]),
        // r in {0, 3}: x = 1 or 2 can't be the minimum, nor sit above
        // the 3 that y supplies.
        (
            "variable_support",
            &[(0, 3), (2, 3)],
            (0, 3),
            &[(2, 1), (2, 2)],
        ),
    ];
    for (name, domains, (lo, hi), holes) in cases {
        let mut m = Model::new();
        let xs: Vec<VarId> = domains
            .iter()
            .enumerate()
            .map(|(i, &(a, b))| m.int_var_named(&format!("x{i}"), a, b))
            .collect();
        let r = m.int_var_named("r", lo, hi);
        let all: Vec<VarId> = xs.iter().copied().chain([r]).collect();
        for &(i, v) in holes {
            let k = m.constant(v);
            m.post(NotEqual::new(all[i], k));
        }
        m.post_named("mm", MinMax::min(&xs, r)).unwrap();
        let mut ranges: Vec<(i64, i64)> = domains.to_vec();
        ranges.push((lo, hi));
        let expected = count(&ranges, &|v| {
            holes.iter().all(|&(i, h)| v[i] != h)
                && v[..v.len() - 1].iter().min() == Some(&v[v.len() - 1])
        });
        let name = format!("min_max_{name}");
        assert_eq!(enumerate_checked(&name, &m, VarOrder::InputOrder), expected);
        let pbp = std::fs::read_to_string(stem(&name).with_extension("pbp")).unwrap();
        assert!(!deleted_labels(&pbp).is_empty(), "{name}: no helpers");
    }
}

// ---- optimisation ----

/// Optimise with a proof, check it, and return the best objective value.
/// Each solution found must improve on the last, and VeriPB must agree on
/// the optimum: `BOUNDS v <= obj <= v`, with `v` negated for a maximisation,
/// which the proof minimises as its negation, and `INF` when there is no
/// solution.
fn optimise_checked(
    name: &str,
    model: &Model,
    objective: Objective,
    var_order: VarOrder,
) -> Option<i64> {
    let config = Config {
        var_order,
        ..config(name)
    };
    let (var, sign) = match objective {
        Objective::Minimize(x) => (x, 1),
        Objective::Maximize(x) => (x, -1),
    };
    let mut seen: Vec<i64> = Vec::new();
    let outcome = optimise(model, objective, &config, |s| seen.push(s.value(var))).unwrap();
    assert!(
        seen.windows(2).all(|w| sign * w[1] < sign * w[0]),
        "{name}: not improving: {seen:?}"
    );
    let best = match outcome {
        Outcome::Satisfiable(s) => Some(s.value(var)),
        _ => None,
    };
    assert_eq!(best, seen.last().copied(), "{name}");
    if let Some(verdict) = check(&stem(name)) {
        let expected = match best {
            Some(v) => format!("BOUNDS {0} <= obj <= {0}", sign * v),
            // No solutions: no finite bound on the objective.
            None => "BOUNDS INF <= obj <= INF".to_string(),
        };
        assert!(verdict.ends_with(&expected), "{name}: {verdict}");
    }
    best
}

#[test]
fn optimisation_like_gcs_cases() {
    // GCS's lin_equals_{minimize,maximize,maximize_neg}_opt: x + y = 3 over
    // 0..3, and x + y = 0 over -3..3, where x has a sign bit.
    for order in [VarOrder::InputOrder, VarOrder::SmallestDomain] {
        let mut m = Model::new();
        let (x, y) = (m.int_var_named("X", 0, 3), m.int_var_named("Y", 0, 3));
        m.post(Linear::eq(&[(x, 1), (y, 1)], 3));
        let min = optimise_checked(
            &format!("opt_min_{order:?}"),
            &m,
            Objective::Minimize(x),
            order,
        );
        assert_eq!(min, Some(0));
        let max = optimise_checked(
            &format!("opt_max_{order:?}"),
            &m,
            Objective::Maximize(x),
            order,
        );
        assert_eq!(max, Some(3));

        let mut m = Model::new();
        let (x, y) = (m.int_var_named("X", -3, 3), m.int_var_named("Y", -3, 3));
        m.post(Linear::eq(&[(x, 1), (y, 1)], 0));
        let neg = optimise_checked(
            &format!("opt_neg_{order:?}"),
            &m,
            Objective::Maximize(x),
            order,
        );
        assert_eq!(neg, Some(3));
    }
}

#[test]
fn optimisation_edge_cases() {
    // A constant objective: its one value is best.
    let mut m = Model::new();
    let x = m.int_var_named("x", 0, 2);
    let k = m.constant(5);
    m.post(NotEqual::new(x, k));
    let order = VarOrder::InputOrder;
    assert_eq!(
        optimise_checked("opt_constant", &m, Objective::Minimize(k), order),
        Some(5)
    );

    // No solutions at all.
    let mut m = Model::new();
    let (x, y) = (m.int_var_named("x", 0, 1), m.int_var_named("y", 0, 1));
    m.post(Linear::eq(&[(x, 1), (y, 1)], 5));
    assert_eq!(
        optimise_checked("opt_unsat", &m, Objective::Maximize(x), order),
        None
    );

    // The first solution is already at the objective's bound.
    let mut m = Model::new();
    let (x, y) = (m.int_var_named("x", -2, 4), m.int_var_named("y", 0, 4));
    m.post(Linear::le(&[(x, 1), (y, 1)], 4));
    assert_eq!(
        optimise_checked("opt_at_bound", &m, Objective::Minimize(x), order),
        Some(-2)
    );
}

#[test]
fn moving_furniture_as_quickly_as_possible() {
    // Four tasks on a resource of capacity 2, with the finish time `end`
    // minimised: each task ends by `end`.
    let (durations, heights) = ([3, 2, 2, 1], [2, 1, 1, 1]);
    let mut m = Model::new();
    let starts: Vec<VarId> = (0..4)
        .map(|i| m.int_var_named(&format!("s{i}"), 0, 8))
        .collect();
    let end = m.int_var_named("end", 0, 9);
    m.post(Cumulative::new(&starts, &durations, &heights, 2));
    for (&s, d) in starts.iter().zip(durations) {
        m.post(Linear::le(&[(s, 1), (end, -1)], -d));
    }
    // 3·2 + 2 + 2 + 1 = 11 resource-slots on capacity 2: at least 6, and
    // the big task can't share, so 3 slots for it and ⌈5/2⌉ = 3 for the rest.
    for order in [VarOrder::InputOrder, VarOrder::SmallestDomain] {
        let name = format!("opt_makespan_{order:?}");
        assert_eq!(
            optimise_checked(&name, &m, Objective::Minimize(end), order),
            Some(6)
        );
    }
}

// ---- random models, against brute force ----

/// The number of assignments over `domains` that `ok` accepts.
fn count(domains: &[(i64, i64)], ok: &dyn Fn(&[i64]) -> bool) -> u64 {
    fn go(vals: &mut Vec<i64>, d: &[(i64, i64)], ok: &dyn Fn(&[i64]) -> bool) -> u64 {
        let Some(&(lo, hi)) = d.get(vals.len()) else {
            return ok(vals) as u64;
        };
        (lo..=hi)
            .map(|v| {
                vals.push(v);
                let n = go(vals, d, ok);
                vals.pop();
                n
            })
            .sum()
    }
    go(&mut Vec::new(), domains, ok)
}

fn domains(n: std::ops::RangeInclusive<usize>) -> impl Strategy<Value = Vec<(i64, i64)>> {
    prop::collection::vec((-4i64..=3, 0i64..=3).prop_map(|(lo, w)| (lo, lo + w)), n)
}

fn model_vars(m: &mut Model, domains: &[(i64, i64)]) -> Vec<VarId> {
    domains
        .iter()
        .enumerate()
        .map(|(i, &(lo, hi))| m.int_var_named(&format!("v{i}"), lo, hi))
        .collect()
}

fn order(input_order: bool) -> VarOrder {
    if input_order {
        VarOrder::InputOrder
    } else {
        VarOrder::SmallestDomain
    }
}

/// `x + a != y + b` as `(x, a, y, b)`, with variable indices.
type Diff = (usize, i64, usize, i64);

/// Terms `(variable index, offset)`.
type Terms = Vec<(usize, i64)>;

/// A table over variable indices (which may repeat), with `None` for `*`.
type RandomTable = (Vec<usize>, Vec<Vec<Option<i64>>>);

/// `Σ aᵢxᵢ ≤ c` (or `= c` when the flag is set), as `((index, aᵢ)s, c, eq)`.
type RandomLinear = (Vec<(usize, i64)>, i64, bool);

fn random_tables(n: usize) -> impl Strategy<Value = Vec<RandomTable>> {
    let table = (1usize..=3).prop_flat_map(move |arity| {
        let vars = prop::collection::vec(0..n, arity);
        let cell = prop::option::weighted(0.75, -5i64..=4); // sometimes outside the domain
        let rows = prop::collection::vec(prop::collection::vec(cell, arity), 0..=6);
        (vars, rows)
    });
    prop::collection::vec(table, 1..=2)
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 40, ..ProptestConfig::default() })]

    #[test]
    fn random_not_equal_models(
        (domains, constraints) in domains(2..=5).prop_flat_map(|d| {
            let n = d.len();
            (Just(d), prop::collection::vec((0..n, -2i64..=2, 0..n, -2i64..=2), 1..=8))
        }),
        input_order: bool,
    ) {
        let mut m = Model::new();
        let vars = model_vars(&mut m, &domains);
        for &(x, a, y, b) in &constraints {
            m.post(NotEqual::with_offsets(vars[x], a, vars[y], b));
        }
        let expected = count(&domains, &|v| constraints.iter().all(|&(x, a, y, b): &Diff| v[x] + a != v[y] + b));
        prop_assert_eq!(enumerate_checked("random_ne", &m, order(input_order)), expected);
    }

    #[test]
    fn random_all_different_models(
        (domains, cliques) in domains(2..=5).prop_flat_map(|d| {
            let n = d.len();
            let clique = prop::collection::vec((0..n, -2i64..=2), 2..=4);
            (Just(d), prop::collection::vec(clique, 1..=2))
        }),
        input_order: bool,
    ) {
        let mut m = Model::new();
        let vars = model_vars(&mut m, &domains);
        for clique in &cliques {
            let terms: Vec<(VarId, i64)> = clique.iter().map(|&(i, a)| (vars[i], a)).collect();
            m.post(AllDifferent::with_offsets(&terms));
        }
        let distinct = |v: &[i64], clique: &Terms| {
            let values: Vec<i64> = clique.iter().map(|&(i, a)| v[i] + a).collect();
            values.iter().enumerate().all(|(k, x)| !values[..k].contains(x))
        };
        let expected = count(&domains, &|v| cliques.iter().all(|c| distinct(v, c)));
        prop_assert_eq!(enumerate_checked("random_ad", &m, order(input_order)), expected);
    }

    #[test]
    fn random_table_models(
        (domains, tables) in domains(1..=4).prop_flat_map(|d| { let n = d.len(); (Just(d), random_tables(n)) }),
        input_order: bool,
    ) {
        let mut m = Model::new();
        let vars = model_vars(&mut m, &domains);
        for (scope, rows) in &tables {
            let scope_vars: Vec<VarId> = scope.iter().map(|&i| vars[i]).collect();
            let rows: Vec<Vec<Cell>> = rows
                .iter()
                .map(|r| r.iter().map(|c| c.map_or(Cell::Any, Cell::Val)).collect())
                .collect();
            m.post(Table::new(&scope_vars, &rows));
        }
        let matches = |v: &[i64], (scope, rows): &RandomTable| {
            rows.iter().any(|row| scope.iter().zip(row).all(|(&i, c)| c.is_none_or(|w| w == v[i])))
        };
        let expected = count(&domains, &|v| tables.iter().all(|t| matches(v, t)));
        prop_assert_eq!(enumerate_checked("random_table", &m, order(input_order)), expected);
    }

    #[test]
    fn random_regular_models(
        (domains, k, table, accepting) in domains(0..=4).prop_flat_map(|d| {
            (1usize..=4).prop_flat_map(move |k| {
                let targets = prop::collection::vec(0..k, 0..=2);
                (Just(d.clone()), Just(k), prop::collection::vec(prop::collection::vec(targets, 8), k), prop::collection::vec(any::<bool>(), k))
            })
        }),
        input_order: bool,
    ) {
        // Symbols -4..=3, the same range the domains come from, each with
        // up to two targets.
        let edges: Vec<(usize, i64, usize)> = table
            .iter()
            .enumerate()
            .flat_map(|(q, row)| row.iter().enumerate().flat_map(move |(s, ts)| ts.iter().map(move |&t| (q, s as i64 - 4, t))))
            .collect();
        let finals: Vec<usize> = (0..k).filter(|&q| accepting[q]).collect();
        let automaton = Automaton::new(k, &edges, &finals).unwrap();
        let mut m = Model::new();
        let vars = model_vars(&mut m, &domains);
        m.post(Regular::new(&vars, automaton.clone()));
        let expected = count(&domains, &|v| automaton.accepts(v));
        prop_assert_eq!(enumerate_checked("random_regular", &m, order(input_order)), expected);
    }

    #[test]
    fn random_cumulative_models(
        (domains, tasks) in domains(1..=4).prop_flat_map(|d| {
            let n = d.len();
            (Just(d), prop::collection::vec((0i64..=3, 0i64..=3), n))
        }),
        capacity in 0i64..=4,
        input_order: bool,
    ) {
        let durations: Vec<i64> = tasks.iter().map(|t| t.0).collect();
        let heights: Vec<i64> = tasks.iter().map(|t| t.1).collect();
        let mut m = Model::new();
        let vars = model_vars(&mut m, &domains);
        m.post(Cumulative::new(&vars, &durations, &heights, capacity));
        let expected = count(&domains, &|v| fits(v, &durations, &heights, capacity));
        prop_assert_eq!(enumerate_checked("random_cumulative", &m, order(input_order)), expected);
    }

    #[test]
    fn random_linear_models(
        (domains, constraints) in domains(1..=4).prop_flat_map(|d| {
            let n = d.len();
            let terms = prop::collection::vec((0..n, -3i64..=3), 1..=3);
            (Just(d), prop::collection::vec((terms, -6i64..=6, any::<bool>()), 1..=2))
        }),
        input_order: bool,
    ) {
        let mut m = Model::new();
        let vars = model_vars(&mut m, &domains);
        for (terms, c, eq) in &constraints {
            let terms: Vec<(VarId, i64)> = terms.iter().map(|&(i, a)| (vars[i], a)).collect();
            m.post(if *eq { Linear::eq(&terms, *c) } else { Linear::le(&terms, *c) });
        }
        let holds = |v: &[i64], (terms, c, eq): &RandomLinear| {
            let sum: i64 = terms.iter().map(|&(i, a)| a * v[i]).sum();
            if *eq { sum == *c } else { sum <= *c }
        };
        let expected = count(&domains, &|v| constraints.iter().all(|k| holds(v, k)));
        prop_assert_eq!(enumerate_checked("random_lin", &m, order(input_order)), expected);
    }

    #[test]
    fn random_min_max_models(
        domains in domains(2..=4),
        min: bool,
        input_order: bool,
    ) {
        // The last variable is the result.
        let mut m = Model::new();
        let vars = model_vars(&mut m, &domains);
        let (xs, r) = vars.split_at(vars.len() - 1);
        m.post(if min { MinMax::min(xs, r[0]) } else { MinMax::max(xs, r[0]) });
        let expected = count(&domains, &|v| {
            let (xs, r) = v.split_at(v.len() - 1);
            let extreme = if min { xs.iter().min() } else { xs.iter().max() };
            extreme == Some(&r[0])
        });
        prop_assert_eq!(enumerate_checked("random_min_max", &m, order(input_order)), expected);
    }

    #[test]
    fn random_optimisation(
        (domains, constraints, target) in domains(1..=4).prop_flat_map(|d| {
            let n = d.len();
            let terms = prop::collection::vec((0..n, -3i64..=3), 1..=3);
            (Just(d), prop::collection::vec((terms, -6i64..=6, any::<bool>()), 1..=2), 0..n)
        }),
        maximise: bool,
        input_order: bool,
    ) {
        let mut m = Model::new();
        let vars = model_vars(&mut m, &domains);
        for (terms, c, eq) in &constraints {
            let terms: Vec<(VarId, i64)> = terms.iter().map(|&(i, a)| (vars[i], a)).collect();
            m.post(if *eq { Linear::eq(&terms, *c) } else { Linear::le(&terms, *c) });
        }
        let holds = |v: &[i64], (terms, c, eq): &RandomLinear| {
            let sum: i64 = terms.iter().map(|&(i, a)| a * v[i]).sum();
            if *eq { sum == *c } else { sum <= *c }
        };
        // The best value of the target over every solution, by brute force.
        let best_seen: std::cell::Cell<Option<i64>> = std::cell::Cell::new(None);
        count(&domains, &|v| {
            let ok = constraints.iter().all(|k| holds(v, k));
            if ok {
                let better = |a: i64, b: i64| if maximise { a.max(b) } else { a.min(b) };
                best_seen.set(Some(best_seen.get().map_or(v[target], |b| better(b, v[target]))));
            }
            ok
        });
        let expected = best_seen.get();
        let objective = if maximise {
            Objective::Maximize(vars[target])
        } else {
            Objective::Minimize(vars[target])
        };
        let best = optimise_checked("random_opt", &m, objective, order(input_order));
        prop_assert_eq!(best, expected);
    }
}
