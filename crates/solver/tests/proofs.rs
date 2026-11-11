//! Proofs written by the solver, checked by VeriPB.
//!
//! Needs `veripb` on the PATH (or its path in `$VERIPB`); without it these
//! tests only check that the files are written. VeriPB 3.0.2 from crates.io
//! checks every step but doesn't know the `ENUMERATION_COMPLETE`
//! conclusion, which is newer; with that version, enumeration proofs are
//! checked with the conclusion swapped for `NONE`, and the solution count
//! is checked here instead.

use std::ops::ControlFlow;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use proptest::prelude::*;
use solver::{enumerate, solve, AllDifferent, Config, Model, NotEqual, Outcome, VarId, VarOrder};

/// The VeriPB command, if there is one.
fn veripb() -> Option<&'static str> {
    static FOUND: OnceLock<Option<String>> = OnceLock::new();
    FOUND
        .get_or_init(|| {
            let cmd = std::env::var("VERIPB").unwrap_or_else(|_| "veripb".into());
            let works = Command::new(&cmd).arg("--version").output().is_ok_and(|o| o.status.success());
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
fn check(stem: &Path) -> Option<String> {
    let cmd = veripb()?;
    let (opb, pbp) = (stem.with_extension("opb"), stem.with_extension("pbp"));
    let run = |pbp: &PathBuf| {
        let out = Command::new(cmd).arg(&opb).arg(pbp).output().unwrap();
        String::from_utf8_lossy(&out.stdout).to_string() + &String::from_utf8_lossy(&out.stderr)
    };
    let mut output = run(&pbp);
    if output.contains("found `ENUMERATION_COMPLETE`") {
        // An older VeriPB: check every step, without the conclusion.
        let text = std::fs::read_to_string(&pbp).unwrap();
        let swapped: String = text
            .lines()
            .map(|l| if l.starts_with("conclusion ENUMERATION_COMPLETE") { "conclusion NONE ;" } else { l })
            .collect::<Vec<_>>()
            .join("\n");
        let older = stem.with_extension("none.pbp");
        std::fs::write(&older, swapped).unwrap();
        output = run(&older);
    }
    let verdict = output.lines().find(|l| l.starts_with("s VERIFIED"));
    match verdict {
        Some(v) => Some(v.to_string()),
        None => panic!("VeriPB rejected {}:\n{output}", pbp.display()),
    }
}

fn config(name: &str) -> Config {
    Config { proof: Some(stem(name)), ..Config::default() }
}

fn solx_lines(name: &str) -> usize {
    let text = std::fs::read_to_string(stem(name).with_extension("pbp")).unwrap();
    text.lines().filter(|l| l.starts_with("solx")).count()
}

/// Enumerate with a proof, check it, and return the number of solutions.
fn enumerate_checked(name: &str, model: &Model, var_order: VarOrder) -> u64 {
    let config = Config { var_order, ..config(name) };
    let count = enumerate(model, &config, |_| ControlFlow::Continue(())).unwrap();
    assert_eq!(solx_lines(name) as u64, count, "one solx per solution");
    if let Some(verdict) = check(&stem(name)) {
        let ok = if count == 0 { "s VERIFIED UNSATISFIABLE" } else { "s VERIFIED" };
        assert!(verdict.starts_with(ok), "{name}: {verdict}");
    }
    count
}

#[test]
fn two_equal_constants_are_unsatisfiable() {
    // GCS's not_equals_unsat.scp: X = Y = 1, X != Y.
    let mut m = Model::new();
    let (x, y) = (m.int_var_named("X", 1, 1), m.int_var_named("Y", 1, 1));
    m.post(NotEqual::new(x, y));
    assert!(matches!(solve(&m, &config("ne_unsat")).unwrap(), Outcome::Unsatisfiable));
    if let Some(verdict) = check(&stem("ne_unsat")) {
        assert_eq!(verdict, "s VERIFIED UNSATISFIABLE");
    }
}

fn pigeonhole(pigeons: usize, holes: i64) -> Model {
    let mut m = Model::new();
    let p: Vec<VarId> = (0..pigeons).map(|i| m.int_var_named(&format!("p{i}"), 1, holes)).collect();
    for i in 0..pigeons {
        for j in i + 1..pigeons {
            m.post_named(&format!("p{i}p{j}"), NotEqual::new(p[i], p[j])).unwrap();
        }
    }
    m
}

#[test]
fn pigeonhole_needs_search_and_backtracking() {
    for (pigeons, holes) in [(3, 2), (4, 3), (5, 4)] {
        for order in [VarOrder::InputOrder, VarOrder::SmallestDomain] {
            let name = format!("php_{pigeons}_{holes}_{order:?}");
            assert_eq!(enumerate_checked(&name, &pigeonhole(pigeons, holes), order), 0);
        }
    }
}

#[test]
fn enumerating_permutations() {
    // n pigeons, n holes: n! solutions.
    assert_eq!(enumerate_checked("perm_3", &pigeonhole(3, 3), VarOrder::InputOrder), 6);
    assert_eq!(enumerate_checked("perm_4", &pigeonhole(4, 4), VarOrder::SmallestDomain), 24);
}

#[test]
fn stopping_at_the_first_solution_proves_satisfiable() {
    let m = pigeonhole(3, 3);
    assert!(matches!(solve(&m, &config("perm_decide")).unwrap(), Outcome::Satisfiable(_)));
    if let Some(verdict) = check(&stem("perm_decide")) {
        assert_eq!(verdict, "s VERIFIED SATISFIABLE");
    }
}

#[test]
fn negative_values_and_offsets() {
    // x + 2 != y, y - 1 != z, x != z over domains with negative values:
    // exercises the sign bit and the offsets in the encoding.
    let mut m = Model::new();
    let (x, y, z) = (m.int_var_named("x", -3, 0), m.int_var_named("y", -2, 1), m.int_var_named("z", -1, -1));
    m.post(NotEqual::with_offsets(x, 2, y, 0));
    m.post(NotEqual::with_offsets(y, -1, z, 0));
    m.post(NotEqual::new(x, z));
    let expected = brute_force(&[(-3, 0), (-2, 1), (-1, -1)], &[(0, 2, 1, 0), (1, -1, 2, 0), (0, 0, 2, 0)]);
    assert_eq!(enumerate_checked("negative", &m, VarOrder::InputOrder), expected);
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

#[test]
fn constraints_without_an_encoding_are_refused() {
    let mut m = Model::new();
    let v: Vec<VarId> = (0..3).map(|_| m.int_var(0, 2)).collect();
    m.post_named("alldiff", AllDifferent::new(&v)).unwrap();
    let err = solve(&m, &config("refused")).unwrap_err();
    assert_eq!(err.kind(), std::io::ErrorKind::Unsupported);
    assert!(err.to_string().contains("alldiff"), "{err}");
}

// ---- random models, against brute force ----

/// Count the assignments satisfying every constraint.
fn brute_force(domains: &[(i64, i64)], constraints: &[Diff]) -> u64 {
    fn go(i: usize, vals: &mut Vec<i64>, d: &[(i64, i64)], c: &[Diff]) -> u64 {
        if i == d.len() {
            return c.iter().all(|&(x, a, y, b)| vals[x] + a != vals[y] + b) as u64;
        }
        (d[i].0..=d[i].1)
            .map(|v| {
                vals.push(v);
                let n = go(i + 1, vals, d, c);
                vals.pop();
                n
            })
            .sum()
    }
    go(0, &mut Vec::new(), domains, constraints)
}

/// `x + a != y + b` as `(x, a, y, b)`, with variable indices.
type Diff = (usize, i64, usize, i64);

fn random_model() -> impl Strategy<Value = (Vec<(i64, i64)>, Vec<Diff>)> {
    (2usize..=5)
        .prop_flat_map(|n| {
            let domains = prop::collection::vec((-4i64..=3, 0i64..=3).prop_map(|(lo, w)| (lo, lo + w)), n);
            let constraint = (0..n, -2i64..=2, 0..n, -2i64..=2);
            (domains, prop::collection::vec(constraint, 1..=8))
        })
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 40, ..ProptestConfig::default() })]

    #[test]
    fn random_not_equal_models((domains, constraints) in random_model(), input_order: bool) {
        let mut m = Model::new();
        let vars: Vec<VarId> = domains.iter().enumerate()
            .map(|(i, &(lo, hi))| m.int_var_named(&format!("v{i}"), lo, hi))
            .collect();
        for &(x, a, y, b) in &constraints {
            m.post(NotEqual::with_offsets(vars[x], a, vars[y], b));
        }
        let order = if input_order { VarOrder::InputOrder } else { VarOrder::SmallestDomain };
        let count = enumerate_checked("random", &m, order);
        prop_assert_eq!(count, brute_force(&domains, &constraints));
    }
}
