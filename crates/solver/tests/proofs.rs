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
    enumerate, solve, AllDifferent, Automaton, Cell, Config, Linear, Model, NotEqual, Outcome, Regular, Table, VarId,
    VarOrder,
};

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
///
/// A proof with unchecked assertions (`a` steps, from linear for now) is
/// accepted as `s UNDER ASSERTIONS ...`, which is what newer VeriPB says
/// for one; VeriPB 3.0.2 says `s VERIFIED` with a warning instead. Any other
/// proof must be `s VERIFIED`.
fn check(stem: &Path) -> Option<String> {
    let cmd = veripb()?;
    let (opb, pbp) = (stem.with_extension("opb"), stem.with_extension("pbp"));
    let out = Command::new(cmd).arg(&opb).arg(&pbp).output().unwrap();
    let output = String::from_utf8_lossy(&out.stdout).to_string() + &String::from_utf8_lossy(&out.stderr);
    let asserted = std::fs::read_to_string(&pbp).unwrap().lines().any(|l| l.starts_with("a "));
    let accepted = |l: &&str| l.starts_with("s VERIFIED") || (asserted && l.starts_with("s UNDER ASSERTIONS"));
    match output.lines().find(accepted) {
        Some(verdict) => Some(verdict.to_string()),
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
        if count == 0 {
            assert!(verdict.ends_with("UNSATISFIABLE"), "{name}: {verdict}");
        }
        // Newer VeriPB checks the count, and says it: "... ENUMERATION OF 24 SOLUTIONS".
        if verdict.contains("ENUMERATION OF") {
            assert!(verdict.ends_with(&format!("ENUMERATION OF {count} SOLUTIONS")), "{name}: {verdict}");
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
    let expected = count(&[(-3, 0), (-2, 1), (-1, -1)], &|v| v[0] + 2 != v[1] && v[1] - 1 != v[2] && v[0] != v[2]);
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

// ---- all-different ----

#[test]
fn all_different_pigeonhole() {
    for n in 3..=5 {
        for order in [VarOrder::InputOrder, VarOrder::SmallestDomain] {
            let mut m = Model::new();
            let v: Vec<VarId> = (0..n).map(|i| m.int_var_named(&format!("p{i}"), 1, n as i64 - 1)).collect();
            m.post_named("holes", AllDifferent::new(&v)).unwrap();
            assert_eq!(enumerate_checked(&format!("ad_php_{n}_{order:?}"), &m, order), 0);
        }
    }
}

#[test]
fn all_different_permutations() {
    let mut m = Model::new();
    let v: Vec<VarId> = (0..4).map(|i| m.int_var_named(&format!("v{i}"), 1, 4)).collect();
    m.post(AllDifferent::new(&v));
    assert_eq!(enumerate_checked("ad_perm_4", &m, VarOrder::SmallestDomain), 24);
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
    assert_eq!(enumerate_checked("table_fixed", &m, VarOrder::InputOrder), 3);
}

#[test]
fn a_table_with_no_rows() {
    let mut m = Model::new();
    let x = m.int_var_named("x", 0, 2);
    m.post(Table::new(&[x], &[]));
    assert_eq!(enumerate_checked("table_empty", &m, VarOrder::InputOrder), 0);
}

// ---- linear ----

#[test]
fn linear_inferences_are_asserted_for_now() {
    // x + 2y = 7, x - y <= 1 over 0..=5: (1, 3) and (3, 2). The bounds
    // reasoning is logged as unchecked assertions until it has `pol`
    // derivations; everything else is still checked.
    let mut m = Model::new();
    let (x, y) = (m.int_var_named("x", 0, 5), m.int_var_named("y", 0, 5));
    m.post(Linear::eq(&[(x, 1), (y, 2)], 7));
    m.post(Linear::le(&[(x, 1), (y, -1)], 1));
    assert_eq!(enumerate_checked("linear_small", &m, VarOrder::InputOrder), 2);
    let pbp = std::fs::read_to_string(stem("linear_small").with_extension("pbp")).unwrap();
    assert!(pbp.lines().any(|l| l.starts_with("a ")), "expected unchecked steps");
}

// ---- regular ----

/// `0* 111 0+ 11 0*`: a nonogram row with the clue "3 2".
fn three_two() -> Automaton {
    let edges = [(0, 0, 0), (0, 1, 1), (1, 1, 2), (2, 1, 3), (3, 0, 4), (4, 0, 4), (4, 1, 5), (5, 1, 6), (6, 0, 6)];
    Automaton::new(7, &edges, &[6]).unwrap()
}

#[test]
fn regular_nonogram_row() {
    let mut m = Model::new();
    let cells: Vec<VarId> = (0..10).map(|i| m.int_var_named(&format!("c{i}"), 0, 1)).collect();
    m.post_named("row", Regular::new(&cells, three_two())).unwrap();
    assert_eq!(enumerate_checked("regular_row", &m, VarOrder::InputOrder), 15);
}

#[test]
fn regular_needs_helpers_for_forward_deaths() {
    // The hand-checked example: A goes to B or C on 0 or 1; B and C loop on
    // 0 and 1 and go to D on 2; D (accepting) loops on 0. Over {0, 1, 2},
    // reaching D at layer 2 needs X1 = 2, with two states behind it.
    let edges = [(0, 0, 1), (0, 1, 2), (1, 0, 1), (1, 1, 1), (1, 2, 3), (2, 0, 2), (2, 1, 2), (2, 2, 3), (3, 0, 3)];
    let a = Automaton::new(4, &edges, &[3]).unwrap();
    for order in [VarOrder::InputOrder, VarOrder::SmallestDomain] {
        let mut m = Model::new();
        let x: Vec<VarId> = (0..4).map(|i| m.int_var_named(&format!("x{i}"), 0, 2)).collect();
        m.post_named("r", Regular::new(&x, a.clone())).unwrap();
        let expected = count(&[(0, 2); 4], &|v| a.accepts(v));
        assert_eq!(enumerate_checked(&format!("regular_helpers_{order:?}"), &m, order), expected);
    }
}

#[test]
fn regular_with_a_repeated_variable() {
    // x y x y with "no two equal neighbours" over {0, 1, 2}.
    let edges: Vec<(usize, i64, usize)> =
        (0..4).flat_map(|q| (0..3).filter(move |&v| q == 0 || v + 1 != q as i64).map(move |v| (q, v, v as usize + 1))).collect();
    let a = Automaton::new(4, &edges, &[1, 2, 3]).unwrap();
    let mut m = Model::new();
    let (x, y) = (m.int_var_named("x", 0, 2), m.int_var_named("y", 0, 2));
    m.post(Regular::new(&[x, y, x, y], a.clone()));
    let expected = count(&[(0, 2); 2], &|v| a.accepts(&[v[0], v[1], v[0], v[1]]));
    assert_eq!(enumerate_checked("regular_repeated", &m, VarOrder::InputOrder), expected);
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
    domains.iter().enumerate().map(|(i, &(lo, hi))| m.int_var_named(&format!("v{i}"), lo, hi)).collect()
}

fn order(input_order: bool) -> VarOrder {
    if input_order { VarOrder::InputOrder } else { VarOrder::SmallestDomain }
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
                let edge = prop::option::weighted(0.6, 0..k);
                (Just(d.clone()), Just(k), prop::collection::vec(prop::collection::vec(edge, 8), k), prop::collection::vec(any::<bool>(), k))
            })
        }),
        input_order: bool,
    ) {
        // Symbols -4..=3, the same range the domains come from.
        let edges: Vec<(usize, i64, usize)> = table
            .iter()
            .enumerate()
            .flat_map(|(q, row)| row.iter().enumerate().filter_map(move |(s, t)| t.map(|t| (q, s as i64 - 4, t))))
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
}
