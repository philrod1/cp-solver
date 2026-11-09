//! SEND + MORE = MONEY: one all-different and one linear equality.
//!
//! Each letter is a different digit, and S and M can't be 0. The unique
//! answer is 9567 + 1085 = 10652. The solution is checked by redoing the
//! arithmetic, not by trusting the model.

use solver::{AllDifferent, Config, Linear, Model, Outcome, VarId, VarOrder};

struct Letters {
    s: VarId,
    e: VarId,
    n: VarId,
    d: VarId,
    m: VarId,
    o: VarId,
    r: VarId,
    y: VarId,
}

fn model() -> (Model, Letters) {
    let mut model = Model::new();
    let mut digit = |lo| model.int_var(lo, 9);
    let l = Letters {
        s: digit(1),
        e: digit(0),
        n: digit(0),
        d: digit(0),
        m: digit(1),
        o: digit(0),
        r: digit(0),
        y: digit(0),
    };
    let Letters {
        s,
        e,
        n,
        d,
        m,
        o,
        r,
        y,
    } = l;

    model.post(AllDifferent::new(&[s, e, n, d, m, o, r, y]));

    // Written out as the sum reads, with letters repeated. Normalising
    // merges them: E appears three times, N, M and O twice.
    #[rustfmt::skip]
    let sum = [
        (s, 1000), (e, 100), (n, 10), (d, 1), //                 SEND
        (m, 1000), (o, 100), (r, 10), (e, 1), //               + MORE
        (m, -10000), (o, -1000), (n, -100), (e, -10), (y, -1), // - MONEY
    ];
    model.post(Linear::eq(&sum, 0));
    (model, l)
}

fn number(sol: &solver::Solution, digits: &[VarId]) -> i64 {
    digits.iter().fold(0, |acc, &v| 10 * acc + sol.value(v))
}

#[test]
fn finds_the_unique_answer() {
    for var_order in [VarOrder::SmallestDomain, VarOrder::InputOrder] {
        let (model, l) = model();
        let config = Config {
            var_order,
            ..Config::default()
        };
        let Outcome::Satisfiable(sol) = solver::solve(&model, &config).unwrap() else {
            panic!("{var_order:?}: expected a solution");
        };

        let send = number(&sol, &[l.s, l.e, l.n, l.d]);
        let more = number(&sol, &[l.m, l.o, l.r, l.e]);
        let money = number(&sol, &[l.m, l.o, l.n, l.e, l.y]);
        assert_eq!(send + more, money, "{var_order:?}: the sum doesn't add up");

        let mut digits: Vec<i64> = [l.s, l.e, l.n, l.d, l.m, l.o, l.r, l.y]
            .iter()
            .map(|&v| sol.value(v))
            .collect();
        digits.sort_unstable();
        digits.dedup();
        assert_eq!(digits.len(), 8, "{var_order:?}: letters share a digit");

        assert_eq!((send, more, money), (9567, 1085, 10652), "{var_order:?}");
    }
}

#[test]
fn no_answer_with_a_wrong_digit() {
    // The unique answer has Y = 2, so forcing Y = 3 leaves none.
    let (mut model, l) = model();
    model.post(Linear::eq(&[(l.y, 1)], 3));
    let outcome = solver::solve(&model, &Config::default()).unwrap();
    assert!(matches!(outcome, Outcome::Unsatisfiable), "got {outcome:?}");
}
