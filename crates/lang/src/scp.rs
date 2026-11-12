//! Reading `.scp` (s-expression constraint programming) files.
//!
//! The format is the four-section version 1 form written by the Glasgow
//! Constraint Solver and checked by CakePB-CP:
//!
//! ```text
//! ( (version 1)
//!   (variables (x 0 10) (y 0 10))
//!   (constraints (c1 lin_equals (2 x 1 y) 12) (c2 not_equals x y))
//!   (prob_type enumerate) )
//! ```
//!
//! Like GCS's reader this is strict: all four sections, in that order,
//! version exactly 1, and anything it can't make sense of is an error.
//! A keyword it has no case for is reported separately, as
//! [`ScpError::Unsupported`], so callers can tell "not implemented yet" from
//! "broken file".
//!
//! Anywhere a variable can appear, an integer constant can appear instead.

use std::collections::HashMap;
use std::fmt;

use solver::{
    AllDifferent, Automaton, Cell, Constraint, Linear, Model, NotEqual, Regular, Table, VarId,
};

use crate::sexpr::{self, SExpr, SExprError};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScpError {
    /// Not a well-formed s-expression.
    Syntax(SExprError),
    /// Well-formed, but not a valid `.scp` document.
    Malformed(String),
    /// A constraint keyword this reader has no case for (yet).
    Unsupported(String),
}

impl fmt::Display for ScpError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ScpError::Syntax(e) => write!(f, "syntax error: {e}"),
            ScpError::Malformed(msg) => f.write_str(msg),
            ScpError::Unsupported(op) => write!(f, "unsupported constraint '{op}'"),
        }
    }
}

impl std::error::Error for ScpError {}

impl From<SExprError> for ScpError {
    fn from(e: SExprError) -> Self {
        ScpError::Syntax(e)
    }
}

fn malformed<T>(msg: impl Into<String>) -> Result<T, ScpError> {
    Err(ScpError::Malformed(msg.into()))
}

/// What kind of answer the document asks for.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ProbType {
    /// Is there a solution?
    Decide,
    /// List every solution.
    Enumerate,
    Minimize(VarId),
    Maximize(VarId),
}

/// Everything the document says besides the constraints themselves.
#[derive(Clone, Debug)]
pub struct ScpModel {
    /// Each declared variable, in declaration order.
    pub variables: Vec<(String, VarId)>,
    pub prob_type: ProbType,
}

impl ScpModel {
    pub fn var(&self, name: &str) -> Option<VarId> {
        self.variables
            .iter()
            .find(|(n, _)| n == name)
            .map(|&(_, v)| v)
    }
}

/// Build a [`Model`] from the text of a `.scp` document. On error nothing is
/// returned, so there's never a half-built model.
pub fn read_scp(text: &str) -> Result<(Model, ScpModel), ScpError> {
    let top = sexpr::parse(text)?;
    let sections = list(&top, "the document")?;
    let [version, variables, constraints, prob_type] = sections else {
        return malformed(
            "a document is ((version 1) (variables ...) (constraints ...) (prob_type ...))",
        );
    };

    // The version first, so an incompatible producer is caught before
    // anything else is read.
    match section(version, "version")? {
        [v] if integer(v, "the version")? == 1 => {}
        [v] => {
            return malformed(format!(
                "unsupported version {v}: only version 1 is accepted"
            ));
        }
        _ => return malformed("the version section is (version 1)"),
    }
    let objective = check_prob_type(prob_type)?;

    let mut reader = Reader {
        model: Model::new(),
        vars: HashMap::new(),
    };
    let mut declared = Vec::new();
    for decl in section(variables, "variables")? {
        let [name, lo, hi] = list(decl, "a variable declaration")? else {
            return malformed(format!(
                "a variable declaration is (name lower upper), got {decl}"
            ));
        };
        let name = atom(name, "a variable name")?;
        let var = reader.model.int_var_named(
            name,
            integer(lo, "a lower bound")?,
            integer(hi, "an upper bound")?,
        );
        if reader.vars.insert(name.to_string(), var).is_some() {
            return malformed(format!("duplicate variable '{name}'"));
        }
        declared.push((name.to_string(), var));
    }

    for c in section(constraints, "constraints")? {
        reader.constraint(c)?;
    }

    let prob_type = match objective {
        Objective::Decide => ProbType::Decide,
        Objective::Enumerate => ProbType::Enumerate,
        Objective::Optimise { maximise, target } => {
            let var = reader.var(&target)?;
            if maximise {
                ProbType::Maximize(var)
            } else {
                ProbType::Minimize(var)
            }
        }
    };
    let scp = ScpModel {
        variables: declared,
        prob_type,
    };
    Ok((reader.model, scp))
}

/// The prob_type section, checked before anything is built. An objective
/// can only be resolved once the variables exist.
enum Objective {
    Decide,
    Enumerate,
    Optimise { maximise: bool, target: SExpr },
}

fn check_prob_type(e: &SExpr) -> Result<Objective, ScpError> {
    let [spec] = section(e, "prob_type")? else {
        return malformed("the prob_type section takes exactly one specification");
    };
    match spec {
        SExpr::Atom(a) if a == "decide" => Ok(Objective::Decide),
        SExpr::Atom(a) if a == "enumerate" => Ok(Objective::Enumerate),
        SExpr::Atom(a) => malformed(format!("unknown prob_type '{a}'")),
        SExpr::List(parts) => match parts.as_slice() {
            [SExpr::Atom(dir), target @ SExpr::Atom(_)]
                if dir == "minimize" || dir == "maximize" =>
            {
                Ok(Objective::Optimise {
                    maximise: dir == "maximize",
                    target: target.clone(),
                })
            }
            _ => malformed("an objective is (minimize var) or (maximize var)"),
        },
    }
}

struct Reader {
    model: Model,
    vars: HashMap<String, VarId>,
}

impl Reader {
    /// A declared variable, or an integer constant standing in for one.
    fn var(&mut self, e: &SExpr) -> Result<VarId, ScpError> {
        let a = atom(e, "a variable")?;
        if let Some(&v) = self.vars.get(a) {
            return Ok(v);
        }
        match parse_integer(a) {
            Some(value) => Ok(self.model.constant(value)),
            None => malformed(format!("unknown variable '{a}'")),
        }
    }

    fn var_list(&mut self, e: &SExpr, what: &str) -> Result<Vec<VarId>, ScpError> {
        list(e, what)?.iter().map(|v| self.var(v)).collect()
    }

    /// Add `coeff * e` to a sum. A constant goes into the sum's constant part
    /// instead of becoming a fixed variable.
    fn add_term(&mut self, sum: &mut Sum, coeff: i64, e: &SExpr) -> Result<(), ScpError> {
        let a = atom(e, "a linear term")?;
        if let Some(&v) = self.vars.get(a) {
            sum.terms.push((v, coeff));
            return Ok(());
        }
        let Some(value) = parse_integer(a) else {
            return malformed(format!("unknown variable '{a}'"));
        };
        let product = coeff.checked_mul(value);
        sum.constant = product
            .and_then(|p| sum.constant.checked_add(p))
            .ok_or_else(|| ScpError::Malformed("integer overflow in a linear constraint".into()))?;
        Ok(())
    }

    fn post(&mut self, label: &str, c: impl Constraint + 'static) -> Result<(), ScpError> {
        self.model
            .post_named(label, c)
            .or_else(|e| malformed(e.to_string()))
    }

    /// One constraint: `(label op args...)`.
    fn constraint(&mut self, c: &SExpr) -> Result<(), ScpError> {
        let terms = list(c, "a constraint")?;
        let [label, op, args @ ..] = terms else {
            return malformed(format!("a constraint is (label op ...), got {c}"));
        };
        let label = atom(label, "a constraint label")?;
        let op = atom(op, "a constraint keyword")?;
        let wrong = || malformed(format!("wrong arguments for '{op}' in {c}"));

        match op {
            "not_equals" => {
                let [x, y] = args else { return wrong() };
                let (x, y) = (self.var(x)?, self.var(y)?);
                self.post(label, NotEqual::new(x, y))
            }
            "equals" => {
                let [x, y] = args else { return wrong() };
                // x - y = 0
                let sum = self.sum_of(&[(1, x), (-1, y)])?;
                self.post(label, sum.eq(0)?)
            }
            "less_than" | "less_equal" | "greater_than" | "greater_equal" => {
                let [x, y] = args else { return wrong() };
                // All four as `a - b <= k`.
                let (a, b, k) = match op {
                    "less_than" => (x, y, -1),    //   x <  y  is  x - y <= -1
                    "less_equal" => (x, y, 0),    //   x <= y  is  x - y <= 0
                    "greater_than" => (y, x, -1), //   x >  y  is  y - x <= -1
                    _ => (y, x, 0),               //   x >= y  is  y - x <= 0
                };
                let sum = self.sum_of(&[(1, a), (-1, b)])?;
                self.post(label, sum.le(k)?)
            }
            "plus" | "minus" => {
                // (label plus a b r) is a + b = r; minus is a - b = r.
                let [a, b, r] = args else { return wrong() };
                let sign = if op == "plus" { 1 } else { -1 };
                let sum = self.sum_of(&[(1, a), (sign, b), (-1, r)])?;
                self.post(label, sum.eq(0)?)
            }
            "lin_equals" | "lin_less_equal" | "lin_less_than" | "lin_greater_equal"
            | "lin_greater_than" => {
                let [pairs, value] = args else { return wrong() };
                let pairs = list(pairs, "a linear coefficient/variable list")?;
                if pairs.len() % 2 != 0 {
                    return malformed(format!(
                        "'{op}' needs coefficient/variable pairs, got {}",
                        SExpr::List(pairs.to_vec())
                    ));
                }
                let mut sum = Sum::default();
                for pair in pairs.chunks(2) {
                    let coeff = integer(&pair[0], "a coefficient")?;
                    self.add_term(&mut sum, coeff, &pair[1])?;
                }
                let value = integer(value, "a right-hand side")?;
                let constraint = match op {
                    "lin_equals" => sum.eq(value)?,
                    "lin_less_equal" => sum.le(value)?,
                    "lin_less_than" => sum.le(step(value, -1)?)?,
                    "lin_greater_equal" => sum.ge(value)?,
                    _ => sum.ge(step(value, 1)?)?,
                };
                self.post(label, constraint)
            }
            "all_different" => {
                let [vars] = args else { return wrong() };
                let vars = self.var_list(vars, "an all_different variable list")?;
                self.post(label, AllDifferent::new(&vars))
            }
            "table" => {
                let [rows, vars] = args else { return wrong() };
                let rows = list(rows, "a table's rows")?
                    .iter()
                    .map(|row| list(row, "a table row")?.iter().map(cell).collect())
                    .collect::<Result<Vec<Vec<Cell>>, ScpError>>()?;
                let vars = self.var_list(vars, "a table variable list")?;
                // A row of the wrong length is legal and makes the constraint
                // unsatisfiable; Table::new already handles that.
                self.post(label, Table::new(&vars, &rows))
            }
            "regular" => {
                let [vars, num_states, edges, finals] = args else {
                    return wrong();
                };
                let vars = self.var_list(vars, "a regular variable list")?;
                let automaton = automaton(num_states, edges, finals)
                    .map_err(|e| ScpError::Malformed(format!("in constraint '{label}': {e}")))?;
                self.post(label, Regular::new(&vars, automaton))
            }
            _ => Err(ScpError::Unsupported(op.to_string())),
        }
    }

    fn sum_of(&mut self, terms: &[(i64, &SExpr)]) -> Result<Sum, ScpError> {
        let mut sum = Sum::default();
        for &(coeff, e) in terms {
            self.add_term(&mut sum, coeff, e)?;
        }
        Ok(sum)
    }
}

/// `Σ terms + constant`, built while reading a linear-style constraint.
#[derive(Default)]
struct Sum {
    terms: Vec<(VarId, i64)>,
    constant: i64,
}

impl Sum {
    /// The right-hand side once the constant part has moved across.
    fn rhs(&self, value: i64) -> Result<i64, ScpError> {
        value
            .checked_sub(self.constant)
            .ok_or_else(|| ScpError::Malformed("integer overflow in a linear constraint".into()))
    }

    fn le(&self, value: i64) -> Result<Linear, ScpError> {
        Ok(Linear::le(&self.terms, self.rhs(value)?))
    }

    fn ge(&self, value: i64) -> Result<Linear, ScpError> {
        Ok(Linear::ge(&self.terms, self.rhs(value)?))
    }

    fn eq(&self, value: i64) -> Result<Linear, ScpError> {
        Ok(Linear::eq(&self.terms, self.rhs(value)?))
    }
}

/// `value + by`, for turning a strict inequality into a non-strict one.
fn step(value: i64, by: i64) -> Result<i64, ScpError> {
    value
        .checked_add(by)
        .ok_or_else(|| ScpError::Malformed("integer overflow in a linear constraint".into()))
}

fn cell(e: &SExpr) -> Result<Cell, ScpError> {
    match atom(e, "a table entry")? {
        "*" => Ok(Cell::Any),
        _ => Ok(Cell::Val(integer(e, "a table entry")?)),
    }
}

fn list<'a>(e: &'a SExpr, what: &str) -> Result<&'a [SExpr], ScpError> {
    e.as_list()
        .ok_or_else(|| ScpError::Malformed(format!("expected a list for {what}, got '{e}'")))
}

fn atom<'a>(e: &'a SExpr, what: &str) -> Result<&'a str, ScpError> {
    e.as_atom()
        .ok_or_else(|| ScpError::Malformed(format!("expected an atom for {what}, got {e}")))
}

/// A top-level section `(tag items...)`: check the tag, return the items.
fn section<'a>(e: &'a SExpr, tag: &str) -> Result<&'a [SExpr], ScpError> {
    match e.as_list() {
        Some([SExpr::Atom(t), items @ ..]) if t == tag => Ok(items),
        _ => malformed(format!("expected a ({tag} ...) section, got {e}")),
    }
}

fn integer(e: &SExpr, what: &str) -> Result<i64, ScpError> {
    let a = atom(e, what)?;
    parse_integer(a)
        .ok_or_else(|| ScpError::Malformed(format!("expected an integer for {what}, got '{a}'")))
}

/// An optional minus sign and digits; `+5`, `0x10` and friends are not
/// integers here.
fn parse_integer(a: &str) -> Option<i64> {
    let digits = a.strip_prefix('-').unwrap_or(a);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    a.parse().ok()
}

/// A `regular` constraint's automaton, from GCS's form: `nstates`, then one
/// list of `(symbol target)` edges per state in order, then the accepting
/// states. The start state is 0. Only deterministic automata are accepted.
fn automaton(num_states: &SExpr, edges: &SExpr, finals: &SExpr) -> Result<Automaton, String> {
    let state = |e: &SExpr, what: &str| -> Result<usize, String> {
        let q = integer(e, what).map_err(|e| e.to_string())?;
        usize::try_from(q).map_err(|_| format!("{what} can't be negative, got {q}"))
    };
    let num_states = state(num_states, "the number of states")?;
    let per_state = list(edges, "the per-state edge lists").map_err(|e| e.to_string())?;
    if per_state.len() != num_states {
        return Err(format!(
            "{num_states} states but {} edge lists",
            per_state.len()
        ));
    }
    let mut transitions = Vec::new();
    for (q, edge_list) in per_state.iter().enumerate() {
        for edge in list(edge_list, "a state's edge list").map_err(|e| e.to_string())? {
            let [symbol, target] = list(edge, "an edge").map_err(|e| e.to_string())? else {
                return Err(format!("an edge is (symbol target), got {edge}"));
            };
            let symbol = integer(symbol, "an edge's symbol").map_err(|e| e.to_string())?;
            transitions.push((q, symbol, state(target, "an edge's target")?));
        }
    }
    let finals = list(finals, "the accepting states")
        .map_err(|e| e.to_string())?
        .iter()
        .map(|f| state(f, "an accepting state"))
        .collect::<Result<Vec<_>, _>>()?;
    Automaton::new(num_states, &transitions, &finals).map_err(|e| e.to_string())
}

#[cfg(test)]
mod tests {
    use std::ops::ControlFlow;

    use solver::Config;

    use super::*;

    fn doc(vars: &str, cons: &str, prob: &str) -> String {
        format!("( (version 1) (variables {vars}) (constraints {cons}) (prob_type {prob}) )")
    }

    fn count(text: &str) -> u64 {
        let (model, _) = read_scp(text).unwrap();
        solver::enumerate(&model, &Config::default(), |_| ControlFlow::Continue(())).unwrap()
    }

    // --- Document structure --------------------------------------------------

    #[test]
    fn reads_variables_and_prob_type() {
        let (model, scp) = read_scp(&doc("(x 0 10) (y -3 3)", "", "decide")).unwrap();
        assert_eq!(model.num_vars(), 2);
        assert_eq!(
            scp.variables
                .iter()
                .map(|(n, _)| n.as_str())
                .collect::<Vec<_>>(),
            ["x", "y"]
        );
        assert_eq!(scp.prob_type, ProbType::Decide);
        let (_, scp) = read_scp(&doc("(x 0 10)", "", "(maximize x)")).unwrap();
        assert_eq!(scp.prob_type, ProbType::Maximize(scp.var("x").unwrap()));
    }

    #[test]
    fn the_figure_1_example_from_the_paper() {
        let text = "((version 1)
                      (variables (x 0 10) (y 0 10) (p 0 100))
                      (constraints
                          (c1 lin_equals (2 x 1 y) 12)
                          (c2 multiply x y p))
                      (prob_type (maximize p)))";
        // We don't have multiply yet: that's Unsupported, not Malformed.
        assert_eq!(
            read_scp(text).unwrap_err(),
            ScpError::Unsupported("multiply".into())
        );
    }

    #[test]
    fn structural_errors_are_malformed() {
        let bad = [
            "( (version 2) (variables) (constraints) (prob_type decide) )",
            "( (version 1) (variables) (constraints) )",
            "( (variables) (version 1) (constraints) (prob_type decide) )",
            "( (version 1) (variables) (constraints) (prob_type wibble) )",
            "( (version 1) (variables (x 0)) (constraints) (prob_type decide) )",
            "( (version 1) (variables (x 0 1) (x 0 1)) (constraints) (prob_type decide) )",
            "( (version 1) (variables (x 0 a)) (constraints) (prob_type decide) )",
            "( (version 1) (variables (x 0 1)) (constraints (c not_equals x z)) (prob_type decide) )",
            "( (version 1) (variables (x 0 1)) (constraints (c not_equals x)) (prob_type decide) )",
            "( (version 1) (variables (x 0 1) (y 0 1)) (constraints (c not_equals x y) (c not_equals x y)) (prob_type decide) )",
            "( (version 1) (variables (x 0 1)) (constraints (c lin_equals (1 x 2) 0)) (prob_type decide) )",
            "( (version 1) (variables (x 0 1)) (constraints) (prob_type (minimize nope)) )",
        ];
        for text in bad {
            assert!(
                matches!(read_scp(text), Err(ScpError::Malformed(_))),
                "{text}"
            );
        }
        assert!(matches!(
            read_scp("( (version 1)"),
            Err(ScpError::Syntax(_))
        ));
    }

    #[test]
    fn unknown_and_reified_keywords_are_unsupported() {
        for op in ["multiply", "not_equals_iff", "lin_not_equals", "wibble"] {
            let text = doc("(x 0 1) (y 0 1)", &format!("(c {op} x y)"), "decide");
            assert_eq!(
                read_scp(&text).unwrap_err(),
                ScpError::Unsupported(op.into())
            );
        }
    }

    #[test]
    fn integers_are_strict() {
        assert_eq!(parse_integer("-12"), Some(-12));
        for not_int in ["+5", "", "-", "1.5", "0x10", "12a"] {
            assert_eq!(parse_integer(not_int), None, "{not_int}");
        }
    }

    #[test]
    fn inconsistent_bounds_give_no_solutions() {
        assert_eq!(count(&doc("(x 5 2)", "", "enumerate")), 0);
    }

    #[test]
    fn unconstrained_variables_count() {
        // As in GCS's tests: a spare variable multiplies the count.
        assert_eq!(count(&doc("(x 0 2) (y 0 1)", "", "enumerate")), 6);
    }

    // --- Each keyword, checked by its number of solutions -------------------

    #[test]
    fn not_equals_and_equals() {
        assert_eq!(
            count(&doc("(x 0 2) (y 0 2)", "(c not_equals x y)", "enumerate")),
            6
        );
        assert_eq!(
            count(&doc("(x 0 2) (y 0 2)", "(c equals x y)", "enumerate")),
            3
        );
    }

    #[test]
    fn comparisons() {
        // x, y in 0..2: 3 pairs with x < y, 6 with x <= y.
        let v = "(x 0 2) (y 0 2)";
        assert_eq!(count(&doc(v, "(c less_than x y)", "enumerate")), 3);
        assert_eq!(count(&doc(v, "(c less_equal x y)", "enumerate")), 6);
        assert_eq!(count(&doc(v, "(c greater_than x y)", "enumerate")), 3);
        assert_eq!(count(&doc(v, "(c greater_equal x y)", "enumerate")), 6);
        // x < x has no solutions.
        assert_eq!(count(&doc(v, "(c less_than x x)", "enumerate")), 0);
    }

    #[test]
    fn plus_and_minus() {
        // a + b = r and a - b = r, all in 0..3: 10 and 10.
        let v = "(a 0 3) (b 0 3) (r 0 3)";
        assert_eq!(count(&doc(v, "(c plus a b r)", "enumerate")), 10);
        assert_eq!(count(&doc(v, "(c minus a b r)", "enumerate")), 10);
    }

    #[test]
    fn linear_family() {
        // x + 2y over x, y in 0..3; check each relation against brute force.
        let v = "(x 0 3) (y 0 3)";
        let brute = |ok: fn(i64) -> bool| {
            (0..=3)
                .flat_map(|x| (0..=3).map(move |y| x + 2 * y))
                .filter(|&s| ok(s))
                .count() as u64
        };
        assert_eq!(
            count(&doc(v, "(c lin_equals (1 x 2 y) 4)", "enumerate")),
            brute(|s| s == 4)
        );
        assert_eq!(
            count(&doc(v, "(c lin_less_equal (1 x 2 y) 4)", "enumerate")),
            brute(|s| s <= 4)
        );
        assert_eq!(
            count(&doc(v, "(c lin_less_than (1 x 2 y) 4)", "enumerate")),
            brute(|s| s < 4)
        );
        assert_eq!(
            count(&doc(v, "(c lin_greater_equal (1 x 2 y) 4)", "enumerate")),
            brute(|s| s >= 4)
        );
        assert_eq!(
            count(&doc(v, "(c lin_greater_than (1 x 2 y) 4)", "enumerate")),
            brute(|s| s > 4)
        );
    }

    #[test]
    fn all_different_and_table() {
        // GCS's own all_different_sat and table_sat cases.
        assert_eq!(
            count(&doc(
                "(A 0 3) (B 0 3) (C 0 3)",
                "(_1 all_different (A B C))",
                "enumerate"
            )),
            24
        );
        assert_eq!(
            count(&doc(
                "(A 0 2) (B 0 2)",
                "(_1 table ((0 1) (1 2) (2 0)) (A B))",
                "enumerate"
            )),
            3
        );
        // Wildcards: (1 * 3) and (* 2 *) over 1..3 has 11 solutions.
        let v = "(a 1 3) (b 1 3) (c 1 3)";
        assert_eq!(
            count(&doc(v, "(t table ((1 * 3) (* 2 *)) (a b c))", "enumerate")),
            11
        );
    }

    // --- Constants -----------------------------------------------------------

    #[test]
    fn constants_fold_into_linear_constraints() {
        // x + 3 = 5 needs no extra variable.
        let (model, _) = read_scp(&doc("(x 0 9)", "(c plus x 3 5)", "enumerate")).unwrap();
        assert_eq!(model.num_vars(), 1);
        assert_eq!(count(&doc("(x 0 9)", "(c plus x 3 5)", "enumerate")), 1);
        assert_eq!(
            count(&doc(
                "(x 0 9)",
                "(c lin_less_equal (2 x 1 4) 10)",
                "enumerate"
            )),
            4
        );
    }

    #[test]
    fn constants_elsewhere_become_shared_fixed_variables() {
        let text = doc(
            "(x 0 3) (y 0 3)",
            "(a not_equals x 2) (b all_different (y 2 x))",
            "enumerate",
        );
        let (mut model, _) = read_scp(&text).unwrap();
        assert_eq!(model.num_vars(), 3); // x, y and one shared constant 2
        let two = model.constant(2); // asking again finds the same variable
        assert_eq!(model.num_vars(), 3);
        assert_eq!(model.constant_value(two), Some(2));
        // x != 2, and x, y, 2 all different: x in {0,1,3}, y in {0,1,3} \ {x}: 6.
        assert_eq!(count(&text), 6);
    }

    #[test]
    fn a_constant_objective_is_allowed() {
        let (model, scp) = read_scp(&doc("(x 0 1)", "", "(minimize 3)")).unwrap();
        let ProbType::Minimize(v) = scp.prob_type else {
            panic!()
        };
        assert_eq!(model.constant_value(v), Some(3));
    }

    #[test]
    fn labels_are_kept() {
        let (model, _) = read_scp(&doc(
            "(x 0 1) (y 0 1)",
            "(first not_equals x y) (_2 equals x y)",
            "decide",
        ))
        .unwrap();
        assert_eq!(model.constraint_names(), ["first", "_2"]);
    }
}
