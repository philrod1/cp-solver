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
//! Something it has no case for, such as an unknown keyword, is reported
//! as [`ErrorKind::Unsupported`], so callers can tell "not implemented yet"
//! from "broken file".
//!
//! Every error says which part of the text it is about. [`read_scp`] stops
//! at the first; [`check_scp`] reads on past each bad declaration or
//! constraint and reports them all.
//!
//! Anywhere a variable can appear, an integer constant can appear instead.

use std::collections::HashMap;
use std::fmt;

use solver::{
    AllDifferent, Automaton, Cell, Constraint, Cumulative, Linear, MinMax, Model, NotEqual,
    Regular, Table, VarId,
};

use crate::sexpr::{self, Node, SExpr, SExprError, Span};

/// What is wrong with a document, and where.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScpError {
    pub kind: ErrorKind,
    /// What is wrong, without the position.
    pub message: String,
    /// The text at fault.
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    /// Not a well-formed s-expression.
    Syntax,
    /// Well-formed, but not a valid `.scp` document.
    Malformed,
    /// Valid, but uses something this reader can't handle yet.
    Unsupported,
}

impl fmt::Display for ScpError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let at = self.span.start;
        write!(
            f,
            "line {}, column {}: {}",
            at.line, at.column, self.message
        )
    }
}

impl std::error::Error for ScpError {}

impl From<SExprError> for ScpError {
    fn from(e: SExprError) -> Self {
        ScpError {
            kind: ErrorKind::Syntax,
            message: e.message,
            span: e.span,
        }
    }
}

fn error(kind: ErrorKind, at: &SExpr, message: impl Into<String>) -> ScpError {
    ScpError {
        kind,
        message: message.into(),
        span: at.span,
    }
}

fn malformed<T>(at: &SExpr, message: impl Into<String>) -> Result<T, ScpError> {
    Err(error(ErrorKind::Malformed, at, message))
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

/// A constraint keyword the reader understands: in a document, a
/// constraint is `(label keyword arguments...)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ConstraintKind {
    pub keyword: &'static str,
    /// What goes after the keyword, one name per argument, e.g. `x`, or
    /// `(var ...)` for a list. Anywhere a variable goes, an integer can
    /// go instead.
    pub arguments: &'static [&'static str],
    /// What the constraint says, in one line.
    pub summary: &'static str,
    /// Arguments that read, over variables `x`, `y` and `z` from 0 to 3.
    pub example: &'static str,
}

const fn kind(
    keyword: &'static str,
    arguments: &'static [&'static str],
    summary: &'static str,
    example: &'static str,
) -> ConstraintKind {
    ConstraintKind {
        keyword,
        arguments,
        summary,
        example,
    }
}

const PAIR: &[&str] = &["x", "y"];
const LINEAR: &[&str] = &["(coeff var ...)", "value"];

/// Every constraint keyword the reader understands. Any other keyword is
/// [`ErrorKind::Unsupported`].
pub const CONSTRAINTS: &[ConstraintKind] = &[
    kind("not_equals", PAIR, "x ≠ y", "x y"),
    kind("equals", PAIR, "x = y", "x y"),
    kind("less_than", PAIR, "x < y", "x y"),
    kind("less_equal", PAIR, "x ≤ y", "x y"),
    kind("greater_than", PAIR, "x > y", "x y"),
    kind("greater_equal", PAIR, "x ≥ y", "x y"),
    kind("plus", &["a", "b", "r"], "a + b = r", "x y z"),
    kind("minus", &["a", "b", "r"], "a − b = r", "x y z"),
    kind("lin_equals", LINEAR, "Σ coeff·var = value", "(1 x 2 y) 3"),
    kind(
        "lin_less_equal",
        LINEAR,
        "Σ coeff·var ≤ value",
        "(1 x 2 y) 3",
    ),
    kind(
        "lin_less_than",
        LINEAR,
        "Σ coeff·var < value",
        "(1 x 2 y) 3",
    ),
    kind(
        "lin_greater_equal",
        LINEAR,
        "Σ coeff·var ≥ value",
        "(1 x 2 y) 3",
    ),
    kind(
        "lin_greater_than",
        LINEAR,
        "Σ coeff·var > value",
        "(1 x -1 y) 0",
    ),
    kind(
        "all_different",
        &["(var ...)"],
        "no two of the variables are equal",
        "(x y z)",
    ),
    kind(
        "array_min",
        &["(var ...)", "result"],
        "result is the least of the variables",
        "(x y) z",
    ),
    kind(
        "array_max",
        &["(var ...)", "result"],
        "result is the greatest of the variables",
        "(x y) z",
    ),
    kind(
        "min",
        &["x", "y", "result"],
        "result is the lesser of x and y",
        "x y z",
    ),
    kind(
        "max",
        &["x", "y", "result"],
        "result is the greater of x and y",
        "x y z",
    ),
    kind(
        "table",
        &["(row ...)", "(var ...)"],
        "the variables match one of the rows; * in a row matches anything",
        "((0 1) (1 *)) (x y)",
    ),
    kind(
        "regular",
        &["(var ...)", "states", "(edges ...)", "(accepting ...)"],
        "the variables spell a word the automaton accepts: one list of \
         (symbol target) edges per state, starting from state 0",
        "(x y) 2 (((0 0) (1 1)) ((0 1))) (1)",
    ),
    kind(
        "cumulative",
        &["(start ...)", "(length ...)", "(height ...)", "capacity"],
        "tasks share a resource: at every time, the heights of the tasks \
         running total at most the capacity; lengths, heights and capacity \
         are constants",
        "(x y) (2 1) (1 1) 1",
    ),
];

/// Build a [`Model`] from the text of a `.scp` document. On error nothing is
/// returned, so there's never a half-built model. The error is the first
/// in the text.
pub fn read_scp(text: &str) -> Result<(Model, ScpModel), ScpError> {
    read(text).map_err(|errors| errors.into_iter().next().expect("at least one error"))
}

/// Every error in the text of a `.scp` document, in the order they appear:
/// none for a document [`read_scp`] accepts.
pub fn check_scp(text: &str) -> Vec<ScpError> {
    read(text).err().unwrap_or_default()
}

/// Read a document, carrying on past each bad declaration or constraint.
/// Errors in the shape of the document itself stop it, since there is
/// nothing sensible to read after them.
fn read(text: &str) -> Result<(Model, ScpModel), Vec<ScpError>> {
    let top = sexpr::parse(text).map_err(|e| vec![e.into()])?;
    let sections = list(&top, "the document").map_err(|e| vec![e])?;
    let [version, variables, constraints, prob_type] = sections else {
        let shape = "a document is ((version 1) (variables ...) (constraints ...) (prob_type ...))";
        return Err(vec![error(ErrorKind::Malformed, &top, shape)]);
    };

    // The version first, so an incompatible producer is caught before
    // anything else is read.
    check_version(version).map_err(|e| vec![e])?;
    let objective = check_prob_type(prob_type);
    let (declarations, constraints) = match (
        section(variables, "variables"),
        section(constraints, "constraints"),
    ) {
        (Ok(d), Ok(c)) => (d, c),
        (d, c) => {
            let errors = [d.err(), c.err(), objective.err()];
            return Err(errors.into_iter().flatten().collect());
        }
    };

    let mut errors = Vec::new();
    let mut reader = Reader {
        model: Model::new(),
        vars: HashMap::new(),
        declared: Vec::new(),
    };
    for decl in declarations {
        if let Err(e) = reader.declare(decl) {
            errors.push(e);
        }
    }
    for c in constraints {
        if let Err(e) = reader.constraint(c) {
            errors.push(e);
        }
    }
    let prob_type = match objective {
        Ok(Objective::Decide) => Some(ProbType::Decide),
        Ok(Objective::Enumerate) => Some(ProbType::Enumerate),
        Ok(Objective::Optimise { maximise, target }) => match reader.var(&target) {
            Ok(var) if maximise => Some(ProbType::Maximize(var)),
            Ok(var) => Some(ProbType::Minimize(var)),
            Err(e) => {
                errors.push(e);
                None
            }
        },
        Err(e) => {
            errors.push(e);
            None
        }
    };

    match prob_type {
        Some(prob_type) if errors.is_empty() => {
            let scp = ScpModel {
                variables: reader.declared,
                prob_type,
            };
            Ok((reader.model, scp))
        }
        _ => {
            errors.sort_by_key(|e| e.span.start.offset);
            Err(errors)
        }
    }
}

fn check_version(e: &SExpr) -> Result<(), ScpError> {
    match section(e, "version")? {
        [v] if integer(v, "the version")? == 1 => Ok(()),
        [v] => malformed(
            v,
            format!("unsupported version {v}: only version 1 is accepted"),
        ),
        _ => malformed(e, "the version section is (version 1)"),
    }
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
        return malformed(e, "the prob_type section takes exactly one specification");
    };
    match &spec.node {
        Node::Atom(a) if a == "decide" => Ok(Objective::Decide),
        Node::Atom(a) if a == "enumerate" => Ok(Objective::Enumerate),
        Node::Atom(a) if a == "minimize" || a == "maximize" => malformed(
            spec,
            format!("an objective is in its own brackets: (prob_type ({a} var))"),
        ),
        Node::Atom(a) => malformed(spec, format!("unknown prob_type '{a}'")),
        Node::List(parts) => match parts.as_slice() {
            [dir, target]
                if matches!(dir.as_atom(), Some("minimize" | "maximize"))
                    && target.as_atom().is_some() =>
            {
                Ok(Objective::Optimise {
                    maximise: dir.as_atom() == Some("maximize"),
                    target: target.clone(),
                })
            }
            _ => malformed(spec, "an objective is (minimize var) or (maximize var)"),
        },
    }
}

struct Reader {
    model: Model,
    vars: HashMap<String, VarId>,
    /// Each declared variable, in declaration order.
    declared: Vec<(String, VarId)>,
}

impl Reader {
    /// Declare `(name lower upper)`. A name with bad bounds is still
    /// declared, with a placeholder domain, so that its uses aren't
    /// reported as unknown variables as well.
    fn declare(&mut self, decl: &SExpr) -> Result<(), ScpError> {
        let shape = "a variable declaration is (name lower upper)";
        let parts = list(decl, "a variable declaration")?;
        let Some(name) = parts.first() else {
            return malformed(decl, shape);
        };
        let name_text = atom(name, "a variable name")?;
        if self.vars.contains_key(name_text) {
            return malformed(name, format!("duplicate variable '{name_text}'"));
        }
        let bounds = match parts {
            [_, lo, hi] => {
                integer(lo, "a lower bound").and_then(|lo| Ok((lo, integer(hi, "an upper bound")?)))
            }
            _ => malformed(decl, shape),
        };
        let (lo, hi) = *bounds.as_ref().unwrap_or(&(0, 0));
        let var = self.model.int_var_named(name_text, lo, hi);
        self.vars.insert(name_text.to_string(), var);
        self.declared.push((name_text.to_string(), var));
        bounds.map(|_| ())
    }

    /// A declared variable, or an integer constant standing in for one.
    fn var(&mut self, e: &SExpr) -> Result<VarId, ScpError> {
        let a = atom(e, "a variable")?;
        if let Some(&v) = self.vars.get(a) {
            return Ok(v);
        }
        match parse_integer(a) {
            Some(value) => Ok(self.model.constant(value)),
            None => malformed(e, format!("unknown variable '{a}'")),
        }
    }

    fn var_list(&mut self, e: &SExpr, what: &str) -> Result<Vec<VarId>, ScpError> {
        list(e, what)?.iter().map(|v| self.var(v)).collect()
    }

    /// A cumulative length, height or capacity: a constant, not negative.
    fn amount(&mut self, e: &SExpr, what: &str) -> Result<i64, ScpError> {
        let v = self.var(e)?;
        let Some(value) = self.model.constant_value(v) else {
            let message =
                "cumulative with variable lengths, heights or capacity isn't supported yet";
            return Err(error(ErrorKind::Unsupported, e, message));
        };
        if value < 0 {
            return malformed(e, format!("{what} can't be negative, got {value}"));
        }
        Ok(value)
    }

    fn amounts(&mut self, e: &SExpr, what: &str) -> Result<Vec<i64>, ScpError> {
        let items = list(e, &format!("a cumulative {what} list"))?;
        items.iter().map(|item| self.amount(item, what)).collect()
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
            return malformed(e, format!("unknown variable '{a}'"));
        };
        sum.constant = coeff
            .checked_mul(value)
            .and_then(|p| sum.constant.checked_add(p))
            .ok_or_else(|| overflow(e))?;
        Ok(())
    }

    fn post(&mut self, label: &SExpr, c: impl Constraint + 'static) -> Result<(), ScpError> {
        let name = atom(label, "a constraint label")?;
        self.model
            .post_named(name, c)
            .or_else(|e| malformed(label, e.to_string()))
    }

    /// One constraint: `(label op args...)`.
    fn constraint(&mut self, c: &SExpr) -> Result<(), ScpError> {
        let terms = list(c, "a constraint")?;
        let [label, keyword, args @ ..] = terms else {
            return malformed(c, "a constraint is (label op ...)");
        };
        atom(label, "a constraint label")?;
        let op = atom(keyword, "a constraint keyword")?;
        if !CONSTRAINTS.iter().any(|k| k.keyword == op) {
            let message = format!("unsupported constraint '{op}'");
            return Err(error(ErrorKind::Unsupported, keyword, message));
        }
        let wrong = || malformed(c, format!("wrong arguments for '{op}'"));

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
                self.post(label, sum.eq(0).ok_or_else(|| overflow(c))?)
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
                self.post(label, sum.le(k).ok_or_else(|| overflow(c))?)
            }
            "plus" | "minus" => {
                // (label plus a b r) is a + b = r; minus is a - b = r.
                let [a, b, r] = args else { return wrong() };
                let sign = if op == "plus" { 1 } else { -1 };
                let sum = self.sum_of(&[(1, a), (sign, b), (-1, r)])?;
                self.post(label, sum.eq(0).ok_or_else(|| overflow(c))?)
            }
            "lin_equals" | "lin_less_equal" | "lin_less_than" | "lin_greater_equal"
            | "lin_greater_than" => {
                let [pairs_list, value] = args else {
                    return wrong();
                };
                let pairs = list(pairs_list, "a linear coefficient/variable list")?;
                if pairs.len() % 2 != 0 {
                    let message = format!("'{op}' needs coefficient/variable pairs");
                    return malformed(pairs_list, message);
                }
                let mut sum = Sum::default();
                for pair in pairs.chunks(2) {
                    let coeff = integer(&pair[0], "a coefficient")?;
                    self.add_term(&mut sum, coeff, &pair[1])?;
                }
                let value = integer(value, "a right-hand side")?;
                let constraint = match op {
                    "lin_equals" => sum.eq(value),
                    "lin_less_equal" => sum.le(value),
                    "lin_less_than" => value.checked_sub(1).and_then(|v| sum.le(v)),
                    "lin_greater_equal" => sum.ge(value),
                    _ => value.checked_add(1).and_then(|v| sum.ge(v)),
                };
                self.post(label, constraint.ok_or_else(|| overflow(c))?)
            }
            "all_different" => {
                let [vars] = args else { return wrong() };
                let vars = self.var_list(vars, "an all_different variable list")?;
                self.post(label, AllDifferent::new(&vars))
            }
            "min" | "max" => {
                // CakePB-CP's binary form: (label max x y result).
                let [x, y, result] = args else { return wrong() };
                let (x, y, result) = (self.var(x)?, self.var(y)?, self.var(result)?);
                let constraint = if op == "min" {
                    MinMax::min(&[x, y], result)
                } else {
                    MinMax::max(&[x, y], result)
                };
                self.post(label, constraint)
            }
            "array_min" | "array_max" => {
                let [vars, result] = args else { return wrong() };
                let vars = self.var_list(vars, "an array_min or array_max variable list")?;
                let result = self.var(result)?;
                let constraint = if op == "array_min" {
                    MinMax::min(&vars, result)
                } else {
                    MinMax::max(&vars, result)
                };
                self.post(label, constraint)
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
                let automaton = automaton(num_states, edges, finals)?;
                self.post(label, Regular::new(&vars, automaton))
            }
            "cumulative" => {
                let [starts, lengths, heights, capacity] = args else {
                    return wrong();
                };
                let starts = self.var_list(starts, "a cumulative start list")?;
                let lengths_given = self.amounts(lengths, "length")?;
                let heights_given = self.amounts(heights, "height")?;
                let capacity = self.amount(capacity, "a capacity")?;
                if lengths_given.len() != starts.len() {
                    return malformed(lengths, "one length per start");
                }
                if heights_given.len() != starts.len() {
                    return malformed(heights, "one height per start");
                }
                let constraint = Cumulative::new(&starts, &lengths_given, &heights_given, capacity);
                self.post(label, constraint)
            }
            _ => unreachable!("'{op}' is in CONSTRAINTS but has no case here"),
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

/// Each of these is `None` if moving the constant across overflows.
impl Sum {
    fn le(&self, value: i64) -> Option<Linear> {
        Some(Linear::le(&self.terms, value.checked_sub(self.constant)?))
    }

    fn ge(&self, value: i64) -> Option<Linear> {
        Some(Linear::ge(&self.terms, value.checked_sub(self.constant)?))
    }

    fn eq(&self, value: i64) -> Option<Linear> {
        Some(Linear::eq(&self.terms, value.checked_sub(self.constant)?))
    }
}

fn overflow(at: &SExpr) -> ScpError {
    let message = "integer overflow in a linear constraint";
    error(ErrorKind::Malformed, at, message)
}

fn cell(e: &SExpr) -> Result<Cell, ScpError> {
    match atom(e, "a table entry")? {
        "*" => Ok(Cell::Any),
        _ => Ok(Cell::Val(integer(e, "a table entry")?)),
    }
}

fn list<'a>(e: &'a SExpr, what: &str) -> Result<&'a [SExpr], ScpError> {
    e.as_list().ok_or_else(|| {
        error(
            ErrorKind::Malformed,
            e,
            format!("expected a list for {what}, got '{e}'"),
        )
    })
}

fn atom<'a>(e: &'a SExpr, what: &str) -> Result<&'a str, ScpError> {
    e.as_atom().ok_or_else(|| {
        error(
            ErrorKind::Malformed,
            e,
            format!("expected an atom for {what}"),
        )
    })
}

/// A top-level section `(tag items...)`: check the tag, return the items.
fn section<'a>(e: &'a SExpr, tag: &str) -> Result<&'a [SExpr], ScpError> {
    match e.as_list() {
        Some([t, items @ ..]) if t.as_atom() == Some(tag) => Ok(items),
        _ => malformed(e, format!("expected a ({tag} ...) section")),
    }
}

fn integer(e: &SExpr, what: &str) -> Result<i64, ScpError> {
    let a = atom(e, what)?;
    parse_integer(a).ok_or_else(|| {
        let message = format!("expected an integer for {what}, got '{a}'");
        error(ErrorKind::Malformed, e, message)
    })
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
/// states. The start state is 0. A state may list several edges on the
/// same symbol.
fn automaton(num_states: &SExpr, edges: &SExpr, finals: &SExpr) -> Result<Automaton, ScpError> {
    let count = integer(num_states, "the number of states")?;
    let n = match usize::try_from(count) {
        Ok(n) if n > 0 => n,
        _ => {
            return malformed(
                num_states,
                format!("an automaton needs states, got {count}"),
            );
        }
    };
    let state = |e: &SExpr, what: &str| -> Result<usize, ScpError> {
        let q = integer(e, what)?;
        match usize::try_from(q) {
            Ok(q) if q < n => Ok(q),
            _ => malformed(
                e,
                format!("{what} must be a state from 0 to {}, got {q}", n - 1),
            ),
        }
    };
    let per_state = list(edges, "the per-state edge lists")?;
    if per_state.len() != n {
        let message = format!("{n} states but {} edge lists", per_state.len());
        return malformed(edges, message);
    }
    let mut transitions = Vec::new();
    for (q, edge_list) in per_state.iter().enumerate() {
        for edge in list(edge_list, "a state's edge list")? {
            let [symbol, target] = list(edge, "an edge")? else {
                return malformed(edge, "an edge is (symbol target)");
            };
            let symbol = integer(symbol, "an edge's symbol")?;
            transitions.push((q, symbol, state(target, "an edge's target")?));
        }
    }
    let finals = list(finals, "the accepting states")?
        .iter()
        .map(|f| state(f, "an accepting state"))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Automaton::new(n, &transitions, &finals).expect("states checked above"))
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

    /// The text an error points at.
    fn shown<'a>(text: &'a str, e: &ScpError) -> &'a str {
        &text[e.span.start.offset..e.span.end.offset]
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
        let e = read_scp(text).unwrap_err();
        assert_eq!(e.kind, ErrorKind::Unsupported);
        assert_eq!(e.message, "unsupported constraint 'multiply'");
        assert_eq!(shown(text, &e), "multiply");
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
                matches!(read_scp(text), Err(e) if e.kind == ErrorKind::Malformed),
                "{text}"
            );
        }
        assert!(matches!(
            read_scp("( (version 1)"),
            Err(e) if e.kind == ErrorKind::Syntax
        ));
    }

    #[test]
    fn unknown_and_reified_keywords_are_unsupported() {
        for op in ["multiply", "not_equals_iff", "lin_not_equals", "wibble"] {
            let text = doc("(x 0 1) (y 0 1)", &format!("(c {op} x y)"), "decide");
            let e = read_scp(&text).unwrap_err();
            assert_eq!(e.kind, ErrorKind::Unsupported, "{op}");
            assert_eq!(shown(&text, &e), op);
        }
    }

    #[test]
    fn errors_point_at_the_text_at_fault() {
        // (variables, constraints, prob_type, the text the error points at)
        let cases = [
            ("(x 0 1)", "(c not_equals x z)", "decide", "z"),
            ("(x 0 a)", "", "decide", "a"),
            ("(x 0 1) (x 0 1)", "", "decide", "x"),
            ("(x 0)", "", "decide", "(x 0)"),
            ("(x 0 1)", "(c not_equals x)", "decide", "(c not_equals x)"),
            (
                "(x 0 1) (y 0 1)",
                "(c not_equals x y) (c equals x y)",
                "decide",
                "c",
            ),
            ("(x 0 1)", "(c lin_equals (1 x 2) 0)", "decide", "(1 x 2)"),
            ("(x 0 1)", "(c lin_equals (1 x) zero)", "decide", "zero"),
            ("(x 0 1)", "", "(minimize nope)", "nope"),
            ("(x 0 1)", "", "wibble", "wibble"),
            (
                "(s 0 3) (d 1 2)",
                "(c cumulative (s) (d) (1) 1)",
                "decide",
                "d",
            ),
            ("(s 0 3)", "(c cumulative (s) (2) (-1) 1)", "decide", "-1"),
            (
                "(s 0 3)",
                "(c cumulative (s) (2 3) (1) 1)",
                "decide",
                "(2 3)",
            ),
            ("(x 0 1)", "(c regular (x) 1 (((0 1))) (0))", "decide", "1"),
            ("(x 0 1)", "(c regular (x) 1 (((0 0))) (2))", "decide", "2"),
        ];
        for (vars, cons, prob, at) in cases {
            let text = doc(vars, cons, prob);
            let e = read_scp(&text).unwrap_err();
            assert_eq!(shown(&text, &e), at, "{text}: {e}");
        }
        let e = read_scp("( (version 2) (variables) (constraints) (prob_type decide) )");
        assert_eq!(
            e.unwrap_err().to_string(),
            "line 1, column 12: unsupported version 2: only version 1 is accepted"
        );
    }

    #[test]
    fn check_reports_every_error_in_order() {
        let text = "( (version 1)
              (variables (x 0 a) (y 0 1))
              (constraints
                  (c1 not_equals x z)
                  (c2 not_equals x y)
                  (c3 wibble x y)
                  (c4 all_different (x y w)))
              (prob_type (minimize nope)) )";
        let errors = check_scp(text);
        let found: Vec<_> = errors
            .iter()
            .map(|e| (e.span.start.line, shown(text, e), e.kind))
            .collect();
        // x's bad bound doesn't make x unknown later on.
        assert_eq!(
            found,
            [
                (2, "a", ErrorKind::Malformed),
                (4, "z", ErrorKind::Malformed),
                (6, "wibble", ErrorKind::Unsupported),
                (7, "w", ErrorKind::Malformed),
                (8, "nope", ErrorKind::Malformed),
            ]
        );
        // read_scp gives the first of them.
        assert_eq!(read_scp(text).unwrap_err(), errors[0]);
    }

    #[test]
    fn check_accepts_what_read_accepts() {
        assert!(check_scp(&doc("(x 0 1) (y 0 1)", "(c not_equals x y)", "enumerate")).is_empty());
        let syntax = check_scp("( (version 1)");
        assert_eq!(syntax.len(), 1);
        assert_eq!(syntax[0].kind, ErrorKind::Syntax);
    }

    #[test]
    fn every_listed_constraint_reads_its_example() {
        for k in CONSTRAINTS {
            let c = format!("(c {} {})", k.keyword, k.example);
            let text = doc("(x 0 3) (y 0 3) (z 0 3)", &c, "enumerate");
            let (model, _) = read_scp(&text).unwrap_or_else(|e| panic!("{c}: {e}"));
            assert_eq!(model.constraint_names(), ["c"], "{c}");
        }
        let mut keywords: Vec<_> = CONSTRAINTS.iter().map(|k| k.keyword).collect();
        keywords.sort();
        keywords.dedup();
        assert_eq!(
            keywords.len(),
            CONSTRAINTS.len(),
            "a keyword is listed twice"
        );
    }

    #[test]
    fn binary_min_and_max() {
        // (x, y) over 0..=2 with r in 0..=1: 8 pairs have their minimum
        // in range, 4 their maximum.
        let v = "(x 0 2) (y 0 2) (r 0 1)";
        assert_eq!(count(&doc(v, "(c min x y r)", "enumerate")), 8);
        assert_eq!(count(&doc(v, "(c max x y r)", "enumerate")), 4);
        // The same as the array forms.
        assert_eq!(count(&doc(v, "(c array_max (x y) r)", "enumerate")), 4);
    }

    #[test]
    fn an_objective_needs_its_own_brackets() {
        let text = doc("(x 0 1)", "", "minimize");
        let e = read_scp(&text).unwrap_err();
        assert_eq!(shown(&text, &e), "minimize");
        assert_eq!(
            e.message,
            "an objective is in its own brackets: (prob_type (minimize var))"
        );
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
