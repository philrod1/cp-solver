//! Pseudo-Boolean vocabulary shared by the OPB model and the proof:
//! Boolean variables with names, literals, and inequalities.

use std::collections::HashMap;
use std::fmt::Write;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct PbVar(u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct PbLit {
    var: PbVar,
    negated: bool,
}

impl PbLit {
    pub(crate) fn pos(var: PbVar) -> Self {
        PbLit { var, negated: false }
    }

    pub(crate) fn var(self) -> PbVar {
        self.var
    }
}

impl std::ops::Not for PbLit {
    type Output = PbLit;
    fn not(self) -> PbLit {
        PbLit { var: self.var, negated: !self.negated }
    }
}

#[derive(Debug, Default)]
pub(crate) struct Names {
    names: Vec<String>,
}

impl Names {
    pub(crate) fn fresh(&mut self, name: String) -> PbVar {
        let var = PbVar(self.names.len() as u32);
        self.names.push(name);
        var
    }

    pub(crate) fn name(&self, var: PbVar) -> &str {
        &self.names[var.0 as usize]
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Ineq {
    pub(crate) terms: Vec<(i128, PbLit)>,
    pub(crate) rhs: i128,
}

impl Ineq {
    pub(crate) fn ge(terms: Vec<(i128, PbLit)>, rhs: i128) -> Self {
        Ineq { terms, rhs }
    }

    pub(crate) fn le(terms: Vec<(i128, PbLit)>, rhs: i128) -> Self {
        let terms = terms.into_iter().map(|(c, l)| (-c, l)).collect();
        Ineq { terms, rhs: -rhs }
    }

    pub(crate) fn clause(lits: impl IntoIterator<Item = PbLit>) -> Self {
        Ineq { terms: lits.into_iter().map(|l| (1, l)).collect(), rhs: 1 }
    }

    fn min_lhs(&self) -> i128 {
        self.terms.iter().map(|&(c, _)| c.min(0)).sum()
    }

    pub(crate) fn implied_by(mut self, flag:PbLit) -> Self {
        let m = (self.rhs - self.min_lhs()).max(0);
        if m > 0 {
            self.terms.push((m, !flag));
        }
        self
    }

    pub(crate) fn merged(&self) -> Ineq {
        // Net coefficient on the literal
        let mut order: Vec<PbVar> = Vec::new();
        let mut coeff: HashMap<PbVar, (i128, bool)> = Default::default();
        let mut constant = 0i128;
        for &(c, lit) in &self.terms {
            let entry = coeff.entry(lit.var).or_insert_with(|| {
                order.push(lit.var);
                (0, lit.negated)
            });
            if lit.negated {
                entry.0 -= c;
                constant += c;
            } else {
                entry.0 += c;
            }
        }
        let mut terms = Vec::with_capacity(order.len());
        for var in order {
            let (a, first_negated) = coeff[&var];
            if a == 0 {
                continue;
            }
            if first_negated {
                terms.push((-a, !PbLit::pos(var)));
                constant += a;
            } else {
                terms.push((a, PbLit::pos(var)));
            }
        }
        Ineq { terms, rhs: self.rhs - constant }
    }

    pub(crate) fn negated(&self) -> Ineq {
        Ineq::le(self.terms.clone(), self.rhs -1)
    }

    /// Append in OPB syntax, without the final `;`
    /// E.g. `2 x 1 ~y >= 1`
    pub(crate) fn write_to(&self, names: &Names, out: &mut String) {
        let merged = self.merged();
        for &(c, lit) in &merged.terms {
            let tilde = if lit.negated { "~" } else { "" };
            write!(out, "{c} {tilde}{} ", names.name(lit.var)).unwrap();
        }
        write!(out, ">= {}", merged.rhs).unwrap();
    }
}

pub(crate) fn write_lit(names: &Names, lit: PbLit, out: &mut String) {
    if lit.negated {
        out.push('~');
    }
    out.push_str(names.name(lit.var));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn text(names: &Names, ineq: &Ineq) -> String {
        let mut s = String::new();
        ineq.write_to(names, &mut s);
        s
    }

    #[test]
    fn writes_opb_syntax() {
        let mut n = Names::default();
        let (x, y) = (PbLit::pos(n.fresh("x".into())), PbLit::pos(n.fresh("y".into())));
        assert_eq!(text(&n, &Ineq::ge(vec![(2, x), (-1, !y)], 1)), "2 x -1 ~y >= 1");
        assert_eq!(text(&n, &Ineq::le(vec![(2, x), (3, y)], 4)), "-2 x -3 y >= -4");
        assert_eq!(text(&n, &Ineq::clause([x, !y])), "1 x 1 ~y >= 1");
    }

    #[test]
    fn implied_by_adds_just_enough() {
        let mut n = Names::default();
        let (x, y, f) = (
            PbLit::pos(n.fresh("x".into())),
            PbLit::pos(n.fresh("y".into())),
            PbLit::pos(n.fresh("f".into())),
        );
        // f => x - y >= 1: with f false the left side can be as low as -1,
        // so it needs 1 - (-1) = 2 more.
        let ineq = Ineq::ge(vec![(1, x), (-1, y)], 1).implied_by(f);
        assert_eq!(text(&n, &ineq), "1 x -1 y 2 ~f >= 1");
        // Already true whatever x is: nothing to add.
        assert_eq!(Ineq::ge(vec![(1, x)], 0).implied_by(f).terms.len(), 1);
    }

    #[test]
    fn merging_cancels_and_combines() {
        let mut n = Names::default();
        let (x, y) = (PbLit::pos(n.fresh("x".into())), PbLit::pos(n.fresh("y".into())));
        // x - x + 2y >= 1  ->  2y >= 1
        assert_eq!(text(&n, &Ineq::ge(vec![(1, x), (-1, x), (2, y)], 1)), "2 y >= 1");
        // x + ~x >= 1  ->  0 >= 0 (always true)
        assert_eq!(text(&n, &Ineq::ge(vec![(1, x), (1, !x)], 1)), ">= 0");
        // 2~x + x >= 2  ->  ~x >= 1 (2~x + 1 - ~x >= 2)
        assert_eq!(text(&n, &Ineq::ge(vec![(2, !x), (1, x)], 2)), "1 ~x >= 1");
    }

    #[test]
    fn merging_preserves_meaning() {
        // Check every assignment of three variables against a few
        // inequalities with repeats and mixed polarity.
        let mut n = Names::default();
        let v: Vec<PbLit> = (0..3).map(|i| PbLit::pos(n.fresh(format!("v{i}")))).collect();
        let cases = [
            Ineq::ge(vec![(3, v[0]), (-2, !v[0]), (1, v[1]), (4, !v[2]), (-1, v[2])], 2),
            Ineq::ge(vec![(1, !v[1]), (1, v[1]), (-5, v[2]), (2, !v[0])], -3),
            Ineq::ge(vec![(-1, !v[0]), (-1, !v[0]), (7, v[0])], 0),
        ];
        let value = |ineq: &Ineq, a: [bool; 3]| -> bool {
            let lhs: i128 = ineq
                .terms
                .iter()
                .map(|&(c, l)| if a[l.var.0 as usize] != l.negated { c } else { 0 })
                .sum();
            lhs >= ineq.rhs
        };
        for ineq in &cases {
            for bits in 0..8 {
                let a = [bits & 1 != 0, bits & 2 != 0, bits & 4 != 0];
                assert_eq!(value(ineq, a), value(&ineq.merged(), a), "{ineq:?} at {a:?}");
            }
        }
    }

    #[test]
    fn not_flips_the_literal() {
        let mut n = Names::default();
        let x = PbLit::pos(n.fresh("x".into()));
        assert_ne!(!x, x);
        assert_eq!(!!x, x);
    }
}
