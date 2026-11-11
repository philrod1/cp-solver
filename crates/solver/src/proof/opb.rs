use std::collections::{BTreeMap, HashMap};
use std::fmt::Write;

use super::pb::{ Ineq, Names, PbLit };
use crate::model::{ Model, VarId };

#[derive(Debug)]
pub(crate) struct IntBits {
    pub(crate) name: String,
    pub(crate) bits: Vec<(i128, PbLit)>,
    pub(crate) hi: i64,
    pub(crate) lo: i64,
}

impl IntBits {
    fn new(names: &mut Names, name: String, lo: i64, hi: i64) -> Self {
        let (mag_bits, signed) = bit_widths(lo, hi);
        let mut bits = Vec::new();
        if signed {
            let sign = names.fresh(format!("i[{name}][sign]"));
            bits.push((-(1i128 << mag_bits), PbLit::pos(sign)));
        }
        for b in 0..mag_bits {
            let bit = names.fresh(format!("i[{name}][b{b}]"));
            bits.push(((1i128 << b), PbLit::pos(bit)));
        }
        IntBits{ name, bits, lo, hi }
    }

    pub(crate) fn scaled(&self, coeff: i128) -> impl Iterator<Item = (i128, PbLit)> + '_ {
        self.bits.iter().map(move |&(c, l)| (coeff * c, l))
    }

    pub(crate) fn label(&self, what: &str) -> String {
        format!("i[{}][{what}]", self.name)
    }

    /// The definition of the atom `x >= v`, as two halves:
    /// `[r]` atom => sum >= v, and `[f]` !atom => sum <= v - 1.
    pub(crate) fn ge_definition(&self, v: i64, atom: PbLit) -> [Ineq; 2] {
        let sum: Vec<_> = self.scaled(1).collect();
        let v = i128::from(v);
        [Ineq::ge(sum.clone(), v).implied_by(atom), Ineq::le(sum, v - 1).implied_by(!atom)]
    }
}

/// The definition of the atom `x = v`
/// from `ge` (x >= v) and `gt` (x >= v + 1), as two halves:
/// `[r]` atom => ge && !gt, and `[f]` ge && !gt => atom.
pub(crate) fn eq_definition(ge: PbLit, gt: PbLit, atom: PbLit) -> [Ineq; 2] {
    [Ineq::ge(vec![(1, ge), (1, !gt)], 2).implied_by(atom), Ineq::clause([atom, !ge, gt])]
}

/// How many magnitude bits a domain needs, and whether it needs a sign bit
pub(crate) fn bit_widths(lo: i64, hi: i64) -> (u32, bool) {
    // An empty domain (lo > hi) still needs bits for the bound rows that  contradict each other.
    let hi = hi.max(lo);
    let largest = if lo < 0 { (lo.unsigned_abs() - 1).max(hi.max(0) as u64) } else { hi as u64 };
    (u64::BITS - largest.leading_zeros(), lo < 0)
}

#[derive(Debug, Default)]
pub(crate) struct Atoms {
    pub(crate) ge: BTreeMap<i64, PbLit>,
    pub(crate) eq: HashMap<i64, PbLit>,
}

#[derive(Debug)]
pub(crate) struct Encoding {
    pub(crate) names: Names,
    pub(crate) ints: Vec<IntBits>,
    pub(crate) atoms: Vec<Atoms>,
}

impl Encoding {
    pub(crate) fn new(model: &Model) -> Self {
        let mut names = Names::default();
        let ints = (0..model.num_vars())
            .map(|i| {
                let var = VarId(i as u32);
                let (lo, hi) = model.domains[i];
                IntBits::new(&mut names, model.var_name(var), lo, hi)
            })
            .collect();
        let atoms = (0..model.num_vars()).map(|_| Atoms::default()).collect();
        Encoding { names, ints, atoms }
    }

    pub(crate) fn int(&self, var: VarId) -> &IntBits {
        &self.ints[var.index()]
    }
}

#[derive(Debug)]
pub struct NotEncodable;

pub struct OpbEncoder<'a> {
    enc: &'a mut Encoding,
    out: &'a mut String,
    constraint_name: &'a str,
}

impl OpbEncoder<'_> {
    pub(crate) fn flag(&mut self, role: &str) -> PbLit {
        PbLit::pos(self.enc.names.fresh(format!("b[{}][{role}]", self.constraint_name)))
    }

    pub(crate) fn linear(&self, terms: &[(i64, VarId)]) -> Vec<(i128, PbLit)> {
        terms.iter().flat_map(|&(a, x)| self.enc.int(x).scaled(a.into())).collect()
    }

    pub(crate) fn row(&mut self, role: &str, ineq: &Ineq) {
        write!(self.out, "@c[{}][{role}] ", self.constraint_name).unwrap();
        ineq.write_to(&self.enc.names, self.out);
        self.out.push_str(" ;\n");
    }

    /// A fresh flag numbered by `index`, e.g. `x[name][0_2]`.
    pub(crate) fn indexed_flag(&mut self, index: &[usize]) -> PbLit {
        let index: Vec<String> = index.iter().map(|i| i.to_string()).collect();
        PbLit::pos(self.enc.names.fresh(format!("x[{}][{}]", self.constraint_name, index.join("_"))))
    }
}

pub(crate) fn write_opb(model: &Model, enc: &mut Encoding) -> Result<String, String> {
    let mut out = String::from("* written by cps\n");
    out.push_str("preserved:");
    for int in &enc.ints {
        for &(_, bit) in &int.bits {
            out.push(' ');
            super::pb::write_lit(&enc.names, bit, &mut out);
        }
    }
    out.push_str(" ;\n");
    for int in &enc.ints {
        let sum: Vec<_> = int.scaled(1).collect();
        write!(out, "@{} ", int.label("lb")).unwrap();
        Ineq::ge(sum.clone(), int.lo.into()).write_to(&enc.names, &mut out);
        write!(out, " ;\n@{} ", int.label("ub")).unwrap();
        Ineq::le(sum, int.hi.into()).write_to(&enc.names, &mut out);
        out.push_str(" ;\n");
    }
    for (constraint, name) in model.constraints().iter().zip(model.constraint_names()) {
        let mut opb = OpbEncoder { enc: &mut *enc, out: &mut out, constraint_name: name };
        constraint.encode(&mut opb).map_err(|NotEncodable| name.clone())?;
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn widths_match_gcs() {
        assert_eq!(bit_widths(0, 0), (0, false)); // no bits: the value is 0
        assert_eq!(bit_widths(1, 1), (1, false));
        assert_eq!(bit_widths(0, 3), (2, false));
        assert_eq!(bit_widths(0, 4), (3, false));
        assert_eq!(bit_widths(-1, 0), (0, true)); // just the sign bit, worth -1
        assert_eq!(bit_widths(-2, 1), (1, true)); // -2·s + b0
        assert_eq!(bit_widths(-3, 1), (2, true)); // -4·s + b0 + 2·b1
        assert_eq!(bit_widths(-5, -2), (3, true)); // -8·s + ..., to reach -5
    }

    #[test]
    fn every_value_in_the_domain_is_reachable() {
        for lo in -9..=9 {
            for hi in lo..=9 {
                let (n, signed) = bit_widths(lo, hi);
                let min = if signed { -(1i64 << n) } else { 0 };
                let max = (1i64 << n) - 1;
                assert!(min <= lo && hi <= max, "{lo}..={hi} with {n} bits, signed {signed}");
            }
        }
    }

    #[test]
    fn variables_become_bits_and_bound_rows() {
        let mut m = Model::new();
        m.int_var_named("x", -2, 1);
        m.int_var_named("y", 0, 0);
        let mut enc = Encoding::new(&m);
        let opb = write_opb(&m, &mut enc).unwrap();
        assert_eq!(
            opb,
            "* written by cps\n\
             preserved: i[x][sign] i[x][b0] ;\n\
             @i[x][lb] -2 i[x][sign] 1 i[x][b0] >= -2 ;\n\
             @i[x][ub] 2 i[x][sign] -1 i[x][b0] >= -1 ;\n\
             @i[y][lb] >= 0 ;\n\
             @i[y][ub] >= 0 ;\n"
        );
    }
}
