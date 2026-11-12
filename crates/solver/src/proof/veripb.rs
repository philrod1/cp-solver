//! Writes the VeriPB output files OPB and PBP

use std::fmt::Write as _;
use std::fs::{self, File};
use std::io::{self, BufWriter, Write as _};
use std::path::{Path, PathBuf};

use super::opb::{Atoms, Encoding, eq_definition, write_opb};
use super::pb::{Ineq, PbLit, write_lit};
use super::{Conclusion, ProofLogger, Rule};
use crate::lit::Lit;
use crate::model::{Model, VarId};

pub(crate) struct VeriPb {
    enc: Encoding,
    atoms: Vec<Atoms>,
    out: BufWriter<File>,
    line: String,
    error: Option<io::Error>,
}

pub(crate) fn with_extension(stem: &Path, ext: &str) -> PathBuf {
    let mut path = stem.as_os_str().to_owned();
    path.push(".");
    path.push(ext);
    path.into()
}

impl VeriPb {
    pub(crate) fn create(model: &Model, stem: &Path) -> io::Result<Self> {
        let mut enc = Encoding::new(model);
        let opb = write_opb(model, &mut enc).map_err(|name| {
            io::Error::new(
                io::ErrorKind::Unsupported,
                format!("constraint '{name}' has no proof encoding"),
            )
        })?;
        fs::write(with_extension(stem, "opb"), opb)?;
        let mut out = BufWriter::new(File::create(with_extension(stem, "pbp"))?);
        out.write_all(b"pseudo-Boolean proof version 3.0\n")?;
        let atoms = (0..model.num_vars()).map(|_| Atoms::default()).collect();
        let mut proof = VeriPb {
            enc,
            atoms,
            out,
            line: String::new(),
            error: None,
        };
        proof.adopt_opb_atoms();
        Ok(proof)
    }

    /// Take over the atoms the OPB defines. They need no `red` step, but
    /// they do need their pins and links, like any other atom.
    fn adopt_opb_atoms(&mut self) {
        let opb_atoms = std::mem::take(&mut self.enc.atoms);
        for (i, atoms) in opb_atoms.into_iter().enumerate() {
            let x = VarId(i as u32);
            for (v, atom) in atoms.ge {
                self.place_ge(x, v, atom);
            }
            self.atoms[i].eq = atoms.eq;
        }
    }

    fn emit(&mut self) {
        self.line.push('\n');
        if self.error.is_none()
            && let Err(e) = self.out.write_all(self.line.as_bytes())
        {
            self.error = Some(e);
        }
        self.line.clear();
    }

    fn emit_text(&mut self, text: &str) {
        self.line.push_str(text);
        self.emit();
    }

    fn emit_step(&mut self, rule: Rule, ineq: &Ineq) {
        self.line.push_str(match rule {
            Rule::Rup => "rup ",
            Rule::Assert => "a ",
        });
        ineq.write_to(&self.enc.names, &mut self.line);
        self.line.push_str(" ;");
        self.emit();
    }

    fn emit_red(&mut self, label: &str, ineq: &Ineq, atom: PbLit, value: bool) {
        write!(self.line, "@{label} red ").unwrap();
        ineq.write_to(&self.enc.names, &mut self.line);
        self.line.push_str(" : ");
        write_lit(&self.enc.names, atom, &mut self.line);
        self.line
            .push_str(if value { " -> 1 ;" } else { " -> 0 ;" });
        self.emit();
    }

    fn atom(&mut self, lit: Lit) -> PbLit {
        match lit {
            Lit::Ge(x, v) => self.ge(x, v),
            Lit::Lt(x, v) => !self.ge(x, v),
            Lit::Eq(x, v) => self.eq(x, v),
            Lit::Neq(x, v) => !self.eq(x, v),
        }
    }

    // The atom x >= v
    fn ge(&mut self, x: VarId, v: i64) -> PbLit {
        if let Some(&atom) = self.atoms[x.index()].ge.get(&v) {
            return atom;
        }
        let label = self.enc.int(x).label(&format!("ge{v}"));
        let atom = PbLit::pos(self.enc.names.fresh(label.clone()));
        // [r] is true when the atom is false, [f] when it is true.
        let [r, f] = self.enc.int(x).ge_definition(v, atom);
        self.emit_red(&format!("{label}[r]"), &r, atom, false);
        self.emit_red(&format!("{label}[f]"), &f, atom, true);
        self.place_ge(x, v, atom);
        atom
    }

    /// Pin and link a newly defined atom `x ≥ v`, and record it.
    fn place_ge(&mut self, x: VarId, v: i64, atom: PbLit) {
        let int = self.enc.int(x);
        let label = int.label(&format!("ge{v}"));
        let (lb, ub) = (int.label("lb"), int.label("ub"));
        let (lo, hi) = (int.lo, int.hi);

        if v <= lo {
            self.emit_text(&format!("pol @{label}[f] @{lb} + s ;"));
        }
        if v > hi {
            self.emit_text(&format!("pol @{label}[r] @{ub} + s ;"));
        }

        let atoms = &self.atoms[x.index()].ge;
        let below = atoms.range(..v).next_back().map(|(&u, _)| u);
        let above = atoms.range(v + 1..).next().map(|(&w, _)| w);
        if let Some(u) = below {
            let lu = self.enc.int(x).label(&format!("ge{u}"));
            self.emit_text(&format!("pol @{label}[r] @{lu}[f] + s ;"));
        }
        if let Some(w) = above {
            let lw = self.enc.int(x).label(&format!("ge{w}"));
            self.emit_text(&format!("pol @{lw}[r] @{label}[f] + s ;"));
        }
        self.atoms[x.index()].ge.insert(v, atom);
    }

    // The atom x = v
    fn eq(&mut self, x: VarId, v: i64) -> PbLit {
        if let Some(&atom) = self.atoms[x.index()].eq.get(&v) {
            return atom;
        }
        let (ge, gt) = (self.ge(x, v), self.ge(x, v + 1));
        let label = self.enc.int(x).label(&format!("eq{v}"));
        let atom = PbLit::pos(self.enc.names.fresh(label.clone()));
        let [r, f] = eq_definition(ge, gt, atom);
        self.emit_red(&format!("{label}[r]"), &r, atom, false);
        self.emit_red(&format!("{label}[f]"), &f, atom, true);
        self.atoms[x.index()].eq.insert(v, atom);
        atom
    }

    // The clause !r1 || ... || !rn || extra
    fn clause(&mut self, reason: &[Lit], extra: Option<Lit>) -> Ineq {
        let mut lits: Vec<PbLit> = reason.iter().map(|&r| !self.atom(r)).collect();
        if let Some(lit) = extra {
            lits.push(self.atom(lit));
        }
        Ineq::clause(lits)
    }
}

impl ProofLogger for VeriPb {
    fn is_logging(&self) -> bool {
        true
    }

    fn inference(&mut self, lit: Lit, rule: Rule, reason: &[Lit]) {
        let clause = self.clause(reason, Some(lit));
        self.emit_step(rule, &clause);
    }

    fn conflict(&mut self, rule: Rule, reason: &[Lit]) {
        let clause = self.clause(reason, None);
        self.emit_step(rule, &clause);
    }

    fn rup(&mut self, reason: &[Lit], clause: &[PbLit]) {
        let mut lits: Vec<PbLit> = reason.iter().map(|&r| !self.atom(r)).collect();
        lits.extend_from_slice(clause);
        self.emit_step(Rule::Rup, &Ineq::clause(lits));
    }

    fn backtrack(&mut self, decisions: &[Lit]) {
        // With no decisions the conflict is at the root
        // The conclusion writes the empty clause for that
        if !decisions.is_empty() {
            let clause = self.clause(decisions, None);
            self.emit_step(Rule::Rup, &clause);
        }
    }

    fn solution(&mut self, values: &[i64]) {
        let atoms: Vec<PbLit> = values
            .iter()
            .enumerate()
            .map(|(i, &v)| self.atom(Lit::Eq(VarId(i as u32), v)))
            .collect();
        self.line.push_str("solx");
        for atom in atoms {
            self.line.push(' ');
            write_lit(&self.enc.names, atom, &mut self.line);
        }
        self.line.push_str(" ;");
        self.emit();
    }

    fn empty_domain(&mut self, var: VarId) {
        let int = self.enc.int(var);
        let text = format!("pol @{} @{} + ;", int.label("lb"), int.label("ub"));
        self.emit_text(&text);
    }

    fn conclude(&mut self, conclusion: Conclusion) {
        let text = match conclusion {
            Conclusion::Satisfiable => "output NONE ;\nconclusion SAT ;".to_string(),
            Conclusion::Unsatisfiable => {
                "rup >= 1 ;\noutput NONE ;\nconclusion UNSAT : -1 ;".to_string()
            }
            Conclusion::Enumerated(n) => {
                format!("rup >= 1 ;\noutput NONE ;\nconclusion ENUMERATION_COMPLETE {n} : -1 ;")
            }
        };
        self.emit_text(&text);
        self.emit_text("end pseudo-Boolean proof ;");
    }

    fn finish(&mut self) -> io::Result<()> {
        if let Some(e) = self.error.take() {
            return Err(e);
        }
        self.out.flush()
    }
}

#[cfg(test)]
mod tests {
    //! The atom layer on its own: facts about one variable that unit
    //! propagation should see once the atoms are defined, linked and pinned.
    //! Checked with VeriPB if it is on the PATH.

    use std::process::Command;

    use super::*;

    fn veripb_verdict(stem: &Path) -> Option<String> {
        let cmd = std::env::var("VERIPB").unwrap_or_else(|_| "veripb".into());
        let out = Command::new(cmd)
            .arg(with_extension(stem, "opb"))
            .arg(with_extension(stem, "pbp"))
            .output()
            .ok()?;
        let text = String::from_utf8_lossy(&out.stdout).to_string()
            + &String::from_utf8_lossy(&out.stderr);
        Some(
            text.lines()
                .find(|l| l.starts_with("s "))
                .unwrap_or(&text)
                .to_string(),
        )
    }

    #[test]
    fn atoms_behave_like_an_order_encoding() {
        let mut m = Model::new();
        // Wide enough that a bound like Σ ≥ 500 fixes no bits.
        let x = m.int_var_named("x", -300, 1000);
        let y = m.int_var_named("y", -3, 5);
        let stem = std::env::temp_dir().join(format!("cps-atoms-{}", std::process::id()));
        let mut p = VeriPb::create(&m, &stem).unwrap();
        let rup = |p: &mut VeriPb, reason: &[Lit], lit: Lit| p.inference(lit, Rule::Rup, reason);

        // x ≥ 500 ⇒ x ≥ 300, defining atoms above and then below ...
        rup(&mut p, &[Lit::Ge(x, 500)], Lit::Ge(x, 300));
        // ... and one between them.
        rup(&mut p, &[Lit::Ge(x, 400)], Lit::Ge(x, -200));
        // The same facts the other way up: x < 300 ⇒ x < 500.
        rup(&mut p, &[Lit::Lt(x, 300)], Lit::Lt(x, 500));
        // Bounds: x ≥ -300 and x < 1001 always hold, and so do weaker ones.
        rup(&mut p, &[], Lit::Ge(x, -300));
        rup(&mut p, &[], Lit::Lt(x, 1001));
        rup(&mut p, &[], Lit::Ge(x, -700));
        rup(&mut p, &[], Lit::Lt(x, 1020));
        // An equality fixes the bounds, and rules out other values.
        rup(&mut p, &[Lit::Eq(x, 100)], Lit::Lt(x, 400));
        rup(&mut p, &[Lit::Eq(x, 100)], Lit::Ge(x, -200));
        rup(&mut p, &[Lit::Eq(x, 100)], Lit::Neq(x, 450));
        // Bounds and holes pin down a value.
        let reason = [
            Lit::Ge(x, 300),
            Lit::Lt(x, 303),
            Lit::Neq(x, 300),
            Lit::Neq(x, 302),
        ];
        rup(&mut p, &reason, Lit::Eq(x, 301));
        // Some value is taken: the whole domain can't be ruled out. This is
        // the one that needs the pins.
        let all_but_5: Vec<Lit> = (-3..5).map(|v| Lit::Neq(y, v)).collect();
        rup(&mut p, &all_but_5, Lit::Eq(y, 5));

        p.solution(&[301, 5]);
        p.conclude(Conclusion::Satisfiable);
        p.finish().unwrap();
        if let Some(verdict) = veripb_verdict(&stem) {
            assert_eq!(verdict, "s VERIFIED SATISFIABLE");
        }
    }
}
