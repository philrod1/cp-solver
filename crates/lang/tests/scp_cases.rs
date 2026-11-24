//! Run a directory of `.scp` files, such as GCS's curated cases in
//! `verified_encodings/scp_cases`. A file named `*_sat.scp` must have a
//! solution and one named `*_unsat.scp` must not; other files only have to
//! be read and solved without error.
//!
//!     GCS_SCP_CASES=~/code/glasgow-constraint-solver/verified_encodings/scp_cases \
//!         cargo test -p lang --test scp_cases -- --nocapture
//!
//! Each case whose constraints all have proof encodings is also solved
//! with a proof, which must pass VeriPB if it is installed. If CakePB-CP
//! is installed too (`$CAKE_PB_CP`, or `cake_pb_cp` on the PATH), the
//! proof must also pass the verified chain: see [`common::cake_chain`].
//!
//! Without the variable set, the test does nothing.

mod common;

use std::fs;

use common::{Chain, Proof, Run, Tally, cake_chain, keywords, run, run_with_proof};

/// Constraints whose encodings aren't yet CakePB-CP's, so their proofs
/// can't pass its chain.
const NOT_YET_CAKE: &[&str] = &["regular", "cumulative"];

#[test]
fn gcs_scp_cases() {
    let Ok(dir) = std::env::var("GCS_SCP_CASES") else {
        println!("GCS_SCP_CASES not set; skipping");
        return;
    };
    let mut paths: Vec<_> = fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("can't read {dir}: {e}"))
        .filter_map(|entry| entry.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|ext| ext == "scp"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "no .scp files in {dir}");

    let proof_dir = std::path::PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("scp_case_proofs");
    std::fs::create_dir_all(&proof_dir).unwrap();
    let mut verified = Vec::new();
    let mut cake_verified = Vec::new();
    let mut not_yet_cake = Vec::new();
    let mut tally = Tally::default();
    for path in &paths {
        let name = path.file_stem().unwrap().to_string_lossy().to_string();
        let text = fs::read_to_string(path).unwrap();
        match run(&text) {
            Err(e) => tally.failures.push(format!("{name}: {e}")),
            Ok(Run::Unsupported(op)) => *tally.unsupported.entry(op).or_default() += 1,
            Ok(outcome @ (Run::Solutions(_) | Run::Optimum(_))) => {
                let wrong = match outcome {
                    Run::Solutions(n) => {
                        (name.ends_with("_sat") && n == 0) || (name.ends_with("_unsat") && n > 0)
                    }
                    // An `_opt` case has a best solution.
                    Run::Optimum(best) => name.ends_with("_opt") && best.is_none(),
                    Run::Unsupported(_) => unreachable!(),
                };
                if wrong {
                    tally.failures.push(format!("{name}: wrong result"));
                } else {
                    tally.passed += 1;
                }
                match run_with_proof(&text, &proof_dir.join(&name)) {
                    Ok(Proof::Verified(verdict)) => {
                        let used = keywords(&text);
                        if used.iter().any(|k| NOT_YET_CAKE.contains(&k.as_str())) {
                            not_yet_cake.push(name.clone());
                        } else {
                            // CakePB-CP bounds the objective as written;
                            // VeriPB, on cps's OPB, the one it minimises,
                            // negated for a maximisation.
                            let expected = match outcome {
                                Run::Optimum(Some(best)) => {
                                    format!("s VERIFIED BOUNDS {best} <= OBJ <= {best}")
                                }
                                _ => verdict.clone(),
                            };
                            match cake_chain(path, &proof_dir.join(&name)) {
                                Ok(Chain::Verified(cake))
                                    if cake.eq_ignore_ascii_case(&expected) =>
                                {
                                    cake_verified.push(format!("{name}: {cake}"));
                                }
                                Ok(Chain::Verified(cake)) => tally.failures.push(format!(
                                    "{name}: CakePB-CP says '{cake}', expected '{expected}'"
                                )),
                                Ok(Chain::NotChecked) => {}
                                Err(e) => tally.failures.push(format!("{name}: {e}")),
                            }
                        }
                        verified.push(format!("{name}: {verdict}"));
                    }
                    Ok(Proof::NotWritten | Proof::NotChecked) => {}
                    Err(e) => tally.failures.push(format!("{name}: {e}")),
                }
            }
        }
    }
    tally.report(&format!("scp cases in {dir}"));
    println!("   {} proofs checked by VeriPB:", verified.len());
    for v in &verified {
        println!("     {v}");
    }
    if !cake_verified.is_empty() {
        println!(
            "   {} proofs through the CakePB-CP chain:",
            cake_verified.len()
        );
        for v in &cake_verified {
            println!("     {v}");
        }
        println!(
            "   not yet CakePB-CP's encoding: {}",
            not_yet_cake.join(" ")
        );
    }
    assert!(
        tally.failures.is_empty(),
        "{} failures",
        tally.failures.len()
    );
}
