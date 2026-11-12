//! Run a directory of `.scp` files, such as GCS's curated cases in
//! `verified_encodings/scp_cases`. A file named `*_sat.scp` must have a
//! solution and one named `*_unsat.scp` must not; other files only have to
//! be read and solved without error.
//!
//!     GCS_SCP_CASES=~/code/glasgow-constraint-solver/verified_encodings/scp_cases \
//!         cargo test -p lang --test scp_cases -- --nocapture
//!
//! Without the variable set, the test does nothing.

mod common;

use std::fs;

use common::{Run, Tally, run};

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

    let mut tally = Tally::default();
    for path in &paths {
        let name = path.file_stem().unwrap().to_string_lossy().to_string();
        let text = fs::read_to_string(path).unwrap();
        match run(&text) {
            Err(e) => tally.failures.push(format!("{name}: {e}")),
            Ok(Run::Unsupported(op)) => *tally.unsupported.entry(op).or_default() += 1,
            Ok(Run::Optimisation) => tally.optimisation += 1,
            Ok(Run::Solutions(n)) => {
                let wrong =
                    (name.ends_with("_sat") && n == 0) || (name.ends_with("_unsat") && n > 0);
                if wrong {
                    tally.failures.push(format!("{name}: found {n} solutions"));
                } else {
                    tally.passed += 1;
                }
            }
        }
    }
    tally.report(&format!("scp cases in {dir}"));
    assert!(
        tally.failures.is_empty(),
        "{} failures",
        tally.failures.len()
    );
}
