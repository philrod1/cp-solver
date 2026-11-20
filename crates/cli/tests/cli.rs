//! The `cps` command, run as a program: its output and exit status.

use std::io::Write;
use std::process::{Command, Output, Stdio};

/// Run `cps` with `args`, feeding `stdin` to it.
fn cps(args: &[&str], stdin: &str) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_cps"))
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("cps runs");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(stdin.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

fn stdout(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn stderr(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

const GOOD: &str = "( (version 1)
  (variables (x 0 2) (y 0 2))
  (constraints (c1 not_equals x y))
  (prob_type enumerate) )";

/// Three problems: an unknown variable, an odd coefficient list, and an
/// unsupported keyword.
const BROKEN: &str = "( (version 1)
  (variables (x 0 3) (y 0 3))
  (constraints
    (c1 not_equals x z)
    (c2 lin_equals (1 x 1) 3)
    (c3 multiply x y x))
  (prob_type enumerate) )";

#[test]
fn help() {
    let o = cps(&["--help"], "");
    assert!(o.status.success());
    assert!(stdout(&o).starts_with("usage: cps"));
}

#[test]
fn a_clean_model_checks_silently() {
    let o = cps(&["--check", "-"], GOOD);
    assert_eq!(o.status.code(), Some(0));
    assert_eq!((stdout(&o), stderr(&o)), (String::new(), String::new()));
    let o = cps(&["--check", "--json", "-"], GOOD);
    assert_eq!(o.status.code(), Some(0));
    assert_eq!(stdout(&o), "[]\n");
}

#[test]
fn check_reports_every_problem() {
    let o = cps(&["--check", "-"], BROKEN);
    assert_eq!(o.status.code(), Some(1));
    assert_eq!(
        stderr(&o),
        "<stdin>:4:22: error: unknown variable 'z'\n\
         <stdin>:5:20: error: 'lin_equals' needs coefficient/variable pairs\n\
         <stdin>:6:9: unsupported: unsupported constraint 'multiply'\n"
    );
    assert_eq!(stdout(&o), "");
}

#[test]
fn check_as_json() {
    let o = cps(&["--check", "--json", "-"], BROKEN);
    assert_eq!(o.status.code(), Some(1));
    let expected = concat!(
        r#"[{"kind":"malformed","message":"unknown variable 'z'","#,
        r#""start":{"offset":80,"line":4,"column":22},"end":{"offset":81,"line":4,"column":23}},"#,
        r#"{"kind":"malformed","message":"'lin_equals' needs coefficient/variable pairs","#,
        r#""start":{"offset":102,"line":5,"column":20},"end":{"offset":109,"line":5,"column":27}},"#,
        r#"{"kind":"unsupported","message":"unsupported constraint 'multiply'","#,
        r#""start":{"offset":121,"line":6,"column":9},"end":{"offset":129,"line":6,"column":17}}]"#,
        "\n"
    );
    assert_eq!(stdout(&o), expected);
    // The offsets mark the text at fault.
    assert_eq!(&BROKEN[80..81], "z");
    assert_eq!(&BROKEN[102..109], "(1 x 1)");
    assert_eq!(&BROKEN[121..129], "multiply");
}

#[test]
fn json_strings_are_escaped() {
    let model = r#"( (version 1) (variables (x 0 1)) (constraints (c not_equals x a"b\c)) (prob_type decide) )"#;
    let o = cps(&["--check", "--json", "-"], model);
    assert!(
        stdout(&o).contains(r#""message":"unknown variable 'a\"b\\c'""#),
        "{}",
        stdout(&o)
    );
}

#[test]
fn a_syntax_error_says_where() {
    let o = cps(&["--check", "-"], "( (version 1)\n  (variables (x 0 1)");
    assert_eq!(o.status.code(), Some(1));
    assert_eq!(stderr(&o), "<stdin>:2:3: error: unclosed '('\n");
}

#[test]
fn solving_a_broken_model_reports_every_problem() {
    let o = cps(&["-"], BROKEN);
    assert_eq!(o.status.code(), Some(1));
    assert_eq!(stderr(&o).lines().count(), 3);
    assert_eq!(stdout(&o), "");
}

#[test]
fn solving_still_works() {
    let o = cps(&["-"], GOOD);
    assert_eq!(o.status.code(), Some(0));
    assert!(stdout(&o).ends_with("6 solutions\n"), "{}", stdout(&o));
}

#[test]
fn optimisation_prints_each_improvement_then_the_optimum() {
    let model = "( (version 1) (variables (X 0 3) (Y 0 3))
      (constraints (_1 lin_equals (1 X 1 Y) 3)) (prob_type (minimize Y)) )";
    let o = cps(&["-"], model);
    assert_eq!(o.status.code(), Some(0));
    let out = stdout(&o);
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines.last(), Some(&"OPTIMUM 0"), "{out}");
    assert_eq!(lines[lines.len() - 2], "X=3 Y=0", "{out}");
}

#[test]
fn optimisation_without_solutions() {
    let model = "( (version 1) (variables (X 0 1) (Y 0 1))
      (constraints (_1 lin_equals (1 X 1 Y) 5)) (prob_type (maximize X)) )";
    let o = cps(&["-"], model);
    assert_eq!(o.status.code(), Some(0));
    assert_eq!(stdout(&o), "UNSATISFIABLE\n");
}

#[test]
fn files_are_named_in_reports() {
    let path = std::env::temp_dir().join(format!("cps-cli-{}.scp", std::process::id()));
    std::fs::write(&path, BROKEN).unwrap();
    let o = cps(&["--check", path.to_str().unwrap()], "");
    std::fs::remove_file(&path).unwrap();
    let first = stderr(&o).lines().next().unwrap_or_default().to_string();
    assert_eq!(
        first,
        format!("{}:4:22: error: unknown variable 'z'", path.display())
    );
}

#[test]
fn constraint_kinds_for_people() {
    let o = cps(&["--constraints"], "");
    assert_eq!(o.status.code(), Some(0));
    let out = stdout(&o);
    assert!(
        out.starts_with("(label not_equals x y)\n    x ≠ y\n"),
        "{out}"
    );
    assert_eq!(out.lines().count(), 2 * lang::CONSTRAINTS.len());
}

#[test]
fn constraint_kinds_as_json() {
    let o = cps(&["--constraints", "--json"], "");
    assert_eq!(o.status.code(), Some(0));
    let out = stdout(&o);
    assert!(
        out.starts_with(
            r#"[{"keyword":"not_equals","arguments":["x","y"],"summary":"x ≠ y","example":"x y"},"#
        ),
        "{out}"
    );
    assert!(out.ends_with("}]\n"));
    for k in lang::CONSTRAINTS {
        assert!(out.contains(&format!(r#""keyword":"{}""#, k.keyword)));
    }
    assert!(
        out.contains(r#""arguments":["(start ...)","(length ...)","(height ...)","capacity"]"#)
    );
}

#[test]
fn every_listed_kind_passes_check() {
    // What a completion would insert: the keyword and its example.
    for k in lang::CONSTRAINTS {
        let model = format!(
            "( (version 1) (variables (x 0 3) (y 0 3) (z 0 3)) \
             (constraints (c {} {})) (prob_type enumerate) )",
            k.keyword, k.example
        );
        let o = cps(&["--check", "-"], &model);
        assert_eq!(o.status.code(), Some(0), "{}: {}", k.keyword, stderr(&o));
    }
}

#[test]
fn usage_problems_exit_with_2() {
    for args in [
        &[][..],
        &["--json", "-"],
        &["--check", "--proof", "p", "-"],
        &["--wibble", "-"],
        &["--check", "/no/such/file.scp"],
        &["--constraints", "-"],
        &["--constraints", "--check", "-"],
        &["--constraints", "--proof", "p"],
    ] {
        let o = cps(args, GOOD);
        assert_eq!(o.status.code(), Some(2), "{args:?}: {}", stderr(&o));
        assert!(stderr(&o).starts_with("cps: "), "{args:?}");
    }
}
