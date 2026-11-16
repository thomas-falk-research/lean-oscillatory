//! The command line: verdict on standard output, exit codes 0, 1, 2, 3.

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

const BIN: &str = env!("CARGO_BIN_EXE_oscint-cert");

const STATEMENTS: &str = r#"{
  "format": "oscint-statements 1",
  "statements": [
    {"name": "OscInt.Statements.LatticeSchrodingerDispersiveStatement", "label": "LS-D",
     "proved_by": "OscInt.API.latticeSchrodingerDispersive",
     "commitment": "c7b1f69b1f2313318626f3e728eb6554636424a47f551286041ba8eb297b16ef"},
    {"name": "OscInt.Statements.LatticeSchrodingerKernelStatement", "label": "LS-K",
     "proved_by": null,
     "commitment": "50d7897f580873dbcb4d0f12300bdbf599aec479b485825991431f5bb33b620a"}
  ]
}"#;

fn scratch(name: &str, content: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"));
    std::fs::create_dir_all(&dir).expect("scratch directory");
    let path = dir.join(name);
    std::fs::write(&path, content).expect("scratch file");
    path
}

/// Runs the binary; returns (exit code, stdout, stderr).
fn run(args: &[&str], stdin: Option<&str>) -> (i32, String, String) {
    let mut child = Command::new(BIN)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn");
    if let Some(text) = stdin {
        child
            .stdin
            .take()
            .expect("stdin")
            .write_all(text.as_bytes())
            .expect("write");
    } else {
        drop(child.stdin.take());
    }
    let out = child.wait_with_output().expect("wait");
    (
        out.status.code().expect("exit code"),
        String::from_utf8(out.stdout).expect("utf-8"),
        String::from_utf8(out.stderr).expect("utf-8"),
    )
}

fn verdict(stdout: &str) -> serde_json::Value {
    serde_json::from_str(stdout).expect("the verdict is JSON")
}

#[test]
fn make_check_and_exit_codes() {
    let list = scratch("cli-statements.json", STATEMENTS);
    let list = list.to_str().expect("path");

    // make, then check: CERTIFIED, exit 0
    let (code, cert, err) = run(
        &[
            "make",
            "lattice-envelope",
            "--inputs",
            r#"{"d": 2, "t": "25"}"#,
            "--statements",
            list,
        ],
        None,
    );
    assert_eq!(code, 0, "{err}");
    let cert_path = scratch("cli-envelope.json", &cert);
    let cert_path = cert_path.to_str().expect("path");
    let (code, out, _) = run(&["check", cert_path, "--statements", list], None);
    assert_eq!(code, 0, "{out}");
    assert_eq!(verdict(&out)["status"], "CERTIFIED");
    // the option may come first, and the certificate may come from standard input
    let (code, out, _) = run(&["check", "--statements", list, "-"], Some(&cert));
    assert_eq!(code, 0, "{out}");
    assert_eq!(verdict(&out)["status"], "CERTIFIED");

    // REJECTED, exit 1
    let bad = cert.replace("\"25\"", "\"0\"");
    assert_ne!(bad, cert);
    let (code, out, _) = run(&["check", "-", "--statements", list], Some(&bad));
    assert_eq!(code, 1, "{out}");
    assert_eq!(verdict(&out)["status"], "REJECTED");
    let (code, out, _) = run(&["check", "-", "--statements", list], Some("this is not JSON"));
    assert_eq!(code, 1);
    assert_eq!(verdict(&out)["status"], "REJECTED");
    let (code, out, _) = run(&["check", "-", "--statements", list], Some(""));
    assert_eq!(code, 1);
    assert_eq!(verdict(&out)["status"], "REJECTED");

    // UNRESOLVED, exit 2: out of range, and a statement without proof
    let far = cert.replace("\"d\": 2", "\"d\": 65");
    assert_ne!(far, cert);
    let (code, out, _) = run(&["check", "-", "--statements", list], Some(&far));
    assert_eq!(code, 2, "{out}");
    assert_eq!(verdict(&out)["status"], "UNRESOLVED");
    let (code, pop, err) = run(
        &[
            "make",
            "lattice-population",
            "--inputs",
            r#"{"n": 1, "t": "3/2"}"#,
            "--statements",
            list,
        ],
        None,
    );
    assert_eq!(code, 0, "{err}");
    let (code, out, _) = run(&["check", "-", "--statements", list], Some(&pop));
    assert_eq!(code, 2, "{out}");
    assert_eq!(verdict(&out)["status"], "UNRESOLVED");
    assert!(verdict(&out)["statement"]["proved_by"].is_null());

    // usage and input errors, exit 3, nothing on standard output
    let missing = scratch("cli-missing-parent.json", "");
    let missing = format!("{}.absent", missing.to_str().expect("path"));
    let not_a_list = scratch("cli-not-a-list.json", "{\"format\": \"something else\"}");
    let not_a_list = not_a_list.to_str().expect("path");
    let cases: Vec<Vec<&str>> = vec![
        vec![],
        vec!["check"],
        vec!["check", cert_path],
        vec!["check", cert_path, "--statements"],
        vec!["check", cert_path, "--statements", &missing],
        vec!["check", cert_path, "--statements", not_a_list],
        vec!["check", &missing, "--statements", list],
        vec!["check", cert_path, cert_path, "--statements", list],
        vec!["check", cert_path, "--statements", list, "--verbose"],
        vec!["check", cert_path, "--statements", list, "--statements", list],
        vec!["verify", cert_path, "--statements", list],
        vec!["make", "lattice-envelope", "--statements", list],
        vec![
            "make",
            "lattice-envelope",
            "--inputs",
            r#"{"d": 2, "t": "0"}"#,
            "--statements",
            list,
        ],
        vec!["make", "lattice-envelope", "--inputs", "{", "--statements", list],
        vec!["make", "no-such-kind", "--inputs", "{}", "--statements", list],
        vec![
            "make",
            "bessel-j",
            "--inputs",
            r#"{"n": 0, "x": "1"}"#,
            "--statements",
            list,
            "--claim-bits",
            "5000",
        ],
    ];
    for args in cases {
        let (code, out, err) = run(&args, None);
        assert_eq!(code, 3, "{args:?}");
        assert!(out.is_empty(), "{args:?} wrote {out}");
        assert!(!err.is_empty(), "{args:?} was silent");
    }
}
