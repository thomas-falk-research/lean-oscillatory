// SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
//
// SPDX-License-Identifier: Apache-2.0

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

// ---------------------------------------------------------------------------
// Revision 3 of the contract
// ---------------------------------------------------------------------------

/// The statement list as it was shipped with revision 3 of the contract
/// (a copy; `sha256sum` gives the digest below).
const SHIPPED: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/statements.json");
const SHIPPED_SHA256: &str = "e9f392c8200f6f8e9bc232f97c8a07f3f94abb10ef7e4a662b1a17d7dfaead42";

fn scratch_bytes(name: &str, content: &[u8]) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"));
    std::fs::create_dir_all(&dir).expect("scratch directory");
    let path = dir.join(name);
    std::fs::write(&path, content).expect("scratch file");
    path
}

/// Runs the binary with bytes on standard input; returns (exit code, stdout, stderr).
fn run_bytes(args: &[&str], stdin: &[u8]) -> (i32, String, String) {
    let mut child = Command::new(BIN)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn");
    // a command that fails before it reads standard input closes the pipe
    match child.stdin.take().expect("stdin").write_all(stdin) {
        Ok(()) => {}
        Err(e) if e.kind() == std::io::ErrorKind::BrokenPipe => {}
        Err(e) => panic!("write: {e}"),
    }
    let out = child.wait_with_output().expect("wait");
    (
        out.status.code().expect("exit code"),
        String::from_utf8(out.stdout).expect("utf-8"),
        String::from_utf8(out.stderr).expect("utf-8"),
    )
}

/// Exit code 3: a message on standard error and nothing on standard output.
fn assert_error(args: &[&str], stdin: Option<&str>) -> String {
    let (code, out, err) = run_bytes(args, stdin.unwrap_or("").as_bytes());
    assert_eq!(code, 3, "{args:?}: {out}");
    assert!(out.is_empty(), "{args:?} wrote {out}");
    assert!(!err.trim().is_empty(), "{args:?} was silent");
    err
}

const VERDICT_KEYS: [&str; 13] = [
    "assumptions",
    "certificate_sha256",
    "checker",
    "format",
    "hypothesis",
    "kind",
    "numeric_rung",
    "reasons",
    "recomputed",
    "statement",
    "statements_pinned",
    "statements_sha256",
    "status",
];

fn assert_keys(v: &serde_json::Value) {
    let keys: Vec<&str> = v
        .as_object()
        .expect("object")
        .keys()
        .map(String::as_str)
        .collect();
    assert_eq!(keys, VERDICT_KEYS);
}

fn make_cert(kind: &str, inputs: &str, list: &str) -> String {
    let (code, cert, err) = run(&["make", kind, "--inputs", inputs, "--statements", list], None);
    assert_eq!(code, 0, "{err}");
    assert!(err.is_empty(), "{err}");
    cert
}

#[test]
fn the_two_new_keys_and_the_pin_option() {
    let cert = make_cert("lattice-population", r#"{"n": 1, "t": "3/2"}"#, SHIPPED);
    let cert_path = scratch("pin-population.json", &cert);
    let cert_path = cert_path.to_str().expect("path");
    let cert_digest = oscint_cert::sha256::sha256_hex(cert.as_bytes());

    // no pin
    let (code, out, _) = run(&["check", cert_path, "--statements", SHIPPED], None);
    assert_eq!(code, 0, "{out}");
    let v = verdict(&out);
    assert_keys(&v);
    assert_eq!(v["status"], "CERTIFIED");
    assert_eq!(v["statements_pinned"], serde_json::Value::Bool(false));
    assert_eq!(v["statements_sha256"], SHIPPED_SHA256);
    assert_eq!(v["certificate_sha256"], cert_digest.as_str());

    // the pin matches: lower case, upper case, mixed, and in any position
    let upper = SHIPPED_SHA256.to_uppercase();
    let mixed = format!("{}{}", &upper[..32], &SHIPPED_SHA256[32..]);
    for expected in [SHIPPED_SHA256, upper.as_str(), mixed.as_str()] {
        for args in [
            vec![
                "check",
                cert_path,
                "--statements",
                SHIPPED,
                "--expect-statements-sha256",
                expected,
            ],
            vec![
                "check",
                "--expect-statements-sha256",
                expected,
                "--statements",
                SHIPPED,
                cert_path,
            ],
        ] {
            let (code, out, err) = run(&args, None);
            assert_eq!(code, 0, "{args:?}: {err}");
            let v = verdict(&out);
            assert_keys(&v);
            assert_eq!(v["status"], "CERTIFIED");
            assert_eq!(v["statements_pinned"], serde_json::Value::Bool(true));
            assert_eq!(v["statements_sha256"], SHIPPED_SHA256); // lower case in the verdict
            assert_eq!(v["certificate_sha256"], cert_digest.as_str());
        }
    }
    // the pin is recorded in a REJECTED and in an UNRESOLVED verdict too
    let (code, out, _) = run(
        &[
            "check",
            "-",
            "--statements",
            SHIPPED,
            "--expect-statements-sha256",
            &upper,
        ],
        Some("null"),
    );
    assert_eq!(code, 1);
    assert_eq!(verdict(&out)["statements_pinned"], serde_json::Value::Bool(true));
    let far = cert.replace("\"3/2\"", "\"1000\"");
    assert_ne!(far, cert);
    let (code, out, _) = run(
        &[
            "check",
            "-",
            "--statements",
            SHIPPED,
            "--expect-statements-sha256",
            SHIPPED_SHA256,
        ],
        Some(&far),
    );
    assert_eq!(code, 2, "{out}");
    assert_eq!(verdict(&out)["statements_pinned"], serde_json::Value::Bool(true));

    // the pin does not match: exit code 3, nothing on standard output
    let wrong = SHIPPED_SHA256.replacen('e', "f", 1);
    let wrong_upper = wrong.to_uppercase();
    let other_list = scratch("pin-other-statements.json", STATEMENTS);
    let other_list = other_list.to_str().expect("path");
    let truncated = &SHIPPED_SHA256[..63];
    let longer = format!("{SHIPPED_SHA256}0");
    let not_hex = format!("{}g", &SHIPPED_SHA256[..63]);
    let cases: Vec<Vec<&str>> = vec![
        vec![
            "check",
            cert_path,
            "--statements",
            SHIPPED,
            "--expect-statements-sha256",
            &wrong,
        ],
        vec![
            "check",
            cert_path,
            "--statements",
            SHIPPED,
            "--expect-statements-sha256",
            &wrong_upper,
        ],
        // the right digest for another list
        vec![
            "check",
            cert_path,
            "--statements",
            other_list,
            "--expect-statements-sha256",
            SHIPPED_SHA256,
        ],
        // not a SHA-256 at all
        vec![
            "check",
            cert_path,
            "--statements",
            SHIPPED,
            "--expect-statements-sha256",
            truncated,
        ],
        vec![
            "check",
            cert_path,
            "--statements",
            SHIPPED,
            "--expect-statements-sha256",
            &longer,
        ],
        vec![
            "check",
            cert_path,
            "--statements",
            SHIPPED,
            "--expect-statements-sha256",
            &not_hex,
        ],
        vec![
            "check",
            cert_path,
            "--statements",
            SHIPPED,
            "--expect-statements-sha256",
            "",
        ],
        // the option without a value, and twice
        vec![
            "check",
            cert_path,
            "--statements",
            SHIPPED,
            "--expect-statements-sha256",
        ],
        vec![
            "check",
            cert_path,
            "--statements",
            SHIPPED,
            "--expect-statements-sha256",
            SHIPPED_SHA256,
            "--expect-statements-sha256",
            SHIPPED_SHA256,
        ],
        // the pin without a list
        vec!["check", cert_path, "--expect-statements-sha256", SHIPPED_SHA256],
        // the contract gives the option to `check` only
        vec![
            "make",
            "bessel-j",
            "--inputs",
            r#"{"n": 0, "x": "1"}"#,
            "--statements",
            SHIPPED,
            "--expect-statements-sha256",
            SHIPPED_SHA256,
        ],
    ];
    for args in cases {
        assert_error(&args, None);
    }
    // a mismatch is reported even for a certificate that would be rejected anyway
    let err = assert_error(
        &[
            "check",
            "-",
            "--statements",
            SHIPPED,
            "--expect-statements-sha256",
            &wrong,
        ],
        Some("null"),
    );
    assert!(err.contains(SHIPPED_SHA256) && err.contains(&wrong), "{err}");
}

#[test]
fn bad_certificate_files_are_rejected_verdicts_with_exit_code_1() {
    let list = scratch("bad-cert-statements.json", STATEMENTS);
    let list = list.to_str().expect("path");
    let good = make_cert("lattice-envelope", r#"{"d": 2, "t": "25"}"#, list);
    let mut with_mark = b"\xef\xbb\xbf".to_vec();
    with_mark.extend_from_slice(good.as_bytes());
    let mut not_utf8 = good.clone().into_bytes();
    let at = good.find("oscint-cert-rs").expect("producer");
    not_utf8[at] = 0xff;
    // digests computed outside this crate (sha256sum)
    let cases: Vec<(&str, Vec<u8>, Option<&str>)> = vec![
        (
            "null",
            b"null".to_vec(),
            Some("74234e98afe7498fb5daf1f36ac2d78acc339464f950703b8c019892f982b90b"),
        ),
        (
            "empty",
            Vec::new(),
            Some("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
        ),
        (
            "utf16-mark",
            b"\xff\xfe{}".to_vec(),
            Some("604ee178ad94b07584aa5c3cd91a5b0b1444bfb7040eedcea14179d377282647"),
        ),
        (
            "utf8-mark",
            b"\xef\xbb\xbf{}".to_vec(),
            Some("aa25e978046d680ef8740d837e6de5bc1e2a2dc6089dbda1012544b538d53f65"),
        ),
        ("mark-then-certificate", with_mark, None),
        ("not-utf8-in-a-string", not_utf8, None),
    ];
    for (name, bytes, digest) in cases {
        let path = scratch_bytes(&format!("bad-cert-{name}.json"), &bytes);
        let path = path.to_str().expect("path");
        let expected = oscint_cert::sha256::sha256_hex(&bytes);
        if let Some(d) = digest {
            assert_eq!(d, expected, "{name}");
        }
        // from a file and from standard input
        let from_file = run(&["check", path, "--statements", list], None);
        let from_stdin = run_bytes(&["check", "-", "--statements", list], &bytes);
        for (code, out, err) in [from_file, from_stdin] {
            assert_eq!(code, 1, "{name}: {err}");
            let v = verdict(&out);
            assert_keys(&v);
            assert_eq!(v["status"], "REJECTED", "{name}");
            assert_eq!(v["certificate_sha256"], expected.as_str(), "{name}");
            assert_eq!(v["statements_pinned"], serde_json::Value::Bool(false));
            assert!(v["kind"].is_null() && v["recomputed"].is_null() && v["hypothesis"].is_null());
            assert!(!v["reasons"].as_array().expect("reasons").is_empty());
        }
    }
    // the certificate itself is fine
    let (code, out, _) = run(&["check", "-", "--statements", list], Some(&good));
    assert_eq!(code, 0, "{out}");
    assert_eq!(
        verdict(&out)["certificate_sha256"],
        oscint_cert::sha256::sha256_hex(good.as_bytes()).as_str()
    );
}

#[test]
fn unusable_statement_lists_give_exit_code_3_and_no_output() {
    let good_list = scratch("lists-good.json", STATEMENTS);
    let good_list = good_list.to_str().expect("path");
    let cert = make_cert("lattice-envelope", r#"{"d": 2, "t": "25"}"#, good_list);
    let cert_path = scratch("lists-envelope.json", &cert);
    let cert_path = cert_path.to_str().expect("path");
    let entry = r#"{"label": "LS-D", "name": "n", "commitment": "c", "proved_by": "p"}"#;
    let mut with_mark = b"\xef\xbb\xbf".to_vec();
    with_mark.extend_from_slice(STATEMENTS.as_bytes());
    let mut not_utf8 = STATEMENTS.as_bytes().to_vec();
    let at = STATEMENTS.find("OscInt").expect("a name");
    not_utf8[at] = 0xff;
    let lists: Vec<(&str, Vec<u8>)> = vec![
        ("bare-array", format!("[{entry}]").into_bytes()),
        (
            "no-statements",
            br#"{"format": "oscint-statements 1"}"#.to_vec(),
        ),
        (
            "duplicate-label",
            format!(r#"{{"format": "oscint-statements 1", "statements": [{entry}, {entry}]}}"#).into_bytes(),
        ),
        (
            "no-commitment",
            br#"{"format": "oscint-statements 1", "statements": [{"label": "LS-D", "name": "n", "proved_by": "p"}]}"#
                .to_vec(),
        ),
        (
            "empty-commitment",
            br#"{"format": "oscint-statements 1", "statements": [{"label": "LS-D", "name": "n", "commitment": ""}]}"#
                .to_vec(),
        ),
        (
            "no-name",
            br#"{"format": "oscint-statements 1", "statements": [{"label": "LS-D", "commitment": "c"}]}"#.to_vec(),
        ),
        (
            "no-label",
            br#"{"format": "oscint-statements 1", "statements": [{"name": "n", "commitment": "c"}]}"#.to_vec(),
        ),
        (
            "other-format",
            format!(r#"{{"format": "oscint-statements 2", "statements": [{entry}]}}"#).into_bytes(),
        ),
        (
            "duplicate-key",
            format!(r#"{{"format": "oscint-statements 1", "statements": [{entry}], "statements": []}}"#)
                .into_bytes(),
        ),
        ("not-json", b"statements".to_vec()),
        ("empty", Vec::new()),
        ("null", b"null".to_vec()),
        ("byte-order-mark", with_mark),
        ("not-utf8", not_utf8),
    ];
    for (name, bytes) in &lists {
        let path = scratch_bytes(&format!("lists-{name}.json"), bytes);
        let path = path.to_str().expect("path");
        assert_error(&["check", cert_path, "--statements", path], None);
        // also when the certificate is itself bad: an unusable list is an error, not a verdict
        assert_error(&["check", "-", "--statements", path], Some("null"));
        // and its own digest does not make it usable
        let digest = oscint_cert::sha256::sha256_hex(bytes);
        assert_error(
            &[
                "check",
                cert_path,
                "--statements",
                path,
                "--expect-statements-sha256",
                &digest,
            ],
            None,
        );
        assert_error(
            &[
                "make",
                "lattice-envelope",
                "--inputs",
                r#"{"d": 2, "t": "25"}"#,
                "--statements",
                path,
            ],
            None,
        );
    }
    // a directory, and a file that is not there
    let dir = env!("CARGO_TARGET_TMPDIR");
    assert_error(&["check", cert_path, "--statements", dir], None);
    assert_error(&["check", dir, "--statements", good_list], None);
    let absent = format!("{dir}/there-is-no-such-file.json");
    assert_error(&["check", &absent, "--statements", good_list], None);
    assert_error(&["check", cert_path, "--statements", &absent], None);
    // the list is usable after all
    let (code, out, _) = run(&["check", cert_path, "--statements", good_list], None);
    assert_eq!(code, 0, "{out}");
}

#[test]
fn make_writes_a_certificate_or_exits_with_3() {
    let cos = |b: &str, mu: &str| {
        format!(
            r#"{{"phase": [{{"amp": "1", "freq": 1, "fn": "cos"}}], "order": 2, "a": "0", "b": "{b}", "mu": "{mu}", "t": "5"}}"#
        )
    };
    // exit code 0: a certificate that check certifies against the same list
    let long_x = format!("399.{}", "9".repeat(96));
    let tiny_mu = format!("1/{}", "9".repeat(98));
    let tiny_t = format!("0.{}1", "0".repeat(96));
    let made: Vec<(&str, String)> = vec![
        ("bessel-j", r#"{"n": 3, "x": "7/2"}"#.to_string()),
        ("bessel-j", format!(r#"{{"n": 10000, "x": "{long_x}"}}"#)),
        ("lattice-population", r#"{"n": -2, "t": "1.25"}"#.to_string()),
        ("lattice-envelope", format!(r#"{{"d": 64, "t": "{tiny_t}"}}"#)),
        ("vdc-hypothesis", cos("1", "0.54")),
        ("vdc-hypothesis", cos("1", &tiny_mu)),
    ];
    for (kind, inputs) in &made {
        let cert = make_cert(kind, inputs, SHIPPED);
        let (code, out, err) = run(&["check", "-", "--statements", SHIPPED], Some(&cert));
        assert_eq!(code, 0, "{kind} {inputs}: {out}{err}");
        assert_eq!(verdict(&out)["status"], "CERTIFIED");
    }
    // exit code 3 and nothing on standard output: inputs outside the tables
    // of section 4, in either column
    let long = format!("0.{}1", "0".repeat(98)); // 101 characters
    let refused: Vec<(&str, String)> = vec![
        ("bessel-j", r#"{"n": 1, "x": "401"}"#.to_string()),
        ("bessel-j", r#"{"n": 10001, "x": "1"}"#.to_string()),
        ("bessel-j", r#"{"n": "1", "x": "1"}"#.to_string()),
        ("bessel-j", r#"{"n": 1, "x": 1}"#.to_string()),
        ("bessel-j", r#"{"n": 1, "x": "1", "x": "1"}"#.to_string()),
        ("bessel-j", format!(r#"{{"n": 1, "x": "{long}"}}"#)),
        ("lattice-population", r#"{"n": 1, "t": "-200.5"}"#.to_string()),
        ("lattice-envelope", r#"{"d": 65, "t": "1"}"#.to_string()),
        ("lattice-envelope", r#"{"d": -1, "t": "1"}"#.to_string()),
        ("lattice-envelope", r#"{"d": 1, "t": "0"}"#.to_string()),
        ("vdc-hypothesis", cos("1", "0")),
        ("vdc-hypothesis", cos("-1", "0.1")),
        ("vdc-hypothesis", cos("65", "0.1")),
        ("vdc-hypothesis", cos("1", &long)),
    ];
    for (kind, inputs) in &refused {
        assert_error(&["make", kind, "--inputs", inputs, "--statements", SHIPPED], None);
    }
    // a hypothesis that fails: the message names the point
    let failing = cos("1", "0.5404");
    let err = assert_error(
        &[
            "make",
            "vdc-hypothesis",
            "--inputs",
            &failing,
            "--statements",
            SHIPPED,
        ],
        None,
    );
    assert!(err.contains("fails at the point 1:"), "{err}");
    // a hypothesis that is undecided: omega'' = cos x - cos(2x)/2 has minimum 1/2 on [-1, 3/2]
    let undecided = r#"{"phase": [{"amp": "-1", "freq": 1, "fn": "cos"}, {"amp": "1/8", "freq": 2, "fn": "cos"}], "order": 2, "a": "-1", "b": "3/2", "mu": "1/2", "t": "2"}"#;
    let err = assert_error(
        &[
            "make",
            "vdc-hypothesis",
            "--inputs",
            undecided,
            "--statements",
            SHIPPED,
        ],
        None,
    );
    assert!(err.contains("undecided"), "{err}");
    // the one exception: a statement without a proof in the list (LS-K in
    // the list of this file): a certificate is written, and check answers UNRESOLVED
    let list = scratch("make-unproved-statements.json", STATEMENTS);
    let list = list.to_str().expect("path");
    let cert = make_cert("lattice-population", r#"{"n": 0, "t": "1"}"#, list);
    let (code, out, _) = run(&["check", "-", "--statements", list], Some(&cert));
    assert_eq!(code, 2, "{out}");
    // a statement that is not in the list at all: no certificate
    assert_error(
        &[
            "make",
            "vdc-hypothesis",
            "--inputs",
            &cos("1", "0.54"),
            "--statements",
            list,
        ],
        None,
    );
}

#[test]
fn input_numerals_of_100_and_of_101_characters_on_the_command_line() {
    // 100 characters: `399.` and 96 nines
    let x100 = format!("399.{}", "9".repeat(96));
    assert_eq!(x100.len(), 100);
    let cert = make_cert("bessel-j", &format!(r#"{{"n": 10000, "x": "{x100}"}}"#), SHIPPED);
    let (code, out, _) = run(&["check", "-", "--statements", SHIPPED], Some(&cert));
    assert_eq!(code, 0, "{out}");
    let v = verdict(&out);
    assert_eq!(v["status"], "CERTIFIED");
    assert!(v["recomputed"]["hi"].as_str().expect("hi").len() <= 4000);
    // 101 characters: one more nine. UNRESOLVED, exit code 2, nothing recomputed
    let x101 = format!("{x100}9");
    let longer = cert.replace(&x100, &x101);
    assert_ne!(longer, cert);
    let (code, out, _) = run(&["check", "-", "--statements", SHIPPED], Some(&longer));
    assert_eq!(code, 2, "{out}");
    let v = verdict(&out);
    assert_keys(&v);
    assert_eq!(v["status"], "UNRESOLVED");
    assert!(v["recomputed"].is_null());
    assert!(
        v["reasons"][0]
            .as_str()
            .expect("reason")
            .contains("101 characters"),
        "{out}"
    );
    // and make refuses it
    assert_error(
        &[
            "make",
            "bessel-j",
            "--inputs",
            &format!(r#"{{"n": 10000, "x": "{x101}"}}"#),
            "--statements",
            SHIPPED,
        ],
        None,
    );
    // 101 characters that are not a numeral: REJECTED, exit code 1
    let malformed = cert.replace(&x100, &format!("+{x100}"));
    let (code, out, _) = run(&["check", "-", "--statements", SHIPPED], Some(&malformed));
    assert_eq!(code, 1, "{out}");
    assert_eq!(verdict(&out)["status"], "REJECTED");
}

#[test]
fn a_wrong_command_line_gives_exit_code_3_and_no_output() {
    let cert = make_cert("bessel-j", r#"{"n": 0, "x": "1"}"#, SHIPPED);
    let cert_path = scratch("usage-bessel.json", &cert);
    let cert_path = cert_path.to_str().expect("path");
    let cases: Vec<Vec<&str>> = vec![
        vec![],
        vec!["check"],
        vec!["check", "--statements", SHIPPED],
        vec!["check", cert_path],
        vec!["check", cert_path, SHIPPED],
        vec!["check", cert_path, "--statements"],
        vec!["check", cert_path, "-", "--statements", SHIPPED],
        vec!["check", cert_path, "--statements", SHIPPED, "--digits", "30"],
        vec!["check", cert_path, "--statement", SHIPPED],
        vec!["check", "--help"],
        vec!["CHECK", cert_path, "--statements", SHIPPED],
        vec!["make"],
        vec!["make", "bessel-j"],
        vec!["make", "bessel-j", "--inputs", r#"{"n": 0, "x": "1"}"#],
        vec![
            "make",
            "--inputs",
            r#"{"n": 0, "x": "1"}"#,
            "--statements",
            SHIPPED,
        ],
        vec![
            "make",
            "bessel-j",
            "lattice-envelope",
            "--inputs",
            r#"{"n": 0, "x": "1"}"#,
            "--statements",
            SHIPPED,
        ],
        vec![
            "make",
            "bessel-j",
            "--inputs",
            r#"{"n": 0, "x": "1"}"#,
            "--statements",
            SHIPPED,
            "--claim-bits",
            "7",
        ],
    ];
    for args in cases {
        // standard input is offered and must not be taken for a certificate
        assert_error(&args, Some(&cert));
    }
    // the same certificate, read from the file and from standard input
    let (code_file, out_file, _) = run(&["check", cert_path, "--statements", SHIPPED], None);
    let (code_stdin, out_stdin, _) = run(&["check", "-", "--statements", SHIPPED], Some(&cert));
    assert_eq!((code_file, code_stdin), (0, 0));
    assert_eq!(out_file, out_stdin);
}
