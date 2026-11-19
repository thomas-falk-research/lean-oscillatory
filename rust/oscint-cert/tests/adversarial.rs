// SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
//
// SPDX-License-Identifier: Apache-2.0

//! Certificates built to be refused, and the few that must be accepted.
//! The statement list used here copies the three entries of
//! `stamps/statements.json` that the contract's kinds cite.

use oscint_cert::check::{
    check, check_guarded, check_staged, compute, kind_spec, load_statements, load_statements_expecting, make,
    read_inputs, Findings, Stage, StatementList, Status, CERT_FORMAT, VERDICT_FORMAT,
};
use oscint_cert::json;
use oscint_cert::num::fmt_ratio;
use oscint_cert::sha256::sha256_hex;
use serde_json::{json, Value};

const STATEMENTS: &str = r#"{
  "format": "oscint-statements 1",
  "statements": [
    {"name": "OscInt.Statements.VdC2Statement", "label": "S1.2",
     "proved_by": "OscInt.vanDerCorput_two",
     "commitment": "66cc331de7d7bf5fb38076895ff7014f280b41cced6492f70cd87134a78a39f5"},
    {"name": "OscInt.Statements.VdCkStatement", "label": "S1.k",
     "proved_by": "OscInt.API.vdCk",
     "commitment": "3f6bcd10ddc304463b047a2ff97bea79cca928d63280b315c80a6192657022b3"},
    {"name": "OscInt.Statements.LatticeSchrodingerKernelStatement", "label": "LS-K",
     "proved_by": "OscInt.API.latticeSchrodingerKernel",
     "commitment": "50d7897f580873dbcb4d0f12300bdbf599aec479b485825991431f5bb33b620a"},
    {"name": "OscInt.Statements.LatticeSchrodingerDispersiveStatement", "label": "LS-D",
     "proved_by": "OscInt.API.latticeSchrodingerDispersive",
     "commitment": "c7b1f69b1f2313318626f3e728eb6554636424a47f551286041ba8eb297b16ef"}
  ]
}"#;

fn stmts() -> StatementList {
    load_statements(STATEMENTS.as_bytes()).expect("statement list")
}

fn stmts_with(edit: impl Fn(&mut Value)) -> StatementList {
    let mut v: Value = serde_json::from_str(STATEMENTS).expect("json");
    edit(&mut v);
    load_statements(v.to_string().as_bytes()).expect("statement list")
}

const BESSEL: &str = r#"{"n": 3, "x": "7/2"}"#;
const POPULATION: &str = r#"{"n": -2, "t": "1.25"}"#;
const ENVELOPE: &str = r#"{"d": 3, "t": "-40"}"#;
const VDC: &str = r#"{"phase": [{"amp": "1", "freq": 1, "fn": "cos"}, {"amp": "-1/8", "freq": 2, "fn": "sin"}],
                      "order": 2, "a": "0", "b": "1/4", "mu": "0.4", "t": "7"}"#;

fn all_kinds() -> Vec<(&'static str, &'static str)> {
    vec![
        ("bessel-j", BESSEL),
        ("lattice-population", POPULATION),
        ("lattice-envelope", ENVELOPE),
        ("vdc-hypothesis", VDC),
    ]
}

fn good(kind: &str, inputs: &str) -> Value {
    make(kind, inputs, &stmts(), 96).expect("certificate")
}

fn run(cert: &Value, list: &StatementList) -> (Status, Value) {
    check(cert.to_string().as_bytes(), list)
}

fn status(cert: &Value) -> Status {
    run(cert, &stmts()).0
}

fn status_text(text: &str) -> Status {
    check(text.as_bytes(), &stmts()).0
}

/// A JSON value from its text, so that the tests never spell a float in Rust.
fn lit(text: &str) -> Value {
    serde_json::from_str(text).expect("literal")
}

fn set(cert: &Value, pointer: &str, value: Value) -> Value {
    let mut c = cert.clone();
    *c.pointer_mut(pointer).unwrap_or_else(|| panic!("no {pointer}")) = value;
    c
}

fn remove(cert: &Value, parent: &str, key: &str) -> Value {
    let mut c = cert.clone();
    let obj = c
        .pointer_mut(parent)
        .and_then(Value::as_object_mut)
        .unwrap_or_else(|| panic!("no {parent}"));
    assert!(obj.remove(key).is_some(), "no key {key} under {parent:?}");
    c
}

fn insert(cert: &Value, parent: &str, key: &str, value: Value) -> Value {
    let mut c = cert.clone();
    let obj = c
        .pointer_mut(parent)
        .and_then(Value::as_object_mut)
        .unwrap_or_else(|| panic!("no {parent}"));
    obj.insert(key.to_string(), value);
    c
}

/// Every object inside a certificate, as JSON pointers.
fn object_pointers(v: &Value, here: String, out: &mut Vec<String>) {
    match v {
        Value::Object(m) => {
            out.push(here.clone());
            for (k, child) in m {
                object_pointers(child, format!("{here}/{k}"), out);
            }
        }
        Value::Array(items) => {
            for (i, child) in items.iter().enumerate() {
                object_pointers(child, format!("{here}/{i}"), out);
            }
        }
        _ => {}
    }
}

#[test]
fn good_certificates_are_certified() {
    for (kind, inputs) in all_kinds() {
        let cert = good(kind, inputs);
        let (st, verdict) = run(&cert, &stmts());
        assert_eq!(st, Status::Certified, "{kind}: {verdict}");
        assert_eq!(verdict["format"], json!(VERDICT_FORMAT));
        assert_eq!(verdict["status"], json!("CERTIFIED"));
        assert_eq!(verdict["kind"], json!(kind));
        assert_eq!(verdict["reasons"], json!([]));
        assert_eq!(
            verdict["statements_sha256"],
            json!(sha256_hex(STATEMENTS.as_bytes()))
        );
        assert!(verdict["checker"]
            .as_str()
            .is_some_and(|s| s.starts_with("oscint-cert-rs")));
        assert!(verdict["numeric_rung"]
            .as_str()
            .is_some_and(|s| s.starts_with("L2")));
        assert!(verdict["recomputed"]["lo"].is_string() && verdict["recomputed"]["hi"].is_string());
        let keys: Vec<&str> = verdict
            .as_object()
            .expect("object")
            .keys()
            .map(String::as_str)
            .collect();
        assert_eq!(
            keys,
            vec![
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
                "status"
            ]
        );
        // revision 3: the verdict names the bytes checked and says whether
        // the statement list was pinned
        assert_eq!(
            verdict["certificate_sha256"],
            json!(sha256_hex(cert.to_string().as_bytes()))
        );
        assert_eq!(verdict["statements_pinned"], json!(false));
        if kind == "bessel-j" {
            assert_eq!(verdict["statement"], Value::Null);
            assert_eq!(verdict["assumptions"], json!([]));
        } else {
            assert!(verdict["statement"]["proved_by"].is_string());
            assert!(verdict["statement"]["rung"]
                .as_str()
                .is_some_and(|s| s.starts_with("L4")));
            let spec = kind_spec(kind).expect("kind");
            let listed: Vec<&str> = verdict["assumptions"]
                .as_array()
                .expect("array")
                .iter()
                .map(|a| a["key"].as_str().expect("key"))
                .collect();
            assert_eq!(listed, spec.assumptions);
            for a in verdict["assumptions"].as_array().expect("array") {
                assert!(a["text"].is_string() && a["rung"].is_string());
            }
        }
        if kind == "vdc-hypothesis" {
            assert_eq!(verdict["hypothesis"]["status"], json!("PASS"));
        } else {
            assert_eq!(verdict["hypothesis"], Value::Null);
        }
        assert_eq!(
            check_guarded(cert.to_string().as_bytes(), &stmts()).0,
            Status::Certified
        );
    }
}

#[test]
fn every_single_key_deletion_is_rejected() {
    for (kind, inputs) in all_kinds() {
        let cert = good(kind, inputs);
        let mut objects = Vec::new();
        object_pointers(&cert, String::new(), &mut objects);
        let mut deletions = 0;
        for parent in &objects {
            let keys: Vec<String> = cert
                .pointer(parent)
                .and_then(Value::as_object)
                .expect("object")
                .keys()
                .cloned()
                .collect();
            for key in keys {
                let mutated = remove(&cert, parent, &key);
                assert_eq!(
                    status(&mutated),
                    Status::Rejected,
                    "{kind}: deleting {parent}/{key}"
                );
                deletions += 1;
            }
        }
        assert!(deletions >= 11, "{kind}: only {deletions} deletions tried");
    }
}

#[test]
fn every_extra_key_is_rejected() {
    for (kind, inputs) in all_kinds() {
        let cert = good(kind, inputs);
        let mut objects = Vec::new();
        object_pointers(&cert, String::new(), &mut objects);
        for parent in &objects {
            for extra in [json!(null), json!("x"), json!(0)] {
                let mutated = insert(&cert, parent, "extra", extra);
                assert_eq!(
                    status(&mutated),
                    Status::Rejected,
                    "{kind}: extra key under {parent:?}"
                );
            }
        }
    }
}

#[test]
fn wrong_format_kind_assumptions_producer() {
    for (kind, inputs) in all_kinds() {
        let cert = good(kind, inputs);
        for bad in [
            json!("oscint-certificate/0.2"),
            json!("oscint-certificate/1"),
            json!(""),
            json!(null),
            json!(1),
            json!(["oscint-certificate/0.1"]),
        ] {
            assert_eq!(
                status(&set(&cert, "/format", bad)),
                Status::Rejected,
                "{kind}: format"
            );
        }
        for bad in [
            json!("bessel"),
            json!("BESSEL-J"),
            json!(""),
            json!(null),
            json!(3),
            json!({}),
            json!(["bessel-j"]),
        ] {
            let (st, v) = run(&set(&cert, "/kind", bad.clone()), &stmts());
            assert_eq!(st, Status::Rejected, "{kind}: kind {bad}");
            if !bad.is_string() {
                assert_eq!(v["kind"], Value::Null);
            }
        }
        for (other, _) in all_kinds() {
            if other != kind {
                assert_eq!(
                    status(&set(&cert, "/kind", json!(other))),
                    Status::Rejected,
                    "{kind} as {other}"
                );
            }
        }
        let spec = kind_spec(kind).expect("kind");
        let mut wrong: Vec<Value> = vec![
            json!(null),
            json!("amplitude-one"),
            json!({}),
            json!([null]),
            json!(["something-else"]),
            json!([1]),
        ];
        let mut longer: Vec<&str> = spec.assumptions.to_vec();
        longer.push("unit-l1-datum");
        wrong.push(json!(longer));
        if !spec.assumptions.is_empty() {
            wrong.push(json!([]));
            wrong.push(json!(spec.assumptions[1..]));
            let mut dup = spec.assumptions.to_vec();
            dup.push(spec.assumptions[0]);
            wrong.push(json!(dup));
        }
        if spec.assumptions.len() > 1 {
            let mut reversed = spec.assumptions.to_vec();
            reversed.reverse();
            wrong.push(json!(reversed));
        }
        for bad in wrong {
            assert_eq!(
                status(&set(&cert, "/assumptions", bad.clone())),
                Status::Rejected,
                "{kind}: assumptions {bad}"
            );
        }
        for bad in [json!(null), json!(7), json!(["me"]), json!({})] {
            assert_eq!(
                status(&set(&cert, "/producer", bad)),
                Status::Rejected,
                "{kind}: producer"
            );
        }
        // any string is a producer
        assert_eq!(
            status(&set(&cert, "/producer", json!("anyone at all"))),
            Status::Certified
        );
    }
}

#[test]
fn non_strings_where_rationals_are_required() {
    let rational_slots = [
        ("bessel-j", BESSEL, vec!["/inputs/x", "/claim/lo", "/claim/hi"]),
        (
            "lattice-population",
            POPULATION,
            vec!["/inputs/t", "/claim/lo", "/claim/hi"],
        ),
        (
            "lattice-envelope",
            ENVELOPE,
            vec!["/inputs/t", "/claim/lo", "/claim/hi"],
        ),
        (
            "vdc-hypothesis",
            VDC,
            vec![
                "/inputs/a",
                "/inputs/b",
                "/inputs/mu",
                "/inputs/t",
                "/inputs/phase/0/amp",
                "/inputs/phase/1/amp",
                "/claim/bound/lo",
                "/claim/bound/hi",
            ],
        ),
    ];
    let bad_values = [
        "1",
        "0",
        "-3",
        "1.5",
        "0.25",
        "1e0",
        "1E2",
        "-0.0",
        "1e-3",
        "true",
        "false",
        "null",
        "[]",
        "[\"1\"]",
        "{}",
        "{\"lo\": \"0\", \"hi\": \"1\"}",
        "\"\"",
        "\" 1\"",
        "\"1 \"",
        "\"+1\"",
        "\"1e3\"",
        "\"NaN\"",
        "\"nan\"",
        "\"Infinity\"",
        "\"-inf\"",
        "\"1/0\"",
        "\"1/-2\"",
        "\"0x1\"",
        "\"1_0\"",
        "\".5\"",
        "\"5.\"",
        "\"1,5\"",
        "\"one\"",
        "\"1/2/3\"",
        "\"1.0e1\"",
    ];
    for (kind, inputs, slots) in rational_slots {
        let cert = good(kind, inputs);
        for slot in slots {
            for bad in bad_values {
                let mutated = set(&cert, slot, lit(bad));
                assert_eq!(status(&mutated), Status::Rejected, "{kind}: {slot} = {bad}");
            }
        }
    }
}

#[test]
fn non_integers_where_integers_are_required() {
    let integer_slots = [
        ("bessel-j", BESSEL, vec!["/inputs/n"]),
        ("lattice-population", POPULATION, vec!["/inputs/n"]),
        ("lattice-envelope", ENVELOPE, vec!["/inputs/d"]),
        (
            "vdc-hypothesis",
            VDC,
            vec!["/inputs/order", "/inputs/phase/0/freq", "/inputs/phase/1/freq"],
        ),
    ];
    let bad_values = [
        "\"3\"", "\"2\"", "2.0", "3.0", "2e0", "20e-1", "2.5", "1E1", "true", "false", "null", "[2]", "{}",
        "\"\"", "-2.0",
    ];
    for (kind, inputs, slots) in integer_slots {
        let cert = good(kind, inputs);
        for slot in slots {
            for bad in bad_values {
                // edit the text, so that the number keeps its spelling
                let marker = "\"@@SLOT@@\"";
                let text = set(&cert, slot, json!("@@SLOT@@"))
                    .to_string()
                    .replace(marker, bad);
                assert_eq!(status_text(&text), Status::Rejected, "{kind}: {slot} = {bad}");
            }
        }
    }
}

#[test]
fn tokens_that_are_not_json() {
    for (kind, inputs) in all_kinds() {
        let cert = good(kind, inputs);
        let marker = "\"@@SLOT@@\"";
        let slot = if kind == "vdc-hypothesis" {
            "/claim/bound/lo"
        } else {
            "/claim/lo"
        };
        let text = set(&cert, slot, json!("@@SLOT@@")).to_string();
        for token in [
            "NaN",
            "Infinity",
            "-Infinity",
            "nan",
            "inf",
            "1e999",
            "0x10",
            "01",
            "+1",
            "1.",
            ".5",
            "--1",
            "",
        ] {
            assert_eq!(
                status_text(&text.replace(marker, token)),
                Status::Rejected,
                "{kind}: token {token:?}"
            );
        }
    }
    for text in [
        "",
        " ",
        "null",
        "true",
        "3",
        "\"bessel-j\"",
        "[]",
        "[{}]",
        "{",
        "{}",
        "{\"format\": \"oscint-certificate/0.1\"}",
        "\u{feff}{}",
    ] {
        let (st, v) = check(text.as_bytes(), &stmts());
        assert_eq!(st, Status::Rejected, "{text:?}");
        assert_eq!(v["kind"], Value::Null);
        assert!(!v["reasons"].as_array().expect("reasons").is_empty());
    }
    assert_eq!(check(&[0xff, 0xfe, b'{', b'}'], &stmts()).0, Status::Rejected);
    assert_eq!(
        check(b"{\"kind\": \"bessel-j\"} trailing", &stmts()).0,
        Status::Rejected
    );
}

#[test]
fn duplicate_keys_are_rejected() {
    for (kind, inputs) in all_kinds() {
        let text = good(kind, inputs).to_string();
        assert_eq!(status_text(&text), Status::Certified);
        // a second "producer", "kind" or "claim" key, even with the same value
        let dup = text.replacen('{', "{\"producer\": \"x\", ", 1);
        assert_eq!(status_text(&dup), Status::Rejected, "{kind}: duplicate producer");
        let dup = text.replacen('{', &format!("{{\"kind\": \"{kind}\", "), 1);
        assert_eq!(status_text(&dup), Status::Rejected, "{kind}: duplicate kind");
        let dup = text.replacen("\"inputs\":{", "\"inputs\":{\"t\": \"1\", \"t\": \"1\", ", 1);
        assert_ne!(dup, text);
        assert_eq!(status_text(&dup), Status::Rejected, "{kind}: duplicate input");
    }
}

#[test]
fn statement_must_match_the_list() {
    for (kind, inputs) in all_kinds() {
        let cert = good(kind, inputs);
        if kind == "bessel-j" {
            let other = json!({"label": "LS-K", "name": "OscInt.Statements.LatticeSchrodingerKernelStatement",
                "commitment": "50d7897f580873dbcb4d0f12300bdbf599aec479b485825991431f5bb33b620a"});
            for bad in [other, json!({}), json!("none"), json!(false), json!(0), json!([])] {
                assert_eq!(status(&set(&cert, "/statement", bad)), Status::Rejected);
            }
            continue;
        }
        let good_commitment = cert["statement"]["commitment"]
            .as_str()
            .expect("commitment")
            .to_string();
        let flipped = {
            let mut c = good_commitment.clone();
            let last = if c.ends_with('0') { '1' } else { '0' };
            c.pop();
            c.push(last);
            c
        };
        for (slot, bad) in [
            ("/statement/commitment", json!(flipped)),
            ("/statement/commitment", json!(good_commitment.to_uppercase())),
            ("/statement/commitment", json!("")),
            ("/statement/commitment", json!(null)),
            ("/statement/commitment", json!(format!("{good_commitment} "))),
            ("/statement/name", json!("OscInt.Statements.VdC2Statement")),
            ("/statement/name", json!("")),
            ("/statement/name", json!(1)),
            ("/statement/label", json!("S1.2")),
            ("/statement/label", json!("LS-D′")),
            ("/statement/label", json!("")),
            ("/statement/label", json!(null)),
            ("/statement", json!(null)),
            ("/statement", json!("LS-K")),
            ("/statement", json!([])),
            ("/statement", json!({})),
        ] {
            assert_eq!(
                status(&set(&cert, slot, bad.clone())),
                Status::Rejected,
                "{kind}: {slot} = {bad}"
            );
        }
        // a statement of another kind, copied faithfully from the list
        for (other, other_inputs) in all_kinds() {
            if other != kind && other != "bessel-j" {
                let donor = good(other, other_inputs);
                let mutated = set(&cert, "/statement", donor["statement"].clone());
                assert_eq!(
                    status(&mutated),
                    Status::Rejected,
                    "{kind} with the statement of {other}"
                );
            }
        }
    }
}

#[test]
fn statement_without_proof_is_unresolved_and_missing_is_rejected() {
    for (kind, inputs) in all_kinds() {
        let cert = good(kind, inputs);
        let unproved: Vec<StatementList> = vec![
            stmts_with(|v| {
                for s in v["statements"].as_array_mut().expect("array") {
                    s["proved_by"] = Value::Null;
                }
            }),
            stmts_with(|v| {
                for s in v["statements"].as_array_mut().expect("array") {
                    s.as_object_mut().expect("object").remove("proved_by");
                }
            }),
            stmts_with(|v| {
                for s in v["statements"].as_array_mut().expect("array") {
                    s["proved_by"] = json!("");
                }
            }),
            stmts_with(|v| {
                for s in v["statements"].as_array_mut().expect("array") {
                    s["proved_by"] = json!(true);
                }
            }),
        ];
        for list in &unproved {
            let (st, v) = run(&cert, list);
            if kind == "bessel-j" {
                assert_eq!(st, Status::Certified);
            } else {
                assert_eq!(st, Status::Unresolved, "{kind}: {v}");
                assert_eq!(v["statement"]["proved_by"], Value::Null);
                assert!(v["statement"]["rung"]
                    .as_str()
                    .is_some_and(|s| s.starts_with("none")));
            }
        }
        // the statement removed from the list altogether
        let emptied = stmts_with(|v| v["statements"] = json!([]));
        let expected = if kind == "bessel-j" {
            Status::Certified
        } else {
            Status::Rejected
        };
        assert_eq!(run(&cert, &emptied).0, expected, "{kind}: empty list");
        // a list whose commitment changed
        let changed = stmts_with(|v| {
            for s in v["statements"].as_array_mut().expect("array") {
                s["commitment"] = json!("00");
            }
        });
        assert_eq!(run(&cert, &changed).0, expected, "{kind}: changed list");
        // an unproved statement does not rescue a wrong claim
        if kind != "bessel-j" {
            let slot = if kind == "vdc-hypothesis" {
                "/claim/bound"
            } else {
                "/claim"
            };
            let wrong = set(&cert, slot, json!({"lo": "-2", "hi": "-1"}));
            assert_eq!(
                run(&wrong, &unproved[0]).0,
                Status::Rejected,
                "{kind}: wrong claim, unproved"
            );
        }
    }
}

#[test]
fn statement_lists_that_are_not_usable() {
    for bad in [
        "", "[]", "{}", "{\"format\": \"oscint-statements 2\", \"statements\": []}",
        "{\"format\": \"oscint-statements 1\"}",
        "{\"format\": \"oscint-statements 1\", \"statements\": {}}",
        "{\"format\": \"oscint-statements 1\", \"statements\": [{\"label\": \"LS-K\"}]}",
        "{\"format\": \"oscint-statements 1\", \"statements\": [{\"label\": \"A\", \"name\": \"n\", \"commitment\": \"c\"}, {\"label\": \"A\", \"name\": \"n\", \"commitment\": \"c\"}]}",
        "{\"format\": \"oscint-statements 1\", \"statements\": [], \"statements\": []}",
    ] {
        assert!(load_statements(bad.as_bytes()).is_err(), "{bad:?}");
    }
    assert!(load_statements(&[0xc3, 0x28]).is_err());
}

fn claim_slot(kind: &str) -> &'static str {
    if kind == "vdc-hypothesis" {
        "/claim/bound"
    } else {
        "/claim"
    }
}

/// The checker's own enclosure of the quantity, as rationals.
fn enclosure(kind: &str, inputs: &str, bits: u64) -> (num_rational::BigRational, num_rational::BigRational) {
    let spec = kind_spec(kind).expect("kind");
    let mut f = Findings::default();
    let parsed = read_inputs(spec, &json::parse(inputs).expect("json"), &mut f).expect("inputs");
    assert!(f.rejected.is_empty() && f.unresolved.is_empty());
    compute(&parsed, bits)
        .expect("compute")
        .to_ratios()
        .expect("ratios")
}

#[test]
fn shifted_point_wide_and_straddling_claims() {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    let r = |n: i64, d: i64| BigRational::new(BigInt::from(n), BigInt::from(d));
    for (kind, inputs) in all_kinds() {
        let cert = good(kind, inputs);
        let slot = claim_slot(kind);
        let (lo, hi) = enclosure(kind, inputs, 256);
        let width = &hi - &lo;
        assert!(width > r(0, 1));
        let scale = hi.clone().max(-lo.clone()); // the modulus of the value, roughly
        let claim = |a: &BigRational, b: &BigRational| {
            set(&cert, slot, json!({"lo": fmt_ratio(a), "hi": fmt_ratio(b)}))
        };

        // shifted by a relative 1e-20, 1e-6 and by a lot: REJECTED
        for shift in [
            &scale * r(1, 100_000_000_000) * r(1, 1_000_000_000),
            &scale * r(1, 1_000_000),
            &scale * r(3, 1),
        ] {
            let delta = &scale * r(1, 1_000_000_000) * r(1, 1_000_000_000) * r(1, 1_000_000_000);
            for sign in [1i64, -1] {
                let centre = &lo + &shift * r(sign, 1);
                let c = claim(&(&centre - &delta), &(&centre + &delta));
                assert_eq!(status(&c), Status::Rejected, "{kind}: shifted claim");
            }
        }
        // a point claim: inside the checker's enclosure it cannot be confirmed,
        // outside it is refuted; never CERTIFIED
        let (lo2, hi2) = enclosure(kind, inputs, 512);
        let mid = (&lo2 + &hi2) / r(2, 1);
        assert_eq!(
            status(&claim(&mid, &mid)),
            Status::Unresolved,
            "{kind}: point claim at the midpoint"
        );
        assert_eq!(
            status(&claim(&lo2, &lo2)),
            Status::Unresolved,
            "{kind}: point claim at the lower end"
        );
        assert_eq!(
            status(&claim(&hi2, &hi2)),
            Status::Unresolved,
            "{kind}: point claim at the upper end"
        );
        let outside = &hi + &scale * r(1, 1000);
        assert_eq!(
            status(&claim(&outside, &outside)),
            Status::Rejected,
            "{kind}: point claim outside"
        );
        // a point of the first enclosure that the second excludes is refuted
        if lo < lo2 {
            assert_eq!(
                status(&claim(&lo, &lo)),
                Status::Rejected,
                "{kind}: point claim excluded at 512 bits"
            );
        }
        // the checker's own enclosure and anything wider: CERTIFIED
        assert_eq!(
            status(&claim(&lo, &hi)),
            Status::Certified,
            "{kind}: own enclosure"
        );
        assert_eq!(
            status(&claim(&(&lo - &scale), &(&hi + &scale))),
            Status::Certified,
            "{kind}: wide claim"
        );
        assert_eq!(
            status(&claim(&r(-1_000_000, 1), &r(1_000_000, 1))),
            Status::Certified,
            "{kind}: very wide claim"
        );
        // one end of the claim strictly inside every enclosure the checker can
        // compute (the value itself is cut): neither contained nor disjoint
        let below = &lo - &scale;
        let above = &hi + &scale;
        // cut at the midpoint of the 512-bit enclosure: is it left or right
        // of the value? Either way one of the two half-lines must not certify.
        let cut = (&lo2 + &hi2) / r(2, 1);
        let left = status(&claim(&below, &cut));
        let right = status(&claim(&cut, &above));
        assert_eq!(
            left,
            Status::Unresolved,
            "{kind}: claim ending inside the enclosure"
        );
        assert_eq!(
            right,
            Status::Unresolved,
            "{kind}: claim starting inside the enclosure"
        );
        // lo > hi
        assert_eq!(status(&claim(&hi, &lo)), Status::Rejected, "{kind}: lo > hi");
        assert_eq!(
            status(&claim(&above, &below)),
            Status::Rejected,
            "{kind}: lo > hi, wide"
        );
    }
}

#[test]
fn precision_is_doubled_once_and_only_once() {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    for (kind, inputs) in all_kinds() {
        let cert = good(kind, inputs);
        let slot = claim_slot(kind);
        let claim = |a: &BigRational, b: &BigRational| {
            set(&cert, slot, json!({"lo": fmt_ratio(a), "hi": fmt_ratio(b)}))
        };
        let (lo, hi) = enclosure(kind, inputs, 2048);
        let scale = hi.clone().max(-lo.clone());
        let pad = |bits: u32| &scale / BigRational::from_integer(BigInt::from(1) << bits);
        // true and of relative width 2^-200: contained at the first pass
        let (st, v) = run(&claim(&(&lo - pad(200)), &(&hi + pad(200))), &stmts());
        assert_eq!(st, Status::Certified, "{kind}: {v}");
        // true and of relative width 2^-400: needs the second pass
        let (st, v) = run(&claim(&(&lo - pad(400)), &(&hi + pad(400))), &stmts());
        assert_eq!(st, Status::Certified, "{kind}: {v}");
        // true but of relative width 2^-900: beyond the doubled precision
        let (st, v) = run(&claim(&(&lo - pad(900)), &(&hi + pad(900))), &stmts());
        assert_eq!(st, Status::Unresolved, "{kind}: {v}");
        // false by a relative 2^-400: refuted at the second pass
        let (st, v) = run(&claim(&(&hi + pad(400)), &(&hi + pad(399))), &stmts());
        assert_eq!(st, Status::Rejected, "{kind}: {v}");
        // false by a relative 2^-900: cannot be told apart
        let (st, v) = run(&claim(&(&hi + pad(900)), &(&hi + pad(899))), &stmts());
        assert_eq!(st, Status::Unresolved, "{kind}: {v}");
    }
}

#[test]
fn exact_values_admit_point_claims() {
    let cases = [
        ("bessel-j", r#"{"n": 0, "x": "0"}"#, "1"),
        ("bessel-j", r#"{"n": 5, "x": "0"}"#, "0"),
        ("bessel-j", r#"{"n": -5, "x": "0.0"}"#, "0"),
        ("lattice-population", r#"{"n": 0, "t": "0"}"#, "1"),
        ("lattice-population", r#"{"n": 1, "t": "0"}"#, "0"),
        ("lattice-envelope", r#"{"d": 0, "t": "123"}"#, "1"),
        ("lattice-envelope", r#"{"d": 2, "t": "1/3"}"#, "1"),
        ("lattice-envelope", r#"{"d": 64, "t": "-0.01"}"#, "1"),
    ];
    for (kind, inputs, value) in cases {
        let cert = good(kind, inputs);
        assert_eq!(
            cert["claim"],
            json!({"lo": value, "hi": value}),
            "{kind} {inputs}"
        );
        assert_eq!(status(&cert), Status::Certified, "{kind} {inputs}");
        let off = if value == "1" { "0.999999" } else { "0.000001" };
        let wrong = set(&cert, "/claim", json!({"lo": off, "hi": off}));
        assert_eq!(status(&wrong), Status::Rejected, "{kind} {inputs}");
    }
}

fn with_inputs(kind: &str, base: &str, pointer: &str, replacement: &str) -> String {
    let cert = good(kind, base);
    let marker = "\"@@SLOT@@\"";
    set(&cert, pointer, json!("@@SLOT@@"))
        .to_string()
        .replace(marker, replacement)
}

#[test]
fn inputs_outside_the_hypotheses_are_rejected() {
    let cases = [
        ("lattice-envelope", ENVELOPE, "/inputs/t", "\"0\""),
        ("lattice-envelope", ENVELOPE, "/inputs/t", "\"0.000\""),
        ("lattice-envelope", ENVELOPE, "/inputs/t", "\"-0\""),
        ("lattice-envelope", ENVELOPE, "/inputs/t", "\"0/7\""),
        ("lattice-envelope", ENVELOPE, "/inputs/d", "-1"),
        ("vdc-hypothesis", VDC, "/inputs/order", "1"),
        ("vdc-hypothesis", VDC, "/inputs/order", "0"),
        ("vdc-hypothesis", VDC, "/inputs/order", "-2"),
        ("vdc-hypothesis", VDC, "/inputs/mu", "\"0\""),
        ("vdc-hypothesis", VDC, "/inputs/mu", "\"-0.4\""),
        ("vdc-hypothesis", VDC, "/inputs/t", "\"0\""),
        ("vdc-hypothesis", VDC, "/inputs/t", "\"-10\""),
        ("vdc-hypothesis", VDC, "/inputs/a", "\"1.0001\""),
        ("vdc-hypothesis", VDC, "/inputs/b", "\"-1/1000\""),
        ("vdc-hypothesis", VDC, "/inputs/phase", "[]"),
        ("vdc-hypothesis", VDC, "/inputs/phase", "{}"),
        ("vdc-hypothesis", VDC, "/inputs/phase", "\"cos\""),
        ("vdc-hypothesis", VDC, "/inputs/phase/0/fn", "\"tan\""),
        ("vdc-hypothesis", VDC, "/inputs/phase/0/fn", "\"COS\""),
        ("vdc-hypothesis", VDC, "/inputs/phase/0/fn", "null"),
        ("vdc-hypothesis", VDC, "/inputs/phase/0", "[\"1\", 1, \"cos\"]"),
        ("vdc-hypothesis", VDC, "/claim/holds", "false"),
        ("vdc-hypothesis", VDC, "/claim/holds", "\"true\""),
        ("vdc-hypothesis", VDC, "/claim/holds", "1"),
        ("vdc-hypothesis", VDC, "/claim/holds", "null"),
        (
            "vdc-hypothesis",
            VDC,
            "/claim",
            "{\"lo\": \"0\", \"hi\": \"100\"}",
        ),
        (
            "bessel-j",
            BESSEL,
            "/claim",
            "{\"holds\": true, \"bound\": {\"lo\": \"0\", \"hi\": \"1\"}}",
        ),
        ("bessel-j", BESSEL, "/claim", "[\"0\", \"1\"]"),
        ("bessel-j", BESSEL, "/claim", "\"0.1\""),
        ("bessel-j", BESSEL, "/inputs", "[3, \"7/2\"]"),
        ("bessel-j", BESSEL, "/inputs", "null"),
    ];
    for (kind, base, pointer, replacement) in cases {
        let text = with_inputs(kind, base, pointer, replacement);
        let (st, v) = check(text.as_bytes(), &stmts());
        assert_eq!(st, Status::Rejected, "{kind}: {pointer} = {replacement}: {v}");
    }
}

#[test]
fn inputs_outside_the_supported_range_are_unresolved() {
    let many_terms = {
        let term = "{\"amp\": \"1\", \"freq\": 1, \"fn\": \"cos\"}";
        format!("[{}]", vec![term; 65].join(", "))
    };
    let long_numeral = format!("\"{}\"", "9".repeat(100_001));
    let cases: Vec<(&str, &str, &str, String)> = vec![
        ("bessel-j", BESSEL, "/inputs/x", "\"400.000001\"".into()),
        ("bessel-j", BESSEL, "/inputs/x", "\"-401\"".into()),
        (
            "bessel-j",
            BESSEL,
            "/inputs/x",
            "\"100000000000000000000/3\"".into(),
        ),
        ("bessel-j", BESSEL, "/inputs/n", "10001".into()),
        (
            "bessel-j",
            BESSEL,
            "/inputs/n",
            "-123456789012345678901234567890".into(),
        ),
        ("bessel-j", BESSEL, "/inputs/x", long_numeral.clone()),
        (
            "bessel-j",
            BESSEL,
            "/claim/lo",
            format!("\"-{}\"", "9".repeat(100_001)),
        ),
        ("lattice-population", POPULATION, "/inputs/t", "\"200.5\"".into()),
        ("lattice-population", POPULATION, "/inputs/t", "\"-1000\"".into()),
        ("lattice-population", POPULATION, "/inputs/n", "20000".into()),
        ("lattice-envelope", ENVELOPE, "/inputs/d", "65".into()),
        ("lattice-envelope", ENVELOPE, "/inputs/d", "1000000".into()),
        (
            "lattice-envelope",
            ENVELOPE,
            "/inputs/d",
            "99999999999999999999999999".into(),
        ),
        ("vdc-hypothesis", VDC, "/inputs/order", "17".into()),
        ("vdc-hypothesis", VDC, "/inputs/order", "1000".into()),
        ("vdc-hypothesis", VDC, "/inputs/b", "\"32.5\"".into()),
        ("vdc-hypothesis", VDC, "/inputs/a", "\"-64.5\"".into()),
        ("vdc-hypothesis", VDC, "/inputs/phase/0/freq", "1001".into()),
        ("vdc-hypothesis", VDC, "/inputs/phase/0/freq", "-1001".into()),
        ("vdc-hypothesis", VDC, "/inputs/phase/1/freq", "257".into()),
        ("vdc-hypothesis", VDC, "/inputs/phase", many_terms),
    ];
    for (kind, base, pointer, replacement) in cases {
        let text = with_inputs(kind, base, pointer, &replacement);
        let (st, v) = check(text.as_bytes(), &stmts());
        let shown: String = replacement.chars().take(40).collect();
        assert_eq!(
            st,
            Status::Unresolved,
            "{kind}: {pointer} = {shown}: {}",
            v["reasons"]
        );
        assert_eq!(v["recomputed"], Value::Null);
    }
    // the boundary itself is inside the range
    for (kind, inputs) in [
        ("bessel-j", r#"{"n": 0, "x": "400"}"#),
        ("bessel-j", r#"{"n": -7, "x": "-400"}"#),
        ("lattice-population", r#"{"n": 3, "t": "200"}"#),
        ("lattice-envelope", r#"{"d": 64, "t": "7"}"#),
        (
            "vdc-hypothesis",
            r#"{"phase": [{"amp": "1", "freq": 64, "fn": "cos"}], "order": 16, "a": "-1", "b": "-63/64", "mu": "1", "t": "1"}"#,
        ),
        (
            "vdc-hypothesis",
            r#"{"phase": [{"amp": "1", "freq": 1000, "fn": "sin"}], "order": 2, "a": "0.0005", "b": "0.001", "mu": "1/2", "t": "3"}"#,
        ),
    ] {
        let cert = good(kind, inputs);
        let (st, v) = run(&cert, &stmts());
        assert_eq!(st, Status::Certified, "{kind} {inputs}: {v}");
    }
    // out of range and malformed together: malformed wins
    let text = with_inputs("bessel-j", BESSEL, "/inputs/x", "\"401\"");
    let both = text.replace("\"producer\":", "\"extra\": 1, \"producer\":");
    assert_eq!(status_text(&text), Status::Unresolved);
    assert_eq!(status_text(&both), Status::Rejected);
}

#[test]
fn hypothesis_decides_before_the_bound() {
    // omega = cos x, order 2: |omega''| = |cos x| >= cos 1 = 0.5403.. on [0, 1]
    let inputs = |mu: &str, b: &str| {
        format!(
            r#"{{"phase": [{{"amp": "1", "freq": 1, "fn": "cos"}}], "order": 2, "a": "0", "b": "{b}", "mu": "{mu}", "t": "5"}}"#
        )
    };
    let cert = good("vdc-hypothesis", &inputs("0.54", "1"));
    assert_eq!(status(&cert), Status::Certified);
    // the same certificate with a larger mu: the hypothesis fails at x = 1
    let (st, v) = run(&set(&cert, "/inputs/mu", json!("0.5404")), &stmts());
    assert_eq!(st, Status::Rejected, "{v}");
    assert_eq!(v["hypothesis"]["status"], json!("FAIL"));
    assert_eq!(v["hypothesis"]["detail"]["point"], json!("1"));
    assert_eq!(v["recomputed"], Value::Null);
    // a zero of the derivative inside [0, 2]
    let (st, v) = run(&set(&cert, "/inputs/b", json!("2")), &stmts());
    assert_eq!(st, Status::Rejected, "{v}");
    assert_eq!(v["hypothesis"]["status"], json!("FAIL"));
    // make refuses to produce such certificates
    assert!(make("vdc-hypothesis", &inputs("0.5404", "1"), &stmts(), 96).is_err());

    // mu equal to the minimum of |omega''|: true, not decidable by subdivision.
    // omega = -cos x + cos(2x)/8, omega'' = cos x - cos(2x)/2 >= 1/2 on [-1, 3/2].
    let nd = |mu: &str| {
        format!(
            r#"{{"phase": [{{"amp": "-1", "freq": 1, "fn": "cos"}}, {{"amp": "1/8", "freq": 2, "fn": "cos"}}], "order": 2, "a": "-1", "b": "3/2", "mu": "{mu}", "t": "2"}}"#
        )
    };
    let base = good("vdc-hypothesis", &nd("0.499999999999"));
    assert_eq!(status(&base), Status::Certified);
    let (st, v) = run(&set(&base, "/inputs/mu", json!("1/2")), &stmts());
    assert_eq!(st, Status::Unresolved, "{v}");
    assert_eq!(v["hypothesis"]["status"], json!("UNRESOLVED"));
    // with an unresolved hypothesis the bound is not examined: even a wrong
    // bound gives UNRESOLVED (contract, rule 3)
    let wrong = set(
        &set(&base, "/inputs/mu", json!("1/2")),
        "/claim/bound",
        json!({"lo": "-2", "hi": "-1"}),
    );
    assert_eq!(status(&wrong), Status::Unresolved);
    let (st, v) = run(&set(&base, "/inputs/mu", json!("0.500000000001")), &stmts());
    assert_eq!(st, Status::Rejected, "{v}");
    assert_eq!(v["hypothesis"]["status"], json!("FAIL"));
    // a passing hypothesis with a wrong bound is REJECTED by rule 4
    let wrong = set(&base, "/claim/bound", json!({"lo": "0", "hi": "1"}));
    let (st, v) = run(&wrong, &stmts());
    assert_eq!(st, Status::Rejected, "{v}");
    assert_eq!(v["hypothesis"]["status"], json!("PASS"));
}

#[test]
fn make_refuses_bad_inputs() {
    let s = stmts();
    assert!(make("nonsense", "{}", &s, 96).is_err());
    assert!(make("bessel-j", "{}", &s, 96).is_err());
    assert!(make("bessel-j", r#"{"n": 1, "x": "401"}"#, &s, 96).is_err());
    assert!(make("bessel-j", r#"{"n": 1, "x": 3}"#, &s, 96).is_err());
    assert!(make("bessel-j", r#"{"n": 1, "x": "3", "y": "0"}"#, &s, 96).is_err());
    assert!(make("lattice-envelope", r#"{"d": 1, "t": "0"}"#, &s, 96).is_err());
    assert!(make(
        "lattice-envelope",
        r#"{"d": 1, "t": "1"}"#,
        &stmts_with(|v| v["statements"] = json!([])),
        96
    )
    .is_err());
    let cert = make("bessel-j", r#"{"n": 1, "x": "3"}"#, &s, 96).expect("certificate");
    assert_eq!(cert["format"], json!(CERT_FORMAT));
    assert_eq!(cert["inputs"], json!({"n": 1, "x": "3"}));
}

#[test]
fn a_panic_cannot_certify() {
    // check_guarded agrees with check on ordinary inputs
    for (kind, inputs) in all_kinds() {
        let cert = good(kind, inputs).to_string();
        let a = check(cert.as_bytes(), &stmts());
        let b = check_guarded(cert.as_bytes(), &stmts());
        assert_eq!(a.0, b.0);
        assert_eq!(a.1, b.1);
    }
    assert_eq!(Status::Certified.exit_code(), 0);
    assert_eq!(Status::Rejected.exit_code(), 1);
    assert_eq!(Status::Unresolved.exit_code(), 2);
}

/// The byte ranges of the text of `"key":value` for the top-level keys named.
fn protected_ranges(text: &str, cert: &Value, keys: &[&str]) -> Vec<(usize, usize)> {
    keys.iter()
        .map(|key| {
            let member = format!("\"{key}\":{}", cert[*key]);
            let start = text.find(&member).unwrap_or_else(|| panic!("{member} not found"));
            (start, start + member.len())
        })
        .collect()
}

#[test]
fn single_byte_mutations_never_panic_and_never_slip_through() {
    let replacements = *b"019 \"}]-x,e./:\\";
    for (kind, inputs) in all_kinds() {
        let cert = good(kind, inputs);
        let text = cert.to_string();
        let protected = protected_ranges(&text, &cert, &["format", "kind", "statement", "assumptions"]);
        let bytes = text.as_bytes();
        let mut counts = [0usize; 3];
        let mut surprises = 0usize;
        for i in 0..bytes.len() {
            for &r in &replacements {
                if bytes[i] == r {
                    continue;
                }
                let mut mutated = bytes.to_vec();
                mutated[i] = r;
                // `check` itself, not the guarded variant: a panic fails the test
                let (st, verdict) = check(&mutated, &stmts());
                assert_eq!(verdict["status"], json!(st.as_str()));
                assert_eq!(
                    verdict["reasons"].as_array().map(Vec::is_empty),
                    Some(st == Status::Certified)
                );
                counts[st.exit_code() as usize] += 1;
                if st == Status::Certified {
                    // whatever is certified is the original certificate up to
                    // its producer and its claim (a wider claim is still
                    // true); the other possibilities are the two symmetries:
                    // the envelope depends on |t| only ("-40" -> "040") and
                    // the population on |n| only (-2 -> 2); see below for
                    // vdc-hypothesis
                    let mut a: Value = serde_json::from_slice(&mutated).expect("certified text is JSON");
                    let mut b = cert.clone();
                    for v in [&mut a, &mut b] {
                        let obj = v.as_object_mut().expect("object");
                        obj.remove("producer");
                        obj.remove("claim");
                    }
                    if a != b {
                        if kind == "vdc-hypothesis" {
                            // the bound depends on order, mu and t only; a
                            // phase or an interval for which the hypothesis
                            // still holds gives another true certificate
                            for key in ["order", "mu", "t"] {
                                assert_eq!(
                                    a["inputs"][key], b["inputs"][key],
                                    "certified with another {key}"
                                );
                            }
                        } else {
                            let allowed = match kind {
                                "lattice-envelope" => json!({"d": 3, "t": "040"}),
                                "lattice-population" => json!({"n": 2, "t": "1.25"}),
                                _ => Value::Null,
                            };
                            assert_eq!(a["inputs"], allowed, "{kind}: certified with other inputs: {a}");
                            surprises += 1;
                        }
                        a["inputs"] = b["inputs"].clone();
                        assert_eq!(a, b, "{kind}: certified with another difference");
                    }
                }
                if protected.iter().any(|(a, b)| (*a..*b).contains(&i)) {
                    assert_eq!(
                        st,
                        Status::Rejected,
                        "{kind}: byte {i} -> {:?} in {:?}",
                        r as char,
                        String::from_utf8_lossy(&mutated)
                    );
                }
            }
        }
        // most mutations are refused; a few (the producer's name, a wider
        // claim) legitimately are not
        assert!(counts[1] > 5 * (counts[0] + 1), "{kind}: {counts:?}");
        assert!(
            surprises <= 1,
            "{kind}: {surprises} certified mutations of the inputs"
        );
    }
}

#[test]
fn truncations_and_insertions_are_rejected() {
    for (kind, inputs) in all_kinds() {
        let text = good(kind, inputs).to_string();
        for cut in 0..text.len() {
            if text.is_char_boundary(cut) {
                assert_eq!(
                    status_text(&text[..cut]),
                    Status::Rejected,
                    "{kind}: prefix of {cut} bytes"
                );
            }
        }
        for extra in ["x", "{}", "null", ",", "]", "}"] {
            assert_eq!(
                status_text(&format!("{text}{extra}")),
                Status::Rejected,
                "{kind}: trailing {extra:?}"
            );
            assert_eq!(
                status_text(&format!("{extra}{text}")),
                Status::Rejected,
                "{kind}: leading {extra:?}"
            );
        }
        assert_eq!(status_text(&format!("[{text}]")), Status::Rejected);
        assert_eq!(status_text(&format!("  {text}\n")), Status::Certified);
    }
}

#[test]
fn a_statement_list_is_named_by_its_bytes() {
    // the same list with different white space has a different digest, and
    // the verdict reports the digest of the bytes it was given
    let a = stmts();
    let spaced = format!("{STATEMENTS}\n");
    let b = load_statements(spaced.as_bytes()).expect("list");
    assert_ne!(a.sha256, b.sha256);
    let cert = good("bessel-j", BESSEL);
    assert_eq!(
        run(&cert, &b).1["statements_sha256"],
        json!(sha256_hex(spaced.as_bytes()))
    );
}

// ---------------------------------------------------------------------------
// Revision 3 of the contract
// ---------------------------------------------------------------------------

/// The keys of the verdict table of section 5, sorted.
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

/// omega = -cos x + cos(2x)/8 on [-1, 3/2], order 2: the minimum of
/// |omega''| is 1/2, attained at 0 only (see `hypothesis_decides_before_the_bound`).
fn near_degenerate(mu: &str) -> String {
    format!(
        r#"{{"phase": [{{"amp": "-1", "freq": 1, "fn": "cos"}}, {{"amp": "1/8", "freq": 2, "fn": "cos"}}], "order": 2, "a": "-1", "b": "3/2", "mu": "{mu}", "t": "2"}}"#
    )
}

fn assert_verdict_shape(bytes: &[u8], list: &StatementList, st: Status, v: &Value) {
    let keys: Vec<&str> = v
        .as_object()
        .expect("object")
        .keys()
        .map(String::as_str)
        .collect();
    assert_eq!(keys, VERDICT_KEYS, "{v}");
    assert_eq!(v["format"], json!(VERDICT_FORMAT));
    assert_eq!(v["status"], json!(st.as_str()));
    assert!(v["kind"].is_null() || v["kind"].is_string());
    assert_eq!(
        v["reasons"].as_array().map(Vec::is_empty),
        Some(st == Status::Certified)
    );
    assert!(v["checker"].is_string() && v["numeric_rung"].is_string());
    assert_eq!(v["statements_sha256"], json!(list.sha256));
    assert!(v["assumptions"].is_array());
    assert!(v["statement"].is_null() || v["statement"].is_object());
    let digest = v["certificate_sha256"].as_str().expect("certificate_sha256");
    assert_eq!(digest, sha256_hex(bytes));
    assert_eq!(digest.len(), 64);
    assert!(digest
        .bytes()
        .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c)));
    assert_eq!(v["statements_pinned"], json!(list.pinned));
}

#[test]
fn every_key_is_in_every_verdict() {
    let plain = stmts();
    let digest = sha256_hex(STATEMENTS.as_bytes());
    let pinned = load_statements_expecting(STATEMENTS.as_bytes(), Some(&digest)).expect("pinned list");
    assert!(pinned.pinned && !plain.pinned);
    let unproved = stmts_with(|v| {
        for s in v["statements"].as_array_mut().expect("array") {
            s["proved_by"] = Value::Null;
        }
    });

    // (bytes, expected status, expected rule, recomputed must be null)
    let mut cases: Vec<(Vec<u8>, Status, Stage, bool)> = vec![
        (b"".to_vec(), Status::Rejected, Stage::Structure, true),
        (b"null".to_vec(), Status::Rejected, Stage::Structure, true),
        (b"{}".to_vec(), Status::Rejected, Stage::Structure, true),
        (b"[1, 2".to_vec(), Status::Rejected, Stage::Structure, true),
        (
            vec![0xff, 0xfe, b'{', b'}'],
            Status::Rejected,
            Stage::Structure,
            true,
        ),
        (
            b"\xef\xbb\xbf{}".to_vec(),
            Status::Rejected,
            Stage::Structure,
            true,
        ),
    ];
    for (kind, inputs) in all_kinds() {
        let cert = good(kind, inputs);
        cases.push((
            cert.to_string().into_bytes(),
            Status::Certified,
            Stage::Certified,
            false,
        ));
        // a claim that is plainly wrong: decided by rule 4, which was reached
        let wrong = set(&cert, claim_slot(kind), json!({"lo": "-2", "hi": "-1"}));
        cases.push((
            wrong.to_string().into_bytes(),
            Status::Rejected,
            Stage::Claim,
            false,
        ));
        // a missing key: decided by the structure
        let cut = remove(&cert, "", "producer");
        cases.push((
            cut.to_string().into_bytes(),
            Status::Rejected,
            Stage::Structure,
            true,
        ));
    }
    // an input beyond the supported range: nothing is compared
    let far = with_inputs("bessel-j", BESSEL, "/inputs/x", "\"401\"");
    cases.push((far.into_bytes(), Status::Unresolved, Stage::Range, true));
    // decided by the hypothesis: FAIL and UNRESOLVED
    let base = good("vdc-hypothesis", &near_degenerate("0.499999999999"));
    let fail = set(&base, "/inputs/mu", json!("0.6"));
    cases.push((
        fail.to_string().into_bytes(),
        Status::Rejected,
        Stage::Hypothesis,
        true,
    ));
    let undecided = set(&base, "/inputs/mu", json!("1/2"));
    cases.push((
        undecided.to_string().into_bytes(),
        Status::Unresolved,
        Stage::Hypothesis,
        true,
    ));

    for (bytes, expected, stage, recomputed_null) in &cases {
        for list in [&plain, &pinned] {
            let (st, v, decided_by) = check_staged(bytes, list);
            assert_eq!(st, *expected, "{v}");
            assert_eq!(decided_by, *stage, "{v}");
            assert_verdict_shape(bytes, list, st, &v);
            assert_eq!(v["recomputed"].is_null(), *recomputed_null, "{v}");
            // check and check_guarded give the same verdict
            assert_eq!(check(bytes, list), (st, v.clone()));
            assert_eq!(check_guarded(bytes, list), (st, v));
        }
    }
    // rule 5 is reached only after the claim was confirmed: recomputed is there
    for (kind, inputs) in all_kinds() {
        let cert = good(kind, inputs).to_string();
        let (st, v, stage) = check_staged(cert.as_bytes(), &unproved);
        assert_verdict_shape(cert.as_bytes(), &unproved, st, &v);
        if kind == "bessel-j" {
            assert_eq!((st, stage), (Status::Certified, Stage::Certified));
        } else {
            assert_eq!((st, stage), (Status::Unresolved, Stage::Proof), "{v}");
            assert!(v["recomputed"]["lo"].is_string());
        }
    }
    // values that do not apply are null, and the kind is null when it could not be read
    let (_, v) = check(b"null", &plain);
    for key in ["kind", "statement", "recomputed", "hypothesis"] {
        assert_eq!(v[key], Value::Null, "{key}");
    }
    assert_eq!(v["assumptions"], json!([]));
    let (_, v) = check(good("bessel-j", BESSEL).to_string().as_bytes(), &plain);
    assert_eq!(v["hypothesis"], Value::Null);
    assert_eq!(v["statement"], Value::Null);
}

#[test]
fn the_verdict_is_bound_to_the_bytes_checked() {
    // digests computed outside this crate (sha256sum)
    let vectors: [(&[u8], &str); 4] = [
        (
            b"",
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        ),
        (
            b"null",
            "74234e98afe7498fb5daf1f36ac2d78acc339464f950703b8c019892f982b90b",
        ),
        (
            b"\xff\xfe{}",
            "604ee178ad94b07584aa5c3cd91a5b0b1444bfb7040eedcea14179d377282647",
        ),
        (
            b"\xef\xbb\xbf{}",
            "aa25e978046d680ef8740d837e6de5bc1e2a2dc6089dbda1012544b538d53f65",
        ),
    ];
    for (bytes, digest) in vectors {
        let (st, v) = check(bytes, &stmts());
        assert_eq!(st, Status::Rejected);
        assert_eq!(v["certificate_sha256"], json!(digest));
    }
    // the same certificate with other white space is another sequence of bytes
    let cert = good("bessel-j", BESSEL).to_string();
    let spaced = format!("{cert}\n");
    let (a, va) = check(cert.as_bytes(), &stmts());
    let (b, vb) = check(spaced.as_bytes(), &stmts());
    assert_eq!((a, b), (Status::Certified, Status::Certified));
    assert_ne!(va["certificate_sha256"], vb["certificate_sha256"]);
    assert_eq!(vb["certificate_sha256"], json!(sha256_hex(spaced.as_bytes())));
}

#[test]
fn certificates_with_bad_content_are_rejected_verdicts() {
    let good_text = good("lattice-envelope", ENVELOPE).to_string();
    let mut with_mark = b"\xef\xbb\xbf".to_vec();
    with_mark.extend_from_slice(good_text.as_bytes());
    // a byte that is not UTF-8 inside the producer's name
    let not_utf8 = {
        let marked = set(&good("lattice-envelope", ENVELOPE), "/producer", json!("@@P@@")).to_string();
        let at = marked.find("@@P@@").expect("marker");
        let mut bytes = marked.into_bytes();
        bytes[at] = 0xff;
        bytes
    };
    let utf16 = {
        let mut bytes = vec![0xff, 0xfe];
        for unit in good_text.encode_utf16() {
            bytes.extend_from_slice(&unit.to_le_bytes());
        }
        bytes
    };
    let cases: Vec<(&str, Vec<u8>)> = vec![
        ("null", b"null".to_vec()),
        ("empty", Vec::new()),
        ("white space", b" \n\t".to_vec()),
        ("byte-order mark", with_mark),
        ("not UTF-8", not_utf8),
        ("UTF-16", utf16),
        ("a lone 0x80", vec![0x80]),
    ];
    for (name, bytes) in cases {
        let (st, v) = check(&bytes, &stmts());
        assert_eq!(st, Status::Rejected, "{name}");
        assert_verdict_shape(&bytes, &stmts(), st, &v);
        assert_eq!(v["kind"], Value::Null, "{name}");
        assert_eq!(v["recomputed"], Value::Null, "{name}");
        assert_eq!(v["hypothesis"], Value::Null, "{name}");
    }
    assert_eq!(status_text(&good_text), Status::Certified);
}

#[test]
fn pinned_statement_lists() {
    let bytes = STATEMENTS.as_bytes();
    let digest = sha256_hex(bytes);
    assert!(!load_statements(bytes).expect("list").pinned);
    assert!(!load_statements_expecting(bytes, None).expect("list").pinned);
    // the expected digest, in any letter case
    let upper = digest.to_uppercase();
    let mixed: String = digest
        .chars()
        .enumerate()
        .map(|(i, c)| if i % 2 == 0 { c.to_ascii_uppercase() } else { c })
        .collect();
    assert_ne!(upper, digest);
    for expected in [&digest, &upper, &mixed] {
        let list = load_statements_expecting(bytes, Some(expected)).expect("matching digest");
        assert!(list.pinned);
        assert_eq!(list.sha256, digest); // always printed in lower case
    }
    // another digest: no list at all
    let mut other: Vec<char> = digest.chars().collect();
    other[10] = if other[10] == '0' { '1' } else { '0' };
    let other: String = other.into_iter().collect();
    let err = load_statements_expecting(bytes, Some(&other)).expect_err("mismatch");
    assert!(err.contains(&digest) && err.contains(&other), "{err}");
    let spaced = format!("{STATEMENTS}\n");
    assert!(load_statements_expecting(spaced.as_bytes(), Some(&digest)).is_err());
    // values that are not a SHA-256
    let prefixed = format!("0x{}", &digest[2..]);
    let padded = format!(" {}", &digest[1..]);
    let longer = format!("{digest}0");
    let not_hex = "g".repeat(64);
    for bad in ["", "abc", &digest[..63], &longer, &prefixed, &padded, &not_hex] {
        assert!(load_statements_expecting(bytes, Some(bad)).is_err(), "{bad:?}");
    }
    // the digest of an unusable list does not make it usable
    let unusable = b"[]";
    assert!(load_statements_expecting(unusable, Some(&sha256_hex(unusable))).is_err());

    // the verdict records the pin, whatever the status
    let pinned = load_statements_expecting(bytes, Some(&upper)).expect("pinned");
    let cert = good("lattice-population", POPULATION);
    let wrong = set(&cert, "/claim", json!({"lo": "2", "hi": "3"}));
    let far = set(&cert, "/inputs/t", json!("1000"));
    for (c, expected) in [
        (&cert, Status::Certified),
        (&wrong, Status::Rejected),
        (&far, Status::Unresolved),
    ] {
        let (st, v) = run(c, &pinned);
        assert_eq!(st, expected);
        assert_eq!(v["statements_pinned"], json!(true));
        assert_eq!(v["statements_sha256"], json!(digest));
        let (st, v) = run(c, &stmts());
        assert_eq!(st, expected);
        assert_eq!(v["statements_pinned"], json!(false));
        assert_eq!(v["statements_sha256"], json!(digest));
    }
    let (_, v) = check(b"null", &pinned);
    assert_eq!(v["statements_pinned"], json!(true));
}

#[test]
fn unusable_statement_lists_of_revision_3() {
    let entry = r#"{"label": "A", "name": "n", "commitment": "c", "proved_by": "p"}"#;
    let list = |entries: &str| format!(r#"{{"format": "oscint-statements 1", "statements": [{entries}]}}"#);
    let unusable: Vec<(&str, String)> = vec![
        ("a bare array", format!("[{entry}]")),
        ("an empty bare array", "[]".into()),
        ("no statements", r#"{"format": "oscint-statements 1"}"#.into()),
        (
            "statements under another name",
            format!(r#"{{"format": "oscint-statements 1", "entries": [{entry}]}}"#),
        ),
        (
            "statements null",
            r#"{"format": "oscint-statements 1", "statements": null}"#.into(),
        ),
        (
            "statements an object",
            format!(r#"{{"format": "oscint-statements 1", "statements": {{"A": {entry}}}}}"#),
        ),
        ("no format", format!(r#"{{"statements": [{entry}]}}"#)),
        (
            "another format",
            format!(r#"{{"format": "oscint-statements 2", "statements": [{entry}]}}"#),
        ),
        (
            "format not a string",
            format!(r#"{{"format": 1, "statements": [{entry}]}}"#),
        ),
        ("a duplicate label", list(&format!("{entry}, {entry}"))),
        (
            "a duplicate label with other content",
            list(&format!(
                r#"{entry}, {{"label": "A", "name": "m", "commitment": "d"}}"#
            )),
        ),
        (
            "an entry without commitment",
            list(r#"{"label": "A", "name": "n"}"#),
        ),
        (
            "an empty commitment",
            list(r#"{"label": "A", "name": "n", "commitment": ""}"#),
        ),
        (
            "a commitment that is null",
            list(r#"{"label": "A", "name": "n", "commitment": null}"#),
        ),
        (
            "a commitment that is a number",
            list(r#"{"label": "A", "name": "n", "commitment": 7}"#),
        ),
        (
            "an entry without name",
            list(r#"{"label": "A", "commitment": "c"}"#),
        ),
        (
            "an empty name",
            list(r#"{"label": "A", "name": "", "commitment": "c"}"#),
        ),
        (
            "an entry without label",
            list(r#"{"name": "n", "commitment": "c"}"#),
        ),
        (
            "an empty label",
            list(r#"{"label": "", "name": "n", "commitment": "c"}"#),
        ),
        ("an entry that is a string", list(r#""A""#)),
        ("an entry that is null", list("null")),
        (
            "the second entry without commitment",
            list(&format!(r#"{entry}, {{"label": "B", "name": "n"}}"#)),
        ),
        ("a byte-order mark", format!("\u{feff}{}", list(entry))),
        ("text after the list", format!("{} x", list(entry))),
        ("a trailing comma", list(&format!("{entry},"))),
        (
            "a duplicate key in an entry",
            list(r#"{"label": "A", "label": "A", "name": "n", "commitment": "c"}"#),
        ),
        (
            "NaN",
            list(r#"{"label": "A", "name": "n", "commitment": "c", "x": NaN}"#),
        ),
        ("null", "null".into()),
        ("empty", String::new()),
    ];
    for (name, text) in &unusable {
        assert!(load_statements(text.as_bytes()).is_err(), "{name}: {text}");
        // and no digest makes it usable
        let digest = sha256_hex(text.as_bytes());
        assert!(
            load_statements_expecting(text.as_bytes(), Some(&digest)).is_err(),
            "{name}, pinned"
        );
    }
    assert!(load_statements(&[0xff, 0xfe, b'{', b'}']).is_err(), "not UTF-8");
    let mut inside = list(entry).into_bytes();
    let at = inside.iter().position(|&c| c == b'A').expect("label");
    inside[at] = 0xe9; // Latin-1, not UTF-8
    assert!(load_statements(&inside).is_err(), "not UTF-8 inside a string");

    // usable: other keys, no proof, no entries
    let usable = [
        list(entry),
        list(r#"{"label": "A", "name": "n", "commitment": "c"}"#),
        list(r#"{"label": "A", "name": "n", "commitment": "c", "proved_by": null, "file": "f"}"#),
        list(&format!(
            r#"{entry}, {{"label": "B", "name": "n", "commitment": "c"}}"#
        )),
        list(""),
        format!(r#"{{"statements": [{entry}], "package": "p", "format": "oscint-statements 1"}}"#),
    ];
    for text in &usable {
        assert!(load_statements(text.as_bytes()).is_ok(), "{text}");
    }
}

/// Pads a numeral with zeros after its sign to `len` characters; the value is unchanged.
fn pad(numeral: &str, len: usize) -> String {
    let (sign, body) = match numeral.strip_prefix('-') {
        Some(rest) => ("-", rest),
        None => ("", numeral),
    };
    assert!(numeral.len() <= len);
    let padded = format!("{sign}{}{body}", "0".repeat(len - numeral.len()));
    assert_eq!(padded.chars().count(), len);
    padded
}

#[test]
fn input_numerals_of_100_and_of_101_characters() {
    let slots = [
        ("bessel-j", BESSEL, vec!["/inputs/x"]),
        ("lattice-population", POPULATION, vec!["/inputs/t"]),
        ("lattice-envelope", ENVELOPE, vec!["/inputs/t"]),
        (
            "vdc-hypothesis",
            VDC,
            vec!["/inputs/a", "/inputs/b", "/inputs/mu", "/inputs/t"],
        ),
    ];
    for (kind, inputs, pointers) in slots {
        let cert = good(kind, inputs);
        for pointer in pointers {
            let original = cert.pointer(pointer).and_then(Value::as_str).expect("numeral");
            // 100 characters: read, and the certificate stands (the value is the same)
            let at_limit = set(&cert, pointer, json!(pad(original, 100)));
            let (st, v) = run(&at_limit, &stmts());
            assert_eq!(st, Status::Certified, "{kind} {pointer}: {v}");
            assert!(make(kind, &at_limit["inputs"].to_string(), &stmts(), 96).is_ok());
            // 101 characters: beyond the supported range, nothing is computed
            let beyond = set(&cert, pointer, json!(pad(original, 101)));
            let (st, v, stage) = check_staged(beyond.to_string().as_bytes(), &stmts());
            assert_eq!(
                (st, stage),
                (Status::Unresolved, Stage::Range),
                "{kind} {pointer}: {v}"
            );
            assert_eq!(v["recomputed"], Value::Null);
            assert_eq!(v["hypothesis"], Value::Null);
            assert!(
                v["reasons"][0]
                    .as_str()
                    .is_some_and(|r| r.contains("101 characters")),
                "{v}"
            );
            assert!(make(kind, &beyond["inputs"].to_string(), &stmts(), 96).is_err());
            // far beyond
            let far = set(&cert, pointer, json!(pad(original, 4001)));
            assert_eq!(status(&far), Status::Unresolved, "{kind} {pointer}");
        }
    }
    // the limit counts every character: sign, digits, point and slash
    let nines = "9".repeat(96);
    let cases = [
        (format!("399.{nines}"), 100, true),
        (format!("-399.{}", &nines[1..]), 100, true),
        (format!("-399.{nines}"), 101, false),
        (format!("399.{nines}9"), 101, false),
        (format!("1/{}", "7".repeat(98)), 100, true),
        (format!("1/{}", "7".repeat(99)), 101, false),
        (format!("-1/{}", "7".repeat(97)), 100, true),
        (format!("-1/{}", "7".repeat(98)), 101, false),
        ("3".repeat(100), 100, false), // read, but |x| > 400
    ];
    for (x, len, supported) in cases {
        assert_eq!(x.len(), len);
        let inputs = format!(r#"{{"n": 2, "x": "{x}"}}"#);
        let made = make("bessel-j", &inputs, &stmts(), 96);
        assert_eq!(made.is_ok(), supported, "x of {len} characters: {x}");
        match made {
            Ok(cert) => assert_eq!(status(&cert), Status::Certified, "x = {x}"),
            Err(_) => {
                let cert = set(&good("bessel-j", BESSEL), "/inputs/x", json!(x));
                assert_eq!(status(&cert), Status::Unresolved, "x = {x}");
            }
        }
    }
}

#[test]
fn phase_amplitudes_and_claims_of_4000_and_of_4001_characters() {
    // a phase amplitude is not under the limit of 100
    let cert = good("vdc-hypothesis", VDC);
    for pointer in ["/inputs/phase/0/amp", "/inputs/phase/1/amp"] {
        let original = cert.pointer(pointer).and_then(Value::as_str).expect("amp");
        for len in [100, 101, 1000, 4000] {
            let c = set(&cert, pointer, json!(pad(original, len)));
            let (st, v) = run(&c, &stmts());
            assert_eq!(st, Status::Certified, "{pointer} with {len} characters: {v}");
        }
        let c = set(&cert, pointer, json!(pad(original, 4001)));
        let (st, v, stage) = check_staged(c.to_string().as_bytes(), &stmts());
        assert_eq!((st, stage), (Status::Unresolved, Stage::Range), "{v}");
        assert_eq!(v["hypothesis"], Value::Null);
        assert!(make("vdc-hypothesis", &c["inputs"].to_string(), &stmts(), 96).is_err());
    }
    // an amplitude with 4000 significant digits is used as it is: omega =
    // 10^3999 cos x has |omega''| >= 10^3999 cos 1 on [0, 1]
    let huge = format!("1{}", "0".repeat(3999));
    let inputs = |mu: &str| {
        format!(
            r#"{{"phase": [{{"amp": "{huge}", "freq": 1, "fn": "cos"}}], "order": 2, "a": "0", "b": "1", "mu": "{mu}", "t": "5"}}"#
        )
    };
    let c = good("vdc-hypothesis", &inputs("0.54"));
    let (st, v) = run(&c, &stmts());
    assert_eq!(st, Status::Certified, "{v}");
    assert_eq!(v["hypothesis"]["status"], json!("PASS"));
    // the largest mu an input can state is still far below it
    let c = good("vdc-hypothesis", &inputs(&"9".repeat(100)));
    assert_eq!(status(&c), Status::Certified);

    // a claim may have numerals of 4000 characters, not of 4001
    for (kind, inputs) in all_kinds() {
        let cert = good(kind, inputs);
        for end in ["lo", "hi"] {
            let pointer = format!("{}/{end}", claim_slot(kind));
            let original = cert.pointer(&pointer).and_then(Value::as_str).expect("end");
            let c = set(&cert, &pointer, json!(pad(original, 4000)));
            assert_eq!(status(&c), Status::Certified, "{kind} {pointer}");
            let c = set(&cert, &pointer, json!(pad(original, 4001)));
            let (st, v, stage) = check_staged(c.to_string().as_bytes(), &stmts());
            assert_eq!(
                (st, stage),
                (Status::Unresolved, Stage::Range),
                "{kind} {pointer}: {v}"
            );
            assert_eq!(v["recomputed"], Value::Null);
        }
    }
}

#[test]
fn rule_1_decides_before_the_length_of_a_numeral() {
    let ones = |n: usize| "1".repeat(n);
    let zeros = |n: usize| "0".repeat(n);
    let (rejected, unresolved) = (Status::Rejected, Status::Unresolved);
    let cases: Vec<(&str, &str, &str, String, Status)> = vec![
        // too long and not a numeral: malformed
        (
            "bessel-j",
            BESSEL,
            "/inputs/x",
            format!("+{}", ones(150)),
            rejected,
        ),
        (
            "bessel-j",
            BESSEL,
            "/inputs/x",
            format!("{}x", ones(5000)),
            rejected,
        ),
        (
            "bessel-j",
            BESSEL,
            "/inputs/x",
            format!("1/{}", zeros(150)),
            rejected,
        ),
        (
            "bessel-j",
            BESSEL,
            "/inputs/x",
            format!("1/{}", zeros(5000)),
            rejected,
        ),
        (
            "bessel-j",
            BESSEL,
            "/inputs/x",
            format!("{}.", ones(150)),
            rejected,
        ),
        (
            "bessel-j",
            BESSEL,
            "/inputs/x",
            format!("{}e5", ones(150)),
            rejected,
        ),
        (
            "bessel-j",
            BESSEL,
            "/claim/lo",
            format!("-{}/", ones(5000)),
            rejected,
        ),
        // too long and well formed: beyond the supported range
        ("bessel-j", BESSEL, "/inputs/x", ones(150), unresolved),
        ("bessel-j", BESSEL, "/inputs/x", ones(5000), unresolved),
        (
            "bessel-j",
            BESSEL,
            "/inputs/x",
            format!("0.{}", zeros(5000)),
            unresolved,
        ),
        (
            "bessel-j",
            BESSEL,
            "/claim/lo",
            format!("-{}", ones(5000)),
            unresolved,
        ),
        (
            "lattice-population",
            POPULATION,
            "/inputs/t",
            format!("0.{}", zeros(150)),
            unresolved,
        ),
        // too long and outside the hypotheses of the statement: rule 1 first
        (
            "lattice-envelope",
            ENVELOPE,
            "/inputs/t",
            format!("0.{}", zeros(150)),
            rejected,
        ),
        (
            "lattice-envelope",
            ENVELOPE,
            "/inputs/t",
            format!("-{}", zeros(5000)),
            rejected,
        ),
        (
            "lattice-envelope",
            ENVELOPE,
            "/inputs/t",
            format!("0/{}", ones(5000)),
            rejected,
        ),
        (
            "lattice-envelope",
            ENVELOPE,
            "/inputs/t",
            format!("0.{}1", zeros(150)),
            unresolved,
        ),
        (
            "vdc-hypothesis",
            VDC,
            "/inputs/mu",
            format!("-0.{}1", zeros(150)),
            rejected,
        ),
        (
            "vdc-hypothesis",
            VDC,
            "/inputs/mu",
            format!("-{}", ones(5000)),
            rejected,
        ),
        ("vdc-hypothesis", VDC, "/inputs/mu", zeros(5000), rejected),
        (
            "vdc-hypothesis",
            VDC,
            "/inputs/mu",
            format!("0.{}1", zeros(150)),
            unresolved,
        ),
        (
            "vdc-hypothesis",
            VDC,
            "/inputs/t",
            format!("-{}", ones(200)),
            rejected,
        ),
        (
            "vdc-hypothesis",
            VDC,
            "/inputs/t",
            format!("0.{}", zeros(4000)),
            rejected,
        ),
        ("vdc-hypothesis", VDC, "/inputs/t", ones(200), unresolved),
        // a > b, where it can be told: from the values up to 4000
        // characters, from the signs beyond (here a = 0 and b = 1/4)
        ("vdc-hypothesis", VDC, "/inputs/a", ones(150), rejected),
        ("vdc-hypothesis", VDC, "/inputs/a", ones(5000), unresolved),
        (
            "vdc-hypothesis",
            VDC,
            "/inputs/b",
            format!("-{}", ones(5000)),
            rejected,
        ),
        ("vdc-hypothesis", VDC, "/inputs/b", ones(5000), unresolved),
        // lo > hi in a claim, likewise
        (
            "vdc-hypothesis",
            VDC,
            "/claim/bound/hi",
            format!("-{}", ones(5000)),
            rejected,
        ),
        ("vdc-hypothesis", VDC, "/claim/bound/hi", ones(5000), unresolved),
    ];
    for (kind, base, pointer, numeral, expected) in cases {
        let cert = set(&good(kind, base), pointer, json!(numeral));
        let (st, v) = run(&cert, &stmts());
        let shown: String = numeral.chars().take(12).collect();
        assert_eq!(
            st,
            expected,
            "{kind}: {pointer} = {shown}... ({} characters): {}",
            numeral.len(),
            v["reasons"]
        );
        assert_eq!(v["recomputed"], Value::Null);
    }
}

#[test]
fn integers_of_300_and_of_301_digits() {
    let digits = |n: usize| format!("1{}", "0".repeat(n - 1));
    let (rejected, unresolved) = (Status::Rejected, Status::Unresolved);
    let cases: Vec<(&str, &str, &str, String, Status)> = vec![
        // 300 digits: an integer, far outside the supported range
        ("bessel-j", BESSEL, "/inputs/n", digits(300), unresolved),
        (
            "bessel-j",
            BESSEL,
            "/inputs/n",
            format!("-{}", digits(300)),
            unresolved,
        ),
        (
            "lattice-population",
            POPULATION,
            "/inputs/n",
            digits(300),
            unresolved,
        ),
        ("lattice-envelope", ENVELOPE, "/inputs/d", digits(300), unresolved),
        ("vdc-hypothesis", VDC, "/inputs/order", digits(300), unresolved),
        (
            "vdc-hypothesis",
            VDC,
            "/inputs/phase/0/freq",
            digits(300),
            unresolved,
        ),
        // 301 digits and more: malformed
        ("bessel-j", BESSEL, "/inputs/n", digits(301), rejected),
        (
            "bessel-j",
            BESSEL,
            "/inputs/n",
            format!("-{}", digits(301)),
            rejected,
        ),
        ("bessel-j", BESSEL, "/inputs/n", digits(305), rejected),
        ("bessel-j", BESSEL, "/inputs/n", digits(400), rejected),
        ("bessel-j", BESSEL, "/inputs/n", digits(5000), rejected),
        (
            "lattice-population",
            POPULATION,
            "/inputs/n",
            digits(301),
            rejected,
        ),
        ("lattice-envelope", ENVELOPE, "/inputs/d", digits(301), rejected),
        ("vdc-hypothesis", VDC, "/inputs/order", digits(301), rejected),
        (
            "vdc-hypothesis",
            VDC,
            "/inputs/phase/0/freq",
            digits(301),
            rejected,
        ),
        (
            "vdc-hypothesis",
            VDC,
            "/inputs/phase/1/freq",
            format!("-{}", digits(301)),
            rejected,
        ),
        // outside the hypotheses whatever the length
        (
            "lattice-envelope",
            ENVELOPE,
            "/inputs/d",
            format!("-{}", digits(300)),
            rejected,
        ),
        (
            "vdc-hypothesis",
            VDC,
            "/inputs/order",
            format!("-{}", digits(300)),
            rejected,
        ),
    ];
    for (kind, base, pointer, replacement, expected) in cases {
        let text = with_inputs(kind, base, pointer, &replacement);
        let (st, v) = check(text.as_bytes(), &stmts());
        assert_eq!(
            st,
            expected,
            "{kind}: {pointer} with {} characters: {}",
            replacement.len(),
            v["reasons"]
        );
    }
}

fn rat(s: &str) -> num_rational::BigRational {
    oscint_cert::num::parse_rational(s).unwrap_or_else(|e| panic!("{s}: {e:?}"))
}

fn numeral_lengths(v: &Value, out: &mut Vec<usize>) {
    match v {
        Value::String(s) => out.push(s.len()),
        Value::Array(items) => items.iter().for_each(|x| numeral_lengths(x, out)),
        Value::Object(m) => m.values().for_each(|x| numeral_lengths(x, out)),
        _ => {}
    }
}

#[test]
fn tiny_radicands_are_decided() {
    // order 2, t = 1, mu = 1/(10^98 - 1): the bound is 8 sqrt(10^98 - 1),
    // which is 8 * 10^49 less about 4 * 10^-49
    let mu = format!("1/{}", "9".repeat(98));
    assert_eq!(mu.len(), 100);
    let inputs = format!(
        r#"{{"phase": [{{"amp": "1", "freq": 1, "fn": "cos"}}], "order": 2, "a": "0", "b": "1", "mu": "{mu}", "t": "1"}}"#
    );
    let cert = good("vdc-hypothesis", &inputs);
    let (st, v) = run(&cert, &stmts());
    assert_eq!(st, Status::Certified, "{v}");
    assert_eq!(v["hypothesis"]["status"], json!("PASS"));
    let top = format!("8{}", "0".repeat(49));
    let below = format!("7{}", "9".repeat(49));
    let (lo, hi) = (
        rat(v["recomputed"]["lo"].as_str().expect("lo")),
        rat(v["recomputed"]["hi"].as_str().expect("hi")),
    );
    // (at 256 bits the upper end is 8 * 10^49 itself: the value is closer to it than 2^-320)
    assert!(rat(&below) < lo && lo < hi && hi <= rat(&top), "{v}");
    let bound = |a: &str, b: &str| set(&cert, "/claim/bound", json!({"lo": a, "hi": b}));
    assert_eq!(status(&bound(&below, &top)), Status::Certified);
    assert_eq!(status(&bound("0", &top)), Status::Certified);
    // false by 4 * 10^-49 in 8 * 10^49, a relative 5 * 10^-99: refuted, at the second pass
    let above = format!("8{}1", "0".repeat(48));
    let (st, v) = run(&bound(&top, &above), &stmts());
    assert_eq!(st, Status::Rejected, "{v}");
    assert!(
        rat(v["recomputed"]["hi"].as_str().expect("hi")) < rat(&top),
        "{v}"
    );
    assert_eq!(status(&bound("0", &below)), Status::Rejected);
    assert_eq!(
        status(&bound(&above, &format!("9{}", "0".repeat(49)))),
        Status::Rejected
    );
    assert_eq!(status(&bound("0", "1")), Status::Rejected);

    // d = 64, t = 10^-97: (C*/2 pi)^64 (2 * 10^-97)^(-64/3) is far above 1,
    // so the envelope is exactly 1
    for t in [
        format!("0.{}1", "0".repeat(96)),
        format!("-0.{}1", "0".repeat(96)),
        format!("1/1{}", "0".repeat(97)),
        format!("1/{}", "9".repeat(98)),
    ] {
        assert!(t.len() <= 100);
        let cert = good("lattice-envelope", &format!(r#"{{"d": 64, "t": "{t}"}}"#));
        assert_eq!(cert["claim"], json!({"lo": "1", "hi": "1"}), "t = {t}");
        let (st, v) = run(&cert, &stmts());
        assert_eq!(st, Status::Certified, "{v}");
        assert_eq!(v["recomputed"], json!({"lo": "1", "hi": "1"}));
        let claim = |a: &str, b: &str| set(&cert, "/claim", json!({"lo": a, "hi": b}));
        assert_eq!(status(&claim("1", "2")), Status::Certified);
        assert_eq!(status(&claim("0", "1")), Status::Certified);
        assert_eq!(status(&claim("1/2", "0.999999")), Status::Rejected);
        assert_eq!(
            status(&claim(
                "1.0000000000000000000000000000000000000000000000000000000000000001",
                "2"
            )),
            Status::Rejected
        );
    }
    // the other end: d = 64 and the largest t an input can state
    let cert = good(
        "lattice-envelope",
        &format!(r#"{{"d": 64, "t": "{}"}}"#, "9".repeat(100)),
    );
    let (st, v) = run(&cert, &stmts());
    assert_eq!(st, Status::Certified, "{v}");
    let hi = rat(v["recomputed"]["hi"].as_str().expect("hi"));
    assert!(hi > rat("0") && hi < rat(&format!("1/1{}", "0".repeat(2000))));
}

#[test]
fn tiny_values_of_bessel_functions_are_decided() {
    let e25 = format!("1/1{}", "0".repeat(25));
    let minus_e25 = format!("-{e25}");
    let e3990 = format!("1/1{}", "0".repeat(3990));
    let tiny_x = format!("0.{}1", "0".repeat(97)); // 10^-98, 100 characters
    assert_eq!(tiny_x.len(), 100);
    let near_400 = format!("399.{}", "9".repeat(96));
    // J_n(x) > 0 for 0 < x < n; (-1)^n J_n(x) for the reflections. All of
    // these are positive, and far below 10^-3990.
    let positive: Vec<(&str, String)> = vec![
        ("bessel-j", format!(r#"{{"n": 10000, "x": "{tiny_x}"}}"#)),
        (
            "bessel-j",
            format!(r#"{{"n": -10000, "x": "-0.{}1"}}"#, "0".repeat(96)),
        ),
        ("bessel-j", format!(r#"{{"n": 10000, "x": "{near_400}"}}"#)),
        (
            "bessel-j",
            format!(r#"{{"n": 9999, "x": "1/{}"}}"#, "9".repeat(98)),
        ),
        (
            "lattice-population",
            format!(r#"{{"n": 10000, "t": "{tiny_x}"}}"#),
        ),
        (
            "lattice-population",
            format!(r#"{{"n": -9999, "t": "-1/{}"}}"#, "9".repeat(97)),
        ),
        ("lattice-population", r#"{"n": 10000, "t": "200"}"#.to_string()),
    ];
    for (kind, inputs) in &positive {
        let cert = good(kind, inputs);
        let mut lengths = Vec::new();
        numeral_lengths(&cert["claim"], &mut lengths);
        assert!(lengths.iter().all(|&l| l <= 4000), "{kind} {inputs}: {lengths:?}");
        let (st, v) = run(&cert, &stmts());
        assert_eq!(st, Status::Certified, "{kind} {inputs}: {}", v["reasons"]);
        let mut lengths = Vec::new();
        numeral_lengths(&v["recomputed"], &mut lengths);
        assert!(lengths.iter().all(|&l| l <= 4000), "{kind} {inputs}: {lengths:?}");
        // what is printed is an enclosure: it can serve as a claim
        assert_eq!(
            status(&set(&cert, "/claim", v["recomputed"].clone())),
            Status::Certified
        );
        let claim = |a: &str, b: &str| set(&cert, "/claim", json!({"lo": a, "hi": b}));
        for (a, b, expected) in [
            ("0", e25.as_str(), Status::Certified),
            (minus_e25.as_str(), e25.as_str(), Status::Certified),
            ("0", e3990.as_str(), Status::Certified),
            ("0", "1", Status::Certified),
            // the value is not 0, and it is positive
            ("0", "0", Status::Rejected),
            (minus_e25.as_str(), "0", Status::Rejected),
            (e3990.as_str(), "1", Status::Rejected),
            (e25.as_str(), "1", Status::Rejected),
        ] {
            let (st, v) = run(&claim(a, b), &stmts());
            let shown: String = a.chars().take(10).collect();
            assert_eq!(st, expected, "{kind} {inputs}: [{shown}.., ..]: {}", v["reasons"]);
        }
    }
    // an odd order and a negative argument: negative
    let cert = good(
        "bessel-j",
        &format!(r#"{{"n": 9999, "x": "-1/{}"}}"#, "9".repeat(97)),
    );
    assert_eq!(status(&cert), Status::Certified);
    let claim = |a: &str, b: &str| set(&cert, "/claim", json!({"lo": a, "hi": b}));
    assert_eq!(status(&claim(&minus_e25, "0")), Status::Certified);
    assert_eq!(status(&claim("0", &e25)), Status::Rejected);
    assert_eq!(status(&claim("0", "0")), Status::Rejected);
}

#[test]
fn rational_van_der_corput_bounds_are_exact() {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    // omega = cos x: |omega''| = cos x >= 1/4 on [0, 1]. Order 2 and
    // t mu = 9 give (5 * 2 - 2) * 9^(-1/2) = 8/3, which no dyadic interval
    // can end at.
    let inputs = |mu: &str, t: &str| {
        format!(
            r#"{{"phase": [{{"amp": "1", "freq": 1, "fn": "cos"}}], "order": 2, "a": "0", "b": "1", "mu": "{mu}", "t": "{t}"}}"#
        )
    };
    let cert = good("vdc-hypothesis", &inputs("1/4", "36"));
    // make still writes an interval around the value
    let (lo, hi) = (
        rat(cert["claim"]["bound"]["lo"].as_str().expect("lo")),
        rat(cert["claim"]["bound"]["hi"].as_str().expect("hi")),
    );
    assert!(lo < rat("8/3") && rat("8/3") < hi);
    let (st, v) = run(&cert, &stmts());
    assert_eq!(st, Status::Certified, "{v}");
    assert_eq!(v["recomputed"], json!({"lo": "8/3", "hi": "8/3"}));
    let bound = |a: &str, b: &str| set(&cert, "/claim/bound", json!({"lo": a, "hi": b}));
    let just_above = format!("2.{}7", "6".repeat(80));
    let just_below = format!("2.{}", "6".repeat(80));
    for (a, b, expected) in [
        ("8/3", "8/3", Status::Certified),
        ("16/6", just_above.as_str(), Status::Certified),
        (just_below.as_str(), "8/3", Status::Certified),
        ("8/3", "3", Status::Certified),
        ("2", "8/3", Status::Certified),
        ("2.67", "3", Status::Rejected),
        ("2", "2.66", Status::Rejected),
        (just_above.as_str(), "3", Status::Rejected),
        ("2", just_below.as_str(), Status::Rejected),
        (just_below.as_str(), just_below.as_str(), Status::Rejected),
    ] {
        let (st, v) = run(&bound(a, b), &stmts());
        assert_eq!(st, expected, "[{a}, {b}]: {v}");
    }
    // order 3: omega''' = sin x >= 3/8 on [1/2, 1]; t mu = 27/8 gives
    // (5 * 4 - 2) * (8/27)^(1/3) = 12
    let inputs3 = r#"{"phase": [{"amp": "1", "freq": 1, "fn": "cos"}], "order": 3, "a": "1/2", "b": "1", "mu": "3/8", "t": "9"}"#;
    let cert3 = good("vdc-hypothesis", inputs3);
    let (st, v) = run(&cert3, &stmts());
    assert_eq!(st, Status::Certified, "{v}");
    assert_eq!(v["recomputed"], json!({"lo": "12", "hi": "12"}));
    let point = set(&cert3, "/claim/bound", json!({"lo": "12", "hi": "12"}));
    assert_eq!(status(&point), Status::Certified);
    let off = set(
        &cert3,
        "/claim/bound",
        json!({"lo": "12.000001", "hi": "12.000001"}),
    );
    assert_eq!(status(&off), Status::Rejected);
    // a bound that is not rational is never a point: t mu = 8 gives 8 / sqrt 8
    let cert = good("vdc-hypothesis", &inputs("1/4", "32"));
    let (st, v) = run(&cert, &stmts());
    assert_eq!(st, Status::Certified, "{v}");
    let (lo, hi) = (
        rat(v["recomputed"]["lo"].as_str().expect("lo")),
        rat(v["recomputed"]["hi"].as_str().expect("hi")),
    );
    assert!(lo < hi);
    // the square of the bound is 8
    let eight = BigRational::from_integer(BigInt::from(8));
    assert!(&lo * &lo < eight && eight < &hi * &hi);
    let mid = (&lo + &hi) / BigRational::from_integer(BigInt::from(2));
    let point = set(
        &cert,
        "/claim/bound",
        json!({"lo": fmt_ratio(&mid), "hi": fmt_ratio(&mid)}),
    );
    assert_ne!(status(&point), Status::Certified);
}

#[test]
fn make_writes_only_what_check_certifies() {
    let s = stmts();
    let unproved = stmts_with(|v| {
        for st in v["statements"].as_array_mut().expect("array") {
            st["proved_by"] = Value::Null;
        }
    });
    let tiny = format!("0.{}1", "0".repeat(97));
    let large = "9".repeat(100);
    let cases: Vec<(&str, String)> = vec![
        ("bessel-j", r#"{"n": 0, "x": "0"}"#.into()),
        ("bessel-j", r#"{"n": -0, "x": "-0"}"#.into()),
        ("bessel-j", r#"{"n": 7, "x": "400"}"#.into()),
        ("bessel-j", r#"{"n": -10000, "x": "-400"}"#.into()),
        ("bessel-j", format!(r#"{{"n": 10000, "x": "{tiny}"}}"#)),
        ("bessel-j", format!(r#"{{"n": 1, "x": "{tiny}"}}"#)),
        ("lattice-population", r#"{"n": 10000, "t": "-200"}"#.into()),
        ("lattice-population", format!(r#"{{"n": 3, "t": "{tiny}"}}"#)),
        ("lattice-population", r#"{"n": 0, "t": "0"}"#.into()),
        ("lattice-envelope", r#"{"d": 0, "t": "1"}"#.into()),
        ("lattice-envelope", format!(r#"{{"d": 64, "t": "{tiny}"}}"#)),
        (
            "lattice-envelope",
            format!(r#"{{"d": 64, "t": "-{}"}}"#, &large[1..]),
        ),
        ("lattice-envelope", format!(r#"{{"d": 1, "t": "{large}"}}"#)),
        (
            "vdc-hypothesis",
            format!(
                r#"{{"phase": [{{"amp": "{large}", "freq": -1, "fn": "sin"}}], "order": 16, "a": "1/2", "b": "1", "mu": "{tiny}", "t": "{tiny}"}}"#
            ),
        ),
        (
            "vdc-hypothesis",
            format!(
                r#"{{"phase": [{{"amp": "1", "freq": 1, "fn": "cos"}}], "order": 2, "a": "1", "b": "1", "mu": "0.54", "t": "{large}"}}"#
            ),
        ),
        ("vdc-hypothesis", VDC.into()),
    ];
    for (kind, inputs) in &cases {
        for bits in [8, 96, 240] {
            let cert = make(kind, inputs, &s, bits).unwrap_or_else(|e| panic!("{kind} {inputs}: {e}"));
            let (st, v) = run(&cert, &s);
            assert_eq!(st, Status::Certified, "{kind} {inputs} at {bits} bits: {v}");
            let mut lengths = Vec::new();
            numeral_lengths(&cert["claim"], &mut lengths);
            assert!(lengths.iter().all(|&l| l <= 4000), "{kind} {inputs}: {lengths:?}");
            // the one exception: a statement without a proof in the list
            let cert = make(kind, inputs, &unproved, bits).expect("certificate");
            let (st, _, stage) = check_staged(cert.to_string().as_bytes(), &unproved);
            if *kind == "bessel-j" {
                assert_eq!(st, Status::Certified);
            } else {
                assert_eq!((st, stage), (Status::Unresolved, Stage::Proof), "{kind} {inputs}");
            }
        }
    }
    // an integer written -0 is the integer 0
    let cert = make("bessel-j", r#"{"n": -0, "x": "1/3"}"#, &s, 96).expect("certificate");
    assert_eq!(cert["inputs"]["n"].to_string(), "0");
    assert_eq!(status(&cert), Status::Certified);

    // no certificate: either column of section 4, and the hypothesis
    let cos_on = |b: &str, mu: &str| {
        format!(
            r#"{{"phase": [{{"amp": "1", "freq": 1, "fn": "cos"}}], "order": 2, "a": "0", "b": "{b}", "mu": "{mu}", "t": "5"}}"#
        )
    };
    let refused: Vec<(&str, String)> = vec![
        ("bessel-j", r#"{"n": 1, "x": "401"}"#.into()),
        ("bessel-j", r#"{"n": 10001, "x": "1"}"#.into()),
        ("bessel-j", r#"{"n": 1.0, "x": "1"}"#.into()),
        ("bessel-j", format!(r#"{{"n": 1, "x": "{}"}}"#, pad("1", 101))),
        ("lattice-population", r#"{"n": 1, "t": "200.5"}"#.into()),
        ("lattice-envelope", r#"{"d": 65, "t": "1"}"#.into()),
        ("lattice-envelope", r#"{"d": -1, "t": "1"}"#.into()),
        ("lattice-envelope", r#"{"d": 1, "t": "0.0"}"#.into()),
        ("vdc-hypothesis", cos_on("1", "0")),
        ("vdc-hypothesis", cos_on("-1", "0.1")),
        ("vdc-hypothesis", cos_on("65", "0.1")),
        (
            "vdc-hypothesis",
            cos_on("1", "0.1").replace("\"order\": 2", "\"order\": 17"),
        ),
        (
            "vdc-hypothesis",
            cos_on("1", "0.1").replace("\"order\": 2", "\"order\": 1"),
        ),
        ("vdc-hypothesis", cos_on("1", "0.1").replace("\"cos\"", "\"tan\"")),
    ];
    for (kind, inputs) in &refused {
        assert!(make(kind, inputs, &s, 96).is_err(), "{kind} {inputs}");
    }
    assert!(make("vdc-hypothesis", &cos_on("1", "0.1"), &s, 96).is_ok());
    // a hypothesis that fails: the message names the point
    let err = make("vdc-hypothesis", &cos_on("1", "0.5404"), &s, 96).expect_err("fails at 1");
    assert!(err.contains("fails at the point 1:"), "{err}");
    let err = make("vdc-hypothesis", &cos_on("2", "0.001"), &s, 96).expect_err("a zero inside");
    assert!(err.contains("fails at the point "), "{err}");
    // a hypothesis that is undecided
    let err = make("vdc-hypothesis", &near_degenerate("1/2"), &s, 96).expect_err("undecided");
    assert!(err.contains("undecided"), "{err}");
}
