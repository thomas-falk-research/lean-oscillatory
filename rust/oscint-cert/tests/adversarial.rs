//! Certificates built to be refused, and the few that must be accepted.
//! The statement list used here copies the three entries of
//! `stamps/statements.json` that the contract's kinds cite.

use oscint_cert::check::{
    check, check_guarded, compute, kind_spec, load_statements, make, read_inputs, Findings, StatementList,
    Status, CERT_FORMAT, VERDICT_FORMAT,
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
                "checker",
                "format",
                "hypothesis",
                "kind",
                "numeric_rung",
                "reasons",
                "recomputed",
                "statement",
                "statements_sha256",
                "status"
            ]
        );
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
    // a passing hypothesis with a wrong bound is REJECTED by rule 2
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
