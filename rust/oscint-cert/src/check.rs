//! The checker of certificate contract 0.1: reads a certificate and a
//! statement list, recomputes everything, and returns a verdict.
//!
//! Order of the decision (contract, section 5):
//!  1. malformed input, a statement that does not match the list, wrong
//!     assumptions, an input outside the statement's hypotheses: REJECTED;
//!  2. an input outside the supported range or the budget: UNRESOLVED;
//!  3. for `vdc-hypothesis`, the hypothesis: FAIL is REJECTED, UNRESOLVED is
//!     UNRESOLVED;
//!  4. the claimed enclosure against the checker's own, at 256 and then at
//!     512 bits: disjoint is REJECTED, neither contained nor disjoint after
//!     the second pass is UNRESOLVED;
//!  5. a statement without a machine-checked proof in the list: UNRESOLVED;
//!  6. otherwise CERTIFIED.

use crate::bessel::{bessel_j, N_MAX, X_MAX};
use crate::json::{self, J};
use crate::num::{fmt_ratio, parse_rational, CalcError, Iv, NumErr, Res};
use crate::quant::{decide_hypothesis, envelope, population, vdc_bound, HypStatus, PhaseTerm, PIECE_BUDGET};
use crate::sha256::sha256_hex;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, ToPrimitive, Zero};
use serde_json::{json, Value};

pub const CHECKER: &str = concat!("oscint-cert-rs ", env!("CARGO_PKG_VERSION"));
pub const CERT_FORMAT: &str = "oscint-certificate/0.1";
pub const VERDICT_FORMAT: &str = "oscint-verdict/0.1";
pub const STATEMENTS_FORMAT: &str = "oscint-statements 1";

/// Relative precision, in bits, of the first comparison; the second uses twice as many.
pub const FIRST_PRECISION_BITS: u64 = 256;

const STATEMENT_RUNG: &str =
    "L4 (machine-checked; statement fidelity reviewed by AI referees, not yet by a human expert)";
const STATEMENT_RUNG_UNPROVED: &str = "none (no machine-checked proof in the statement list)";
const NUMERIC_RUNG: &str =
    "L2 (exact rational interval arithmetic; the checker is tested, not proved correct)";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    Certified,
    Rejected,
    Unresolved,
}

impl Status {
    pub fn as_str(self) -> &'static str {
        match self {
            Status::Certified => "CERTIFIED",
            Status::Rejected => "REJECTED",
            Status::Unresolved => "UNRESOLVED",
        }
    }
    /// Exit code of the command line (contract, section 5).
    pub fn exit_code(self) -> u8 {
        match self {
            Status::Certified => 0,
            Status::Rejected => 1,
            Status::Unresolved => 2,
        }
    }
}

#[derive(Debug, Clone)]
pub struct StatementEntry {
    pub label: String,
    pub name: String,
    pub commitment: String,
    pub proved_by: Option<String>,
}

#[derive(Debug, Clone)]
pub struct StatementList {
    pub sha256: String,
    pub entries: Vec<StatementEntry>,
}

impl StatementList {
    pub fn find(&self, label: &str) -> Option<&StatementEntry> {
        self.entries.iter().find(|e| e.label == label)
    }
}

/// Reads a statement list (format `oscint-statements 1`). An unusable list
/// is an input error of the command line, not a verdict.
pub fn load_statements(bytes: &[u8]) -> Result<StatementList, String> {
    let text = std::str::from_utf8(bytes).map_err(|_| "the statement list is not UTF-8".to_string())?;
    let j = json::parse(text).map_err(|e| format!("the statement list: {e}"))?;
    match j.get("format") {
        Some(J::Str(s)) if s == STATEMENTS_FORMAT => {}
        _ => {
            return Err(format!(
                "the statement list does not have format {STATEMENTS_FORMAT:?}"
            ))
        }
    }
    let items = match j.get("statements") {
        Some(J::Arr(items)) => items,
        _ => return Err("the statement list has no array \"statements\"".into()),
    };
    let mut entries: Vec<StatementEntry> = Vec::new();
    for (i, item) in items.iter().enumerate() {
        let field = |key: &str| -> Result<String, String> {
            match item.get(key) {
                Some(J::Str(s)) if !s.is_empty() => Ok(s.clone()),
                _ => Err(format!("statement {i} of the list has no string {key:?}")),
            }
        };
        let label = field("label")?;
        if entries.iter().any(|e| e.label == label) {
            return Err(format!("the statement list has the label {label:?} twice"));
        }
        // `proved_by` is set only if it is a non-empty string; absent, null
        // or anything else counts as "no machine-checked proof".
        let proved_by = match item.get("proved_by") {
            Some(J::Str(s)) if !s.is_empty() => Some(s.clone()),
            _ => None,
        };
        entries.push(StatementEntry {
            label,
            name: field("name")?,
            commitment: field("commitment")?,
            proved_by,
        });
    }
    Ok(StatementList {
        sha256: sha256_hex(bytes),
        entries,
    })
}

/// What the contract fixes for a kind.
pub struct KindSpec {
    pub name: &'static str,
    pub label: Option<&'static str>,
    pub assumptions: &'static [&'static str],
    pub input_keys: &'static [&'static str],
}

pub const KINDS: [KindSpec; 4] = [
    KindSpec {
        name: "bessel-j",
        label: None,
        assumptions: &[],
        input_keys: &["n", "x"],
    },
    KindSpec {
        name: "lattice-population",
        label: Some("LS-K"),
        assumptions: &["bessel-identification", "single-site-datum"],
        input_keys: &["n", "t"],
    },
    KindSpec {
        name: "lattice-envelope",
        label: Some("LS-D"),
        assumptions: &["unit-l1-datum"],
        input_keys: &["d", "t"],
    },
    KindSpec {
        name: "vdc-hypothesis",
        label: Some("S1.k"),
        assumptions: &["amplitude-one"],
        input_keys: &["phase", "order", "a", "b", "mu", "t"],
    },
];

pub fn kind_spec(name: &str) -> Option<&'static KindSpec> {
    KINDS.iter().find(|k| k.name == name)
}

/// The checker's own text and rung for an assumption key (contract, section 4).
fn assumption_text(key: &str) -> (&'static str, &'static str) {
    match key {
        "bessel-identification" => (
            "I(t, n) = 2 pi i^n J_n(t) for the lattice kernel of the statements (DLMF 10.9.2)",
            "L3 on paper, validated at L2 (numerics/results-unlock-chain-checks-2026-11-16.txt, check K2); not machine-checked",
        ),
        "single-site-datum" => (
            "the initial datum is the unit vector at site 0 of the infinite lattice Z",
            "a modelling assumption",
        ),
        "unit-l1-datum" => (
            "the bound is for a datum of l^1 norm 1 on the infinite lattice Z^d; a device is finite",
            "a modelling assumption",
        ),
        "amplitude-one" => (
            "the bound is for the amplitude 1 on [a, b] and the phase t*omega(k) + xi*k, for every real xi",
            "a modelling assumption",
        ),
        _ => ("unknown assumption", "none"),
    }
}

/// The inputs of a certificate, typed.
#[derive(Debug, Clone)]
#[allow(clippy::large_enum_variant)] // one value per run; boxing would only obscure it
pub enum Inputs {
    Bessel {
        n: BigInt,
        x: BigRational,
    },
    Population {
        n: BigInt,
        t: BigRational,
    },
    Envelope {
        d: BigInt,
        t: BigRational,
    },
    Vdc {
        phase: Vec<PhaseTerm>,
        order: BigInt,
        a: BigRational,
        b: BigRational,
        mu: BigRational,
        t: BigRational,
    },
}

/// Collects the reasons found while reading a certificate.
#[derive(Default)]
pub struct Findings {
    /// rule 1: malformed, mismatching or outside the hypotheses
    pub rejected: Vec<String>,
    /// rule 5: outside the supported range or the budget
    pub unresolved: Vec<String>,
}

fn exact_keys(obj: &J, keys: &[&str], what: &str, f: &mut Findings) -> bool {
    let members = match obj {
        J::Obj(m) => m,
        other => {
            f.rejected
                .push(format!("{what} must be an object, not {}", other.type_name()));
            return false;
        }
    };
    let mut ok = true;
    for k in keys {
        if !members.iter().any(|(name, _)| name == k) {
            f.rejected.push(format!("{what}: missing key {k:?}"));
            ok = false;
        }
    }
    for (name, _) in members {
        if !keys.contains(&name.as_str()) {
            f.rejected.push(format!("{what}: unexpected key {name:?}"));
            ok = false;
        }
    }
    ok
}

fn get_rational(obj: &J, key: &str, what: &str, f: &mut Findings) -> Option<BigRational> {
    match obj.get(key) {
        None => None, // reported as a missing key
        Some(J::Str(s)) => match parse_rational(s) {
            Ok(r) => Some(r),
            Err(NumErr::Malformed(m)) => {
                f.rejected.push(format!("{what}.{key}: {m}"));
                None
            }
            Err(NumErr::Budget(m)) => {
                f.unresolved.push(format!("{what}.{key}: {m}"));
                None
            }
        },
        Some(other) => {
            f.rejected.push(format!(
                "{what}.{key} must be a string holding an exact rational, not {}",
                other.type_name()
            ));
            None
        }
    }
}

fn get_integer(obj: &J, key: &str, what: &str, f: &mut Findings) -> Option<BigInt> {
    match obj.get(key) {
        None => None,
        Some(v) => match v.as_integer() {
            Some(i) => Some(i),
            None => {
                let shape = if matches!(v, J::Num(_)) {
                    "a JSON number with a fraction or an exponent"
                } else {
                    v.type_name()
                };
                f.rejected
                    .push(format!("{what}.{key} must be a JSON integer, not {shape}"));
                None
            }
        },
    }
}

/// An enclosure object {"lo", "hi"} with lo <= hi.
fn get_enclosure(v: &J, what: &str, f: &mut Findings) -> Option<(BigRational, BigRational)> {
    if !exact_keys(v, &["lo", "hi"], what, f) {
        return None;
    }
    let lo = get_rational(v, "lo", what, f);
    let hi = get_rational(v, "hi", what, f);
    match (lo, hi) {
        (Some(lo), Some(hi)) => {
            if lo > hi {
                f.rejected.push(format!("{what}: lo is greater than hi"));
                None
            } else {
                Some((lo, hi))
            }
        }
        _ => None,
    }
}

fn int_from(i: i64) -> BigInt {
    BigInt::from(i)
}

fn rat_from(i: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(i))
}

/// Reads and classifies the inputs of a kind. Hypotheses of the cited
/// statement that fail (t = 0, k < 2, mu <= 0, t <= 0, a > b, d < 0, an
/// empty phase) are rule 1; limits of the checker (|x| > 400, d > 64,
/// k > 16, more than 64 terms, |freq| > 1000, |freq * end| > 64, |n| >
/// 10000) are rule 5.
pub fn read_inputs(spec: &KindSpec, inputs: &J, f: &mut Findings) -> Option<Inputs> {
    if !exact_keys(inputs, spec.input_keys, "inputs", f) {
        return None;
    }
    let w = "inputs";
    match spec.name {
        "bessel-j" => {
            let n = get_integer(inputs, "n", w, f);
            let x = get_rational(inputs, "x", w, f);
            let (n, x) = (n?, x?);
            if x.abs() > rat_from(X_MAX) {
                f.unresolved
                    .push(format!("inputs.x: |x| > {X_MAX} is outside the supported range"));
            }
            if n.abs() > BigInt::from(N_MAX) {
                f.unresolved
                    .push(format!("inputs.n: |n| > {N_MAX} is outside the checker's budget"));
            }
            Some(Inputs::Bessel { n, x })
        }
        "lattice-population" => {
            let n = get_integer(inputs, "n", w, f);
            let t = get_rational(inputs, "t", w, f);
            let (n, t) = (n?, t?);
            if (&t * rat_from(2)).abs() > rat_from(X_MAX) {
                f.unresolved.push(format!(
                    "inputs.t: |2t| > {X_MAX} is outside the supported range of J_n"
                ));
            }
            if n.abs() > BigInt::from(N_MAX) {
                f.unresolved
                    .push(format!("inputs.n: |n| > {N_MAX} is outside the checker's budget"));
            }
            Some(Inputs::Population { n, t })
        }
        "lattice-envelope" => {
            let d = get_integer(inputs, "d", w, f);
            let t = get_rational(inputs, "t", w, f);
            let (d, t) = (d?, t?);
            if t.is_zero() {
                f.rejected
                    .push("inputs.t: t = 0 is outside the hypotheses of LS-D (t != 0)".into());
            }
            if d.is_negative() {
                f.rejected
                    .push("inputs.d: a negative d is not a dimension".into());
            } else if d > int_from(64) {
                f.unresolved
                    .push("inputs.d: d > 64 is outside the supported range".into());
            }
            Some(Inputs::Envelope { d, t })
        }
        "vdc-hypothesis" => {
            let phase = read_phase(inputs.get("phase"), f);
            let order = get_integer(inputs, "order", w, f);
            let a = get_rational(inputs, "a", w, f);
            let b = get_rational(inputs, "b", w, f);
            let mu = get_rational(inputs, "mu", w, f);
            let t = get_rational(inputs, "t", w, f);
            let (phase, order, a, b, mu, t) = (phase?, order?, a?, b?, mu?, t?);
            if order < int_from(2) {
                f.rejected
                    .push("inputs.order: k < 2 is outside the hypotheses of S1.k (k >= 2)".into());
            } else if order > int_from(16) {
                f.unresolved
                    .push("inputs.order: k > 16 is outside the supported range".into());
            }
            if a > b {
                f.rejected
                    .push("inputs: a > b is outside the hypotheses (a <= b)".into());
            }
            if !mu.is_positive() {
                f.rejected
                    .push("inputs.mu: mu <= 0 is outside the hypotheses (mu > 0)".into());
            }
            if !t.is_positive() {
                f.rejected
                    .push("inputs.t: t <= 0 is outside the hypotheses (t > 0)".into());
            }
            if phase.is_empty() {
                f.rejected
                    .push("inputs.phase: a phase has at least one term".into());
            } else if phase.len() > 64 {
                f.unresolved
                    .push("inputs.phase: more than 64 terms is outside the supported range".into());
            }
            let limit = rat_from(64);
            let mut freq_range = false;
            let mut arg_range = false;
            for term in &phase {
                if term.freq.abs() > int_from(1000) {
                    freq_range = true;
                }
                let fr = BigRational::from_integer(term.freq.clone());
                if (&fr * &a).abs() > limit || (&fr * &b).abs() > limit {
                    arg_range = true;
                }
            }
            if freq_range {
                f.unresolved
                    .push("inputs.phase: |freq| > 1000 is outside the supported range".into());
            }
            if arg_range {
                f.unresolved.push(
                    "inputs.phase: |freq * a| or |freq * b| exceeds 64, outside the supported range".into(),
                );
            }
            Some(Inputs::Vdc {
                phase,
                order,
                a,
                b,
                mu,
                t,
            })
        }
        _ => None,
    }
}

fn read_phase(v: Option<&J>, f: &mut Findings) -> Option<Vec<PhaseTerm>> {
    let items = match v {
        None => return None,
        Some(J::Arr(items)) => items,
        Some(other) => {
            f.rejected.push(format!(
                "inputs.phase must be an array of terms, not {}",
                other.type_name()
            ));
            return None;
        }
    };
    let mut terms = Vec::new();
    let mut ok = true;
    for (i, item) in items.iter().enumerate() {
        let what = format!("inputs.phase[{i}]");
        if !exact_keys(item, &["amp", "freq", "fn"], &what, f) {
            ok = false;
            continue;
        }
        let amp = get_rational(item, "amp", &what, f);
        let freq = get_integer(item, "freq", &what, f);
        let is_cos = match item.get("fn") {
            Some(J::Str(s)) if s == "cos" => Some(true),
            Some(J::Str(s)) if s == "sin" => Some(false),
            _ => {
                f.rejected.push(format!("{what}.fn must be \"cos\" or \"sin\""));
                None
            }
        };
        match (amp, freq, is_cos) {
            (Some(amp), Some(freq), Some(is_cos)) => terms.push(PhaseTerm { amp, freq, is_cos }),
            _ => ok = false,
        }
    }
    if ok {
        Some(terms)
    } else {
        None
    }
}

/// The claim of a certificate, typed.
pub struct Claim {
    pub lo: BigRational,
    pub hi: BigRational,
}

/// The claim: an enclosure object for the three numeric kinds, and
/// {"holds": true, "bound": enclosure} for `vdc-hypothesis`.
fn read_claim(spec: &KindSpec, claim: &J, f: &mut Findings) -> Option<Claim> {
    if spec.name == "vdc-hypothesis" {
        if !exact_keys(claim, &["holds", "bound"], "claim", f) {
            return None;
        }
        let holds = match claim.get("holds") {
            Some(J::Bool(true)) => true,
            Some(J::Bool(false)) => {
                f.rejected
                    .push("claim.holds must be true: a certificate claims that the hypothesis holds".into());
                false
            }
            Some(other) => {
                f.rejected.push(format!(
                    "claim.holds must be the JSON value true, not {}",
                    other.type_name()
                ));
                false
            }
            None => false,
        };
        let bound = claim
            .get("bound")
            .and_then(|b| get_enclosure(b, "claim.bound", f));
        match (holds, bound) {
            (true, Some((lo, hi))) => Some(Claim { lo, hi }),
            _ => None,
        }
    } else {
        get_enclosure(claim, "claim", f).map(|(lo, hi)| Claim { lo, hi })
    }
}

/// The checker's enclosure of the quantity of a kind at `bits` of relative precision.
pub fn compute(inputs: &Inputs, bits: u64) -> Res<Iv> {
    match inputs {
        Inputs::Bessel { n, x } => bessel_j(n, x, bits),
        Inputs::Population { n, t } => population(n, t, bits),
        Inputs::Envelope { d, t } => {
            let d = d
                .to_u32()
                .ok_or_else(|| CalcError::Internal("d outside the range checked earlier".into()))?;
            envelope(d, t, bits)
        }
        Inputs::Vdc { order, mu, t, .. } => {
            let k = order
                .to_u32()
                .ok_or_else(|| CalcError::Internal("order outside the range checked earlier".into()))?;
            vdc_bound(k, t, mu, bits)
        }
    }
}

/// The verdict under construction.
struct Verdict<'a> {
    stmts: &'a StatementList,
    kind: Option<String>,
    spec: Option<&'static KindSpec>,
    recomputed: Value,
    hypothesis: Value,
}

impl Verdict<'_> {
    fn finish(&self, status: Status, reasons: Vec<String>) -> (Status, Value) {
        let entry = self.spec.and_then(|s| s.label).and_then(|l| self.stmts.find(l));
        let statement = match entry {
            Some(e) => json!({
                "label": e.label,
                "name": e.name,
                "commitment": e.commitment,
                "proved_by": e.proved_by,
                "rung": if e.proved_by.is_some() { STATEMENT_RUNG } else { STATEMENT_RUNG_UNPROVED },
            }),
            None => Value::Null,
        };
        let assumptions: Vec<Value> = self
            .spec
            .map(|s| s.assumptions)
            .unwrap_or(&[])
            .iter()
            .map(|key| {
                let (text, rung) = assumption_text(key);
                json!({"key": key, "text": text, "rung": rung})
            })
            .collect();
        let reasons = if status == Status::Certified {
            Vec::new()
        } else {
            reasons
        };
        let v = json!({
            "format": VERDICT_FORMAT,
            "status": status.as_str(),
            "kind": self.kind,
            "reasons": reasons,
            "checker": CHECKER,
            "statements_sha256": self.stmts.sha256,
            "statement": statement,
            "numeric_rung": NUMERIC_RUNG,
            "assumptions": assumptions,
            "recomputed": self.recomputed,
            "hypothesis": self.hypothesis,
        });
        (status, v)
    }
}

const CERT_KEYS: [&str; 7] = [
    "format",
    "kind",
    "statement",
    "inputs",
    "claim",
    "assumptions",
    "producer",
];

fn check_statement(spec: &KindSpec, stmt: &J, stmts: &StatementList, f: &mut Findings) {
    match spec.label {
        None => {
            if *stmt != J::Null {
                f.rejected
                    .push(format!("statement must be null for kind {:?}", spec.name));
            }
        }
        Some(label) => {
            if *stmt == J::Null {
                f.rejected.push(format!(
                    "statement must name {label} for kind {:?}, not null",
                    spec.name
                ));
                return;
            }
            if !exact_keys(stmt, &["label", "name", "commitment"], "statement", f) {
                return;
            }
            let field = |key: &str| match stmt.get(key) {
                Some(J::Str(s)) => Some(s.as_str()),
                _ => None,
            };
            let (Some(c_label), Some(c_name), Some(c_commitment)) =
                (field("label"), field("name"), field("commitment"))
            else {
                f.rejected
                    .push("statement: label, name and commitment must be strings".into());
                return;
            };
            if c_label != label {
                f.rejected.push(format!(
                    "statement.label is {c_label:?}; kind {:?} is about {label:?}",
                    spec.name
                ));
                return;
            }
            match stmts.find(label) {
                None => f
                    .rejected
                    .push(format!("statement {label:?} is not in the statement list")),
                Some(e) => {
                    if c_name != e.name {
                        f.rejected
                            .push("statement.name does not match the statement list".into());
                    }
                    if c_commitment != e.commitment {
                        f.rejected
                            .push("statement.commitment does not match the statement list".into());
                    }
                }
            }
        }
    }
}

fn check_assumptions(spec: &KindSpec, a: &J, f: &mut Findings) {
    let ok = match a {
        J::Arr(items) => {
            items.len() == spec.assumptions.len()
                && items
                    .iter()
                    .zip(spec.assumptions)
                    .all(|(x, want)| matches!(x, J::Str(s) if s == want))
        }
        _ => false,
    };
    if !ok {
        f.rejected.push(format!(
            "assumptions must be exactly {:?} for kind {:?}",
            spec.assumptions, spec.name
        ));
    }
}

fn enclosure_value(lo: &BigRational, hi: &BigRational) -> Value {
    json!({"lo": fmt_ratio(lo), "hi": fmt_ratio(hi)})
}

/// Checks one certificate against a statement list. Never panics on any
/// input; a failure inside the checker is reported as UNRESOLVED.
pub fn check(cert: &[u8], stmts: &StatementList) -> (Status, Value) {
    let mut v = Verdict {
        stmts,
        kind: None,
        spec: None,
        recomputed: Value::Null,
        hypothesis: Value::Null,
    };

    // ---- rule 1: the shape of the certificate ----
    let text = match std::str::from_utf8(cert) {
        Ok(t) => t,
        Err(_) => return v.finish(Status::Rejected, vec!["the certificate is not UTF-8 text".into()]),
    };
    let doc = match json::parse(text) {
        Ok(j) => j,
        Err(e) => {
            return v.finish(
                Status::Rejected,
                vec![format!("the certificate is malformed: {e}")],
            )
        }
    };
    let mut f = Findings::default();
    if !matches!(doc, J::Obj(_)) {
        return v.finish(
            Status::Rejected,
            vec![format!(
                "the certificate must be a JSON object, not {}",
                doc.type_name()
            )],
        );
    }
    exact_keys(&doc, &CERT_KEYS, "certificate", &mut f);
    match doc.get("format") {
        Some(J::Str(s)) if s == CERT_FORMAT => {}
        Some(_) => f
            .rejected
            .push(format!("format must be the string {CERT_FORMAT:?}")),
        None => {}
    }
    match doc.get("producer") {
        Some(J::Str(_)) | None => {}
        Some(other) => f
            .rejected
            .push(format!("producer must be a string, not {}", other.type_name())),
    }
    match doc.get("kind") {
        Some(J::Str(s)) => {
            v.kind = Some(s.clone());
            v.spec = kind_spec(s);
            if v.spec.is_none() {
                f.rejected.push(format!("unknown kind {s:?}"));
            }
        }
        Some(other) => f
            .rejected
            .push(format!("kind must be a string, not {}", other.type_name())),
        None => {}
    }
    let mut inputs: Option<Inputs> = None;
    let mut claim: Option<Claim> = None;
    if let Some(spec) = v.spec {
        if let Some(s) = doc.get("statement") {
            check_statement(spec, s, stmts, &mut f);
        }
        if let Some(a) = doc.get("assumptions") {
            check_assumptions(spec, a, &mut f);
        }
        if let Some(i) = doc.get("inputs") {
            inputs = read_inputs(spec, i, &mut f);
        }
        if let Some(c) = doc.get("claim") {
            claim = read_claim(spec, c, &mut f);
        }
    }
    if !f.rejected.is_empty() {
        return v.finish(Status::Rejected, f.rejected);
    }
    // ---- rule 5: supported range and budget of the inputs ----
    if !f.unresolved.is_empty() {
        return v.finish(Status::Unresolved, f.unresolved);
    }
    let (Some(spec), Some(inputs), Some(claim)) = (v.spec, inputs, claim) else {
        // unreachable when no reason was recorded; never certify on it
        return v.finish(
            Status::Unresolved,
            vec!["internal error: the certificate was not fully read".into()],
        );
    };

    // ---- rule 3: the hypothesis of vdc-hypothesis, decided first ----
    if let Inputs::Vdc {
        phase,
        order,
        a,
        b,
        mu,
        ..
    } = &inputs
    {
        let Some(k) = order.to_u32() else {
            return v.finish(
                Status::Unresolved,
                vec!["internal error: order out of range".into()],
            );
        };
        let h = decide_hypothesis(phase, k, a, b, mu, PIECE_BUDGET);
        v.hypothesis = json!({"status": h.status.as_str(), "detail": h.detail});
        match h.status {
            HypStatus::Pass => {}
            HypStatus::Fail => {
                return v.finish(
                    Status::Rejected,
                    vec!["the hypothesis |omega^(k)| >= mu on [a, b] fails at the point named in \"hypothesis\"".into()],
                );
            }
            HypStatus::Unresolved => {
                return v.finish(
                    Status::Unresolved,
                    vec![
                        "the hypothesis |omega^(k)| >= mu on [a, b] could not be decided within the budget"
                            .into(),
                    ],
                );
            }
        }
    }

    // ---- rule 2: the claimed enclosure against the checker's own ----
    let mut contained = false;
    for bits in [FIRST_PRECISION_BITS, 2 * FIRST_PRECISION_BITS] {
        let (lo, hi) = match compute(&inputs, bits).and_then(|iv| iv.to_ratios()) {
            Ok(r) => r,
            Err(e) => return v.finish(Status::Unresolved, vec![e.message()]),
        };
        if lo > hi {
            return v.finish(Status::Unresolved, vec!["internal error: empty enclosure".into()]);
        }
        v.recomputed = enclosure_value(&lo, &hi);
        if claim.lo <= lo && hi <= claim.hi {
            contained = true;
            break;
        }
        if hi < claim.lo || claim.hi < lo {
            return v.finish(
                Status::Rejected,
                vec![format!(
                    "the claimed enclosure is disjoint from the checker's enclosure (at {bits} bits)"
                )],
            );
        }
    }
    if !contained {
        return v.finish(
            Status::Unresolved,
            vec![format!(
                "the claimed enclosure neither contains nor is disjoint from the checker's enclosure, at {} and at {} bits",
                FIRST_PRECISION_BITS,
                2 * FIRST_PRECISION_BITS
            )],
        );
    }

    // ---- rule 4: the statement must have a machine-checked proof ----
    if let Some(label) = spec.label {
        match stmts.find(label) {
            Some(e) if e.proved_by.is_some() => {}
            _ => {
                return v.finish(
                    Status::Unresolved,
                    vec![format!("statement {label:?} has no machine-checked proof in the statement list (proved_by is not set)")],
                );
            }
        }
    }
    v.finish(Status::Certified, Vec::new())
}

/// Like [`check`], and turns a panic inside the checker into UNRESOLVED.
pub fn check_guarded(cert: &[u8], stmts: &StatementList) -> (Status, Value) {
    match std::panic::catch_unwind(|| check(cert, stmts)) {
        Ok(r) => r,
        Err(_) => {
            let v = Verdict {
                stmts,
                kind: None,
                spec: None,
                recomputed: Value::Null,
                hypothesis: Value::Null,
            };
            v.finish(
                Status::Unresolved,
                vec!["internal error: the checker panicked".into()],
            )
        }
    }
}

/// Builds a certificate for `kind` from `inputs` (JSON text). The claim is
/// the checker's own enclosure at 256 bits, rounded outward to `claim_bits`
/// significant bits. No certificate is made when the inputs are malformed
/// or out of range, or when the hypothesis is not proved.
pub fn make(kind: &str, inputs_text: &str, stmts: &StatementList, claim_bits: u64) -> Result<Value, String> {
    let spec = kind_spec(kind).ok_or_else(|| format!("unknown kind {kind:?}"))?;
    let inputs_j = json::parse(inputs_text).map_err(|e| format!("inputs: {e}"))?;
    let mut f = Findings::default();
    let inputs = read_inputs(spec, &inputs_j, &mut f);
    if !f.rejected.is_empty() || !f.unresolved.is_empty() {
        let mut all = f.rejected;
        all.extend(f.unresolved);
        return Err(all.join("; "));
    }
    let inputs = inputs.ok_or_else(|| "inputs could not be read".to_string())?;
    let statement = match spec.label {
        None => Value::Null,
        Some(label) => {
            let e = stmts
                .find(label)
                .ok_or_else(|| format!("statement {label:?} is not in the statement list"))?;
            json!({"label": e.label, "name": e.name, "commitment": e.commitment})
        }
    };
    if let Inputs::Vdc {
        phase,
        order,
        a,
        b,
        mu,
        ..
    } = &inputs
    {
        let k = order.to_u32().ok_or_else(|| "order out of range".to_string())?;
        let h = decide_hypothesis(phase, k, a, b, mu, PIECE_BUDGET);
        if h.status != HypStatus::Pass {
            return Err(format!("the hypothesis is {}: {}", h.status.as_str(), h.detail));
        }
    }
    let iv = compute(&inputs, FIRST_PRECISION_BITS).map_err(|e| e.message())?;
    let (lo, hi) = iv.round(claim_bits.max(8)).to_ratios().map_err(|e| e.message())?;
    let enclosure = enclosure_value(&lo, &hi);
    let claim = if spec.name == "vdc-hypothesis" {
        json!({"holds": true, "bound": enclosure})
    } else {
        enclosure
    };
    Ok(json!({
        "format": CERT_FORMAT,
        "kind": spec.name,
        "statement": statement,
        "inputs": j_to_value(&inputs_j),
        "claim": claim,
        "assumptions": spec.assumptions,
        "producer": CHECKER,
    }))
}

/// Re-serialises a strictly read JSON value, keeping number spellings.
fn j_to_value(j: &J) -> Value {
    match j {
        J::Null => Value::Null,
        J::Bool(b) => Value::Bool(*b),
        J::Num(raw) => serde_json::from_str::<Value>(raw).unwrap_or(Value::Null),
        J::Str(s) => Value::String(s.clone()),
        J::Arr(items) => Value::Array(items.iter().map(j_to_value).collect()),
        J::Obj(members) => Value::Object(members.iter().map(|(k, v)| (k.clone(), j_to_value(v))).collect()),
    }
}
