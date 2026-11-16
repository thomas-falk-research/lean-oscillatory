//! The checker of certificate contract 0.1, revision 3: reads a certificate
//! and a statement list, recomputes everything, and returns a verdict.
//!
//! Order of the decision (contract, section 5); the first rule that
//! decides, decides:
//!  1. structure: malformed input, a statement that does not match the
//!     list, wrong assumptions, an input outside the statement's
//!     hypotheses: REJECTED;
//!  2. supported range: an input beyond what the checker supports, or a
//!     computation beyond its budget: UNRESOLVED, and nothing is compared;
//!  3. for `vdc-hypothesis`, the hypothesis: FAIL is REJECTED, UNRESOLVED is
//!     UNRESOLVED;
//!  4. the claimed enclosure against the checker's own, at 256 and then at
//!     512 bits: disjoint is REJECTED, neither contained nor disjoint after
//!     the second pass is UNRESOLVED;
//!  5. a statement without a machine-checked proof in the list: UNRESOLVED;
//!  6. otherwise CERTIFIED.

use crate::bessel::{bessel_j, N_MAX, X_MAX};
use crate::json::{self, J};
use crate::num::{
    cmp_ratio_fl, fmt_ratio, read_numeral, CalcError, Iv, Numeral, Res, MAX_INPUT_NUMERAL_LEN,
    MAX_NUMERAL_LEN, MAX_RESULT_EXP,
};
use crate::quant::{
    decide_hypothesis, envelope, population, vdc_bound, vdc_bound_exact, HypStatus, PhaseTerm, PIECE_BUDGET,
};
use crate::sha256::sha256_hex;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, ToPrimitive};
use serde_json::{json, Value};
use std::cmp::Ordering;

pub const CHECKER: &str = concat!("oscint-cert-rs ", env!("CARGO_PKG_VERSION"));
pub const CERT_FORMAT: &str = "oscint-certificate/0.1";
pub const VERDICT_FORMAT: &str = "oscint-verdict/0.1";
pub const STATEMENTS_FORMAT: &str = "oscint-statements 1";

/// Relative precision, in bits, of the first comparison; the second uses twice as many.
pub const FIRST_PRECISION_BITS: u64 = 256;

/// A JSON integer of more digits than this is malformed (contract, section 2).
pub const MAX_INTEGER_DIGITS: usize = 300;

/// Most terms of a phase (contract, section 4).
pub const MAX_PHASE_TERMS: usize = 64;

/// The finest binary grid on which an enclosure is printed, in a verdict
/// and in a certificate made here: end points are multiples of 2^-12000
/// at the finest. A denominator 2^12000 has 3613 digits, so with a
/// numerator of up to 1000 bits the numeral stays within the 4000
/// characters of section 2, and what `make` writes `check` can read.
pub const PRINT_MIN_EXP: i64 = -12_000;

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
    /// SHA-256 of the bytes of the list, lower-case hexadecimal.
    pub sha256: String,
    pub entries: Vec<StatementEntry>,
    /// The list was required to have a given SHA-256 and has it
    /// (`--expect-statements-sha256`); the verdict's `statements_pinned`.
    pub pinned: bool,
}

impl StatementList {
    pub fn find(&self, label: &str) -> Option<&StatementEntry> {
        self.entries.iter().find(|e| e.label == label)
    }
}

/// Reads a statement list (format `oscint-statements 1`). An unusable list
/// is an input error of the command line (exit code 3), not a verdict:
/// text that is not strict JSON (also a byte-order mark, a duplicate key,
/// bytes that are not UTF-8), another format, no array `statements`, an
/// entry without a non-empty string `label`, `name` and `commitment`, or
/// two entries with one label.
pub fn load_statements(bytes: &[u8]) -> Result<StatementList, String> {
    load_statements_expecting(bytes, None)
}

/// Like [`load_statements`]; with `expected`, the list must have that
/// SHA-256 (64 hexadecimal digits, compared without regard to letter case)
/// and is then marked as pinned. The digest is compared before the list is
/// read.
pub fn load_statements_expecting(bytes: &[u8], expected: Option<&str>) -> Result<StatementList, String> {
    let sha256 = sha256_hex(bytes);
    if let Some(expected) = expected {
        if expected.len() != 64 || !expected.bytes().all(|c| c.is_ascii_hexdigit()) {
            return Err("the expected SHA-256 of the statement list must be 64 hexadecimal digits".into());
        }
        if !expected.eq_ignore_ascii_case(&sha256) {
            return Err(format!(
                "the statement list has SHA-256 {sha256}, not the expected {}",
                expected.to_ascii_lowercase()
            ));
        }
    }
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
        sha256,
        entries,
        pinned: expected.is_some(),
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
    /// rule 2: outside the supported range or the budget
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

/// A rational in a certificate. A numeral that is not of the contract's
/// forms is rule 1 (`None`, REJECTED). A well-formed numeral of more than
/// `limit` characters is rule 2 (UNRESOLVED): it is still returned, with
/// its sign and, up to [`MAX_NUMERAL_LEN`] characters, its value, so that
/// the tests of rule 1 that it enters (mu > 0, t != 0, a <= b, lo <= hi)
/// are made all the same; rule 1 comes first.
fn get_numeral(obj: &J, key: &str, what: &str, limit: usize, f: &mut Findings) -> Option<Numeral> {
    match obj.get(key) {
        None => None, // reported as a missing key
        Some(J::Str(s)) => match read_numeral(s) {
            Ok(n) => {
                if n.len > limit {
                    f.unresolved.push(format!(
                        "{what}.{key}: a numeral of {} characters is beyond the supported range (at most {limit})",
                        n.len
                    ));
                }
                Some(n)
            }
            Err(m) => {
                f.rejected.push(format!("{what}.{key}: {m}"));
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

/// The value of a numeral that was read and is short enough to have one.
fn value(n: &Option<Numeral>) -> Option<&BigRational> {
    n.as_ref().and_then(|n| n.value.as_ref())
}

/// `a > b`, when that can be told: from the values, or from the signs
/// alone when a numeral is too long to have a value.
fn certainly_greater(a: &Numeral, b: &Numeral) -> bool {
    match (&a.value, &b.value) {
        (Some(x), Some(y)) => x > y,
        _ => a.sign > b.sign,
    }
}

fn get_integer(obj: &J, key: &str, what: &str, f: &mut Findings) -> Option<BigInt> {
    match obj.get(key) {
        None => None,
        Some(v) => match v.as_integer() {
            Some(i) => {
                let digits = match v {
                    J::Num(raw) => raw.strip_prefix('-').unwrap_or(raw).len(),
                    _ => 0,
                };
                if digits > MAX_INTEGER_DIGITS {
                    f.rejected.push(format!(
                        "{what}.{key}: an integer of {digits} digits is malformed (at most {MAX_INTEGER_DIGITS})"
                    ));
                    return None;
                }
                Some(i)
            }
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
    let lo = get_numeral(v, "lo", what, MAX_NUMERAL_LEN, f);
    let hi = get_numeral(v, "hi", what, MAX_NUMERAL_LEN, f);
    let (lo, hi) = (lo?, hi?);
    if certainly_greater(&lo, &hi) {
        f.rejected.push(format!("{what}: lo is greater than hi"));
        return None;
    }
    Some((lo.value?, hi.value?))
}

fn int_from(i: i64) -> BigInt {
    BigInt::from(i)
}

fn rat_from(i: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(i))
}

/// Reads and classifies the inputs of a kind (contract, section 4).
/// Malformed inputs and hypotheses of the cited statement that fail (t = 0,
/// k < 2, mu <= 0, t <= 0, a > b, d < 0, an empty phase) are rule 1; limits
/// of the checker (a numeral of more than 100 characters, |x| > 400,
/// d > 64, k > 16, more than 64 terms, |freq| > 1000, |freq * end| > 64,
/// |n| > 10000) are rule 2. Every test of rule 1 that can be made is made,
/// whatever rule 2 has found, because rule 1 decides first.
///
/// Inputs are returned whenever they could all be read as numbers; the
/// caller must not compute with them unless both lists of findings are
/// empty.
pub fn read_inputs(spec: &KindSpec, inputs: &J, f: &mut Findings) -> Option<Inputs> {
    if !exact_keys(inputs, spec.input_keys, "inputs", f) {
        return None;
    }
    let w = "inputs";
    let limit = MAX_INPUT_NUMERAL_LEN;
    match spec.name {
        "bessel-j" => {
            let n = get_integer(inputs, "n", w, f);
            let x = get_numeral(inputs, "x", w, limit, f);
            if value(&x).is_some_and(|x| x.abs() > rat_from(X_MAX)) {
                f.unresolved
                    .push(format!("inputs.x: |x| > {X_MAX} is outside the supported range"));
            }
            if n.as_ref().is_some_and(|n| n.abs() > BigInt::from(N_MAX)) {
                f.unresolved
                    .push(format!("inputs.n: |n| > {N_MAX} is outside the checker's budget"));
            }
            Some(Inputs::Bessel { n: n?, x: x?.value? })
        }
        "lattice-population" => {
            let n = get_integer(inputs, "n", w, f);
            let t = get_numeral(inputs, "t", w, limit, f);
            if value(&t).is_some_and(|t| (t * rat_from(2)).abs() > rat_from(X_MAX)) {
                f.unresolved.push(format!(
                    "inputs.t: |2t| > {X_MAX} is outside the supported range of J_n"
                ));
            }
            if n.as_ref().is_some_and(|n| n.abs() > BigInt::from(N_MAX)) {
                f.unresolved
                    .push(format!("inputs.n: |n| > {N_MAX} is outside the checker's budget"));
            }
            Some(Inputs::Population { n: n?, t: t?.value? })
        }
        "lattice-envelope" => {
            let d = get_integer(inputs, "d", w, f);
            let t = get_numeral(inputs, "t", w, limit, f);
            if t.as_ref().is_some_and(|t| t.sign == 0) {
                f.rejected
                    .push("inputs.t: t = 0 is outside the hypotheses of LS-D (t != 0)".into());
            }
            if let Some(d) = &d {
                if d.is_negative() {
                    f.rejected
                        .push("inputs.d: a negative d is not a dimension".into());
                } else if *d > int_from(64) {
                    f.unresolved
                        .push("inputs.d: d > 64 is outside the supported range".into());
                }
            }
            Some(Inputs::Envelope { d: d?, t: t?.value? })
        }
        "vdc-hypothesis" => {
            let phase = read_phase(inputs.get("phase"), f);
            let order = get_integer(inputs, "order", w, f);
            let a = get_numeral(inputs, "a", w, limit, f);
            let b = get_numeral(inputs, "b", w, limit, f);
            let mu = get_numeral(inputs, "mu", w, limit, f);
            let t = get_numeral(inputs, "t", w, limit, f);
            if let Some(order) = &order {
                if *order < int_from(2) {
                    f.rejected
                        .push("inputs.order: k < 2 is outside the hypotheses of S1.k (k >= 2)".into());
                } else if *order > int_from(16) {
                    f.unresolved
                        .push("inputs.order: k > 16 is outside the supported range".into());
                }
            }
            if let (Some(a), Some(b)) = (&a, &b) {
                if certainly_greater(a, b) {
                    f.rejected
                        .push("inputs: a > b is outside the hypotheses (a <= b)".into());
                }
            }
            if mu.as_ref().is_some_and(|mu| mu.sign <= 0) {
                f.rejected
                    .push("inputs.mu: mu <= 0 is outside the hypotheses (mu > 0)".into());
            }
            if t.as_ref().is_some_and(|t| t.sign <= 0) {
                f.rejected
                    .push("inputs.t: t <= 0 is outside the hypotheses (t > 0)".into());
            }
            if let (Some(phase), Some(a), Some(b)) = (&phase, value(&a), value(&b)) {
                let limit = rat_from(64);
                let beyond = phase.iter().any(|term| {
                    let fr = BigRational::from_integer(term.freq.clone());
                    (&fr * a).abs() > limit || (&fr * b).abs() > limit
                });
                if beyond {
                    f.unresolved.push(
                        "inputs.phase: |freq * a| or |freq * b| exceeds 64, outside the supported range"
                            .into(),
                    );
                }
            }
            Some(Inputs::Vdc {
                phase: phase?,
                order: order?,
                a: a?.value?,
                b: b?.value?,
                mu: mu?.value?,
                t: t?.value?,
            })
        }
        _ => None,
    }
}

/// The phase: 1 to 64 terms {"amp", "freq", "fn"}. An amplitude may be as
/// long as any numeral ([`MAX_NUMERAL_LEN`] characters).
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
    if items.is_empty() {
        f.rejected
            .push("inputs.phase: a phase has at least one term".into());
    } else if items.len() > MAX_PHASE_TERMS {
        f.unresolved.push(format!(
            "inputs.phase: more than {MAX_PHASE_TERMS} terms is outside the supported range"
        ));
    }
    let mut terms = Vec::new();
    let mut ok = !items.is_empty();
    let mut freq_range = false;
    for (i, item) in items.iter().enumerate() {
        let what = format!("inputs.phase[{i}]");
        if !exact_keys(item, &["amp", "freq", "fn"], &what, f) {
            ok = false;
            continue;
        }
        let amp = get_numeral(item, "amp", &what, MAX_NUMERAL_LEN, f);
        let freq = get_integer(item, "freq", &what, f);
        let is_cos = match item.get("fn") {
            Some(J::Str(s)) if s == "cos" => Some(true),
            Some(J::Str(s)) if s == "sin" => Some(false),
            _ => {
                f.rejected.push(format!("{what}.fn must be \"cos\" or \"sin\""));
                None
            }
        };
        if freq.as_ref().is_some_and(|fr| fr.abs() > int_from(1000)) {
            freq_range = true;
        }
        match (amp.and_then(|a| a.value), freq, is_cos) {
            (Some(amp), Some(freq), Some(is_cos)) => terms.push(PhaseTerm { amp, freq, is_cos }),
            _ => ok = false,
        }
    }
    if freq_range {
        f.unresolved
            .push("inputs.phase: |freq| > 1000 is outside the supported range".into());
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

/// The checker's enclosure of a quantity as rule 4 uses it: an interval
/// with dyadic end points, or the exact value when it is a rational number
/// the checker can name (a van der Corput bound whose root is rational).
#[derive(Debug, Clone)]
pub enum Enclosure {
    Interval(Iv),
    Exact(BigRational),
}

impl Enclosure {
    /// The enclosure lies inside the closed interval [lo, hi].
    pub fn within(&self, lo: &BigRational, hi: &BigRational) -> bool {
        match self {
            Enclosure::Interval(iv) => {
                cmp_ratio_fl(lo, &iv.lo) != Ordering::Greater && cmp_ratio_fl(hi, &iv.hi) != Ordering::Less
            }
            Enclosure::Exact(v) => lo <= v && v <= hi,
        }
    }

    /// The enclosure and the closed interval [lo, hi] have no common point.
    pub fn disjoint(&self, lo: &BigRational, hi: &BigRational) -> bool {
        match self {
            Enclosure::Interval(iv) => {
                cmp_ratio_fl(lo, &iv.hi) == Ordering::Greater || cmp_ratio_fl(hi, &iv.lo) == Ordering::Less
            }
            Enclosure::Exact(v) => v < lo || hi < v,
        }
    }

    fn is_empty(&self) -> bool {
        match self {
            Enclosure::Interval(iv) => iv.hi.lt(&iv.lo),
            Enclosure::Exact(_) => false,
        }
    }

    /// The end points for printing: exact, except that an end point finer
    /// than 2^[`PRINT_MIN_EXP`] is rounded outward to that grid, so that
    /// no numeral printed is longer than a numeral the contract accepts
    /// (a value of J_10000 can be 10^-1000000). What is printed still
    /// contains the quantity; the comparison of rule 4 is made with the
    /// enclosure itself, not with what is printed.
    pub fn printed(&self) -> Res<(BigRational, BigRational)> {
        match self {
            Enclosure::Interval(iv) => {
                for x in [&iv.lo, &iv.hi] {
                    if !x.is_zero() && x.top() > MAX_RESULT_EXP {
                        return Err(CalcError::Budget(
                            "the enclosure has a binary exponent beyond 2^20".into(),
                        ));
                    }
                }
                Ok((
                    iv.lo.round_to_exp(PRINT_MIN_EXP, false).to_ratio(),
                    iv.hi.round_to_exp(PRINT_MIN_EXP, true).to_ratio(),
                ))
            }
            Enclosure::Exact(v) => Ok((v.clone(), v.clone())),
        }
    }
}

/// The enclosure rule 4 compares with the claim, at `bits` of relative
/// precision.
pub fn enclose(inputs: &Inputs, bits: u64) -> Res<Enclosure> {
    if let Inputs::Vdc { order, mu, t, .. } = inputs {
        let k = order
            .to_u32()
            .ok_or_else(|| CalcError::Internal("order outside the range checked earlier".into()))?;
        if let Some(v) = vdc_bound_exact(k, t, mu)? {
            return Ok(Enclosure::Exact(v));
        }
    }
    compute(inputs, bits).map(Enclosure::Interval)
}

/// The rule of section 5 that decided a verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stage {
    /// rule 1
    Structure,
    /// rule 2: an input in the UNRESOLVED column, or the budget
    Range,
    /// rule 3
    Hypothesis,
    /// rule 4
    Claim,
    /// rule 5: the statement has no machine-checked proof in the list
    Proof,
    /// rule 6
    Certified,
    /// a failure inside the checker (UNRESOLVED, never CERTIFIED)
    Internal,
}

/// The verdict under construction.
struct Verdict<'a> {
    stmts: &'a StatementList,
    certificate_sha256: String,
    kind: Option<String>,
    spec: Option<&'static KindSpec>,
    recomputed: Value,
    hypothesis: Value,
}

impl<'a> Verdict<'a> {
    fn new(cert: &[u8], stmts: &'a StatementList) -> Verdict<'a> {
        Verdict {
            stmts,
            certificate_sha256: sha256_hex(cert),
            kind: None,
            spec: None,
            recomputed: Value::Null,
            hypothesis: Value::Null,
        }
    }

    /// Every key of the contract's table is written in every verdict; what
    /// does not apply or was not reached is null.
    fn finish(&self, status: Status, stage: Stage, reasons: Vec<String>) -> (Status, Value, Stage) {
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
            "certificate_sha256": self.certificate_sha256,
            "statements_pinned": self.stmts.pinned,
        });
        (status, v, stage)
    }

    fn rejected(&self, reasons: Vec<String>) -> (Status, Value, Stage) {
        self.finish(Status::Rejected, Stage::Structure, reasons)
    }

    /// A failure of the computation: the budget is rule 2, anything else
    /// is a fault of the checker. Both are UNRESOLVED.
    fn failed(&self, e: &CalcError) -> (Status, Value, Stage) {
        let stage = match e {
            CalcError::Budget(_) => Stage::Range,
            CalcError::Internal(_) => Stage::Internal,
        };
        self.finish(Status::Unresolved, stage, vec![e.message()])
    }

    fn internal(&self, what: &str) -> (Status, Value, Stage) {
        self.finish(
            Status::Unresolved,
            Stage::Internal,
            vec![format!("internal error in the checker: {what}")],
        )
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
    let (status, verdict, _) = check_staged(cert, stmts);
    (status, verdict)
}

/// Like [`check`], and also names the rule that decided.
pub fn check_staged(cert: &[u8], stmts: &StatementList) -> (Status, Value, Stage) {
    let mut v = Verdict::new(cert, stmts);

    // ---- rule 1: structure ----
    let text = match std::str::from_utf8(cert) {
        Ok(t) => t,
        Err(_) => return v.rejected(vec!["the certificate is not UTF-8 text".into()]),
    };
    let doc = match json::parse(text) {
        Ok(j) => j,
        Err(e) => return v.rejected(vec![format!("the certificate is malformed: {e}")]),
    };
    let mut f = Findings::default();
    if !matches!(doc, J::Obj(_)) {
        return v.rejected(vec![format!(
            "the certificate must be a JSON object, not {}",
            doc.type_name()
        )]);
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
        return v.rejected(f.rejected);
    }
    // ---- rule 2: the supported range of the inputs; nothing is compared ----
    if !f.unresolved.is_empty() {
        return v.finish(Status::Unresolved, Stage::Range, f.unresolved);
    }
    let (Some(spec), Some(inputs), Some(claim)) = (v.spec, inputs, claim) else {
        // unreachable when no reason was recorded; never certify on it
        return v.internal("the certificate was not fully read");
    };

    // ---- rule 3: the hypothesis of vdc-hypothesis, before any bound is compared ----
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
            return v.internal("order out of range");
        };
        let h = decide_hypothesis(phase, k, a, b, mu, PIECE_BUDGET);
        v.hypothesis = json!({"status": h.status.as_str(), "detail": h.detail});
        match h.status {
            HypStatus::Pass => {}
            HypStatus::Fail => {
                return v.finish(
                    Status::Rejected,
                    Stage::Hypothesis,
                    vec!["the hypothesis |omega^(k)| >= mu on [a, b] fails at the point named in \"hypothesis\"".into()],
                );
            }
            HypStatus::Unresolved => {
                return v.finish(
                    Status::Unresolved,
                    Stage::Hypothesis,
                    vec![
                        "the hypothesis |omega^(k)| >= mu on [a, b] could not be decided within the budget"
                            .into(),
                    ],
                );
            }
        }
    }

    // ---- rule 4: the claimed enclosure against the checker's own ----
    let mut contained = false;
    for bits in [FIRST_PRECISION_BITS, 2 * FIRST_PRECISION_BITS] {
        let own = match enclose(&inputs, bits) {
            Ok(e) => e,
            Err(e) => return v.failed(&e),
        };
        if own.is_empty() {
            return v.internal("empty enclosure");
        }
        match own.printed() {
            Ok((lo, hi)) => v.recomputed = enclosure_value(&lo, &hi),
            Err(e) => return v.failed(&e),
        }
        // a claim of zero width is contained only in an enclosure that is
        // that very point: an exact value
        if own.within(&claim.lo, &claim.hi) {
            contained = true;
            break;
        }
        if own.disjoint(&claim.lo, &claim.hi) {
            return v.finish(
                Status::Rejected,
                Stage::Claim,
                vec![format!(
                    "the claimed enclosure is disjoint from the checker's enclosure (at {bits} bits)"
                )],
            );
        }
    }
    if !contained {
        return v.finish(
            Status::Unresolved,
            Stage::Claim,
            vec![format!(
                "the claimed enclosure neither contains nor is disjoint from the checker's enclosure, at {} and at {} bits",
                FIRST_PRECISION_BITS,
                2 * FIRST_PRECISION_BITS
            )],
        );
    }

    // ---- rule 5: the statement must have a machine-checked proof ----
    if let Some(label) = spec.label {
        match stmts.find(label) {
            Some(e) if e.proved_by.is_some() => {}
            _ => {
                return v.finish(
                    Status::Unresolved,
                    Stage::Proof,
                    vec![format!("statement {label:?} has no machine-checked proof in the statement list (proved_by is not set)")],
                );
            }
        }
    }
    // ---- rule 6 ----
    v.finish(Status::Certified, Stage::Certified, Vec::new())
}

/// Like [`check`], and turns a panic inside the checker into UNRESOLVED.
pub fn check_guarded(cert: &[u8], stmts: &StatementList) -> (Status, Value) {
    match std::panic::catch_unwind(|| check(cert, stmts)) {
        Ok(r) => r,
        Err(_) => {
            let (status, verdict, _) = Verdict::new(cert, stmts).internal("the checker panicked");
            (status, verdict)
        }
    }
}

/// Builds a certificate for `kind` from `inputs` (JSON text). The claim is
/// the checker's own enclosure at 256 bits, rounded outward to `claim_bits`
/// significant bits and to multiples of 2^[`PRINT_MIN_EXP`], so that its
/// numerals are within the length the contract accepts.
///
/// No certificate is made when the inputs are outside the tables of
/// section 4 (in either column), when the hypothesis fails (the message
/// names the point) or is undecided, or when the statement is not in the
/// list. The certificate is checked before it is returned: `make` returns
/// only what [`check`] certifies against the same list, the one exception
/// being a statement without a proof in that list (UNRESOLVED by rule 5).
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
    let iv = compute(&inputs, FIRST_PRECISION_BITS)
        .map_err(|e| e.message())?
        .round(claim_bits.max(8));
    let claimed = Enclosure::Interval(iv).printed().map_err(|e| e.message())?;
    let enclosure = enclosure_value(&claimed.0, &claimed.1);
    let claim = if spec.name == "vdc-hypothesis" {
        json!({"holds": true, "bound": enclosure})
    } else {
        enclosure
    };
    let cert = json!({
        "format": CERT_FORMAT,
        "kind": spec.name,
        "statement": statement,
        "inputs": j_to_value(&inputs_j),
        "claim": claim,
        "assumptions": spec.assumptions,
        "producer": CHECKER,
    });
    // The certificate must be one this checker certifies; the hypothesis
    // of a `vdc-hypothesis` certificate is decided here, once.
    let (status, verdict, stage) = check_staged(cert.to_string().as_bytes(), stmts);
    match (status, stage) {
        (Status::Certified, _) | (Status::Unresolved, Stage::Proof) => Ok(cert),
        (Status::Rejected, Stage::Hypothesis) => {
            let detail = &verdict["hypothesis"]["detail"];
            Err(format!(
                "the hypothesis |omega^(k)| >= mu on [a, b] fails at the point {}: {detail}",
                detail["point"].as_str().unwrap_or("named in the detail")
            ))
        }
        (_, Stage::Hypothesis) => Err(format!(
            "the hypothesis |omega^(k)| >= mu on [a, b] is undecided: {}",
            verdict["hypothesis"]["detail"]
        )),
        _ => Err(format!(
            "the certificate made is {} by this checker: {}",
            status.as_str(),
            verdict["reasons"]
        )),
    }
}

/// Re-serialises a strictly read JSON value, keeping number spellings.
fn j_to_value(j: &J) -> Value {
    match j {
        J::Null => Value::Null,
        J::Bool(b) => Value::Bool(*b),
        // an integer is written as an integer (`-0` as 0); the inputs that
        // reach a certificate have passed the range tests, so they fit
        J::Num(raw) => match j.as_integer().and_then(|i| i.to_i64()) {
            Some(i) => Value::from(i),
            None => serde_json::from_str::<Value>(raw).unwrap_or(Value::Null),
        },
        J::Str(s) => Value::String(s.clone()),
        J::Arr(items) => Value::Array(items.iter().map(j_to_value).collect()),
        J::Obj(members) => Value::Object(members.iter().map(|(k, v)| (k.clone(), j_to_value(v))).collect()),
    }
}
