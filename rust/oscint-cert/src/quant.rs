//! The quantities of the contract other than J_n itself: the lattice
//! population, the LS-D envelope, the van der Corput bound of S1.k, and the
//! decision of the hypothesis |omega^(k)| >= mu on [a, b].

use crate::bessel::bessel_j;
use crate::num::{fmt_ratio, CalcError, Fl, Iv, Res, MAX_RESULT_EXP};
use crate::trig::{pi_iv, Trig};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use serde_json::{json, Value};
use std::cmp::Ordering;
use std::collections::BinaryHeap;

/// J_n(2t)^2, relative width about 2^-(t_bits - 2).
pub fn population(n: &BigInt, t: &BigRational, t_bits: u64) -> Res<Iv> {
    let x = t * BigRational::from_integer(BigInt::from(2));
    let j = bessel_j(n, &x, t_bits + 4)?;
    Ok(j.sqr(t_bits + 68))
}

/// min{1, (C*/(2 pi))^d (2|t|)^(-d/3)} with C* = 8(1 + sqrt 7)/3, for
/// 0 <= d <= 64 and t != 0.
///
/// Every factor is positive, so B = (C*/(2 pi)) (1/(2|t|))^(1/3) is enclosed
/// by positive intervals, B^d by repeated multiplication, and the minimum
/// with 1 is taken end point by end point (x -> min(1, x) is monotone).
pub fn envelope(d: u32, t: &BigRational, t_bits: u64) -> Res<Iv> {
    if t.is_zero() {
        return Err(CalcError::Internal("envelope at t = 0".into()));
    }
    if d > 64 {
        return Err(CalcError::Budget("d exceeds 64".into()));
    }
    if d == 0 {
        return Ok(Iv::one()); // min{1, 1}
    }
    let w = t_bits + 64;
    let sqrt7 = Iv::from_i64(7).root(2, w)?;
    let c_star = Iv::one()
        .add(&sqrt7, w)
        .mul_int(&BigInt::from(8), w)
        .div_u(3, w)?;
    let two_pi = pi_iv(w).mul_int(&BigInt::from(2), w);
    let inv = BigRational::one() / (t.abs() * BigRational::from_integer(BigInt::from(2)));
    let cbrt = Iv::from_ratio(&inv, w).root(3, w)?;
    let b = c_star.div(&two_pi, w)?.mul(&cbrt, w);
    let p = b.powu(u64::from(d), w);
    if !p.lo.is_pos() {
        return Err(CalcError::Internal("envelope not positive".into()));
    }
    if p.hi.top() < -MAX_RESULT_EXP {
        return Err(CalcError::Budget("the envelope is below 2^-1048576".into()));
    }
    let one = Fl::one();
    Ok(Iv {
        lo: p.lo.min(&one),
        hi: p.hi.min(&one),
    })
}

/// (5 * 2^(k-1) - 2) (t mu)^(-1/k) for 2 <= k <= 16, t > 0, mu > 0.
pub fn vdc_bound(k: u32, t: &BigRational, mu: &BigRational, t_bits: u64) -> Res<Iv> {
    if !(2..=16).contains(&k) || !t.is_positive() || !mu.is_positive() {
        return Err(CalcError::Internal(
            "van der Corput bound outside its domain".into(),
        ));
    }
    let w = t_bits + 64;
    let inv = BigRational::one() / (t * mu);
    let root = Iv::from_ratio(&inv, w).root(k, w)?;
    let constant = BigInt::from(5) * (BigInt::one() << (k - 1)) - BigInt::from(2);
    let v = root.mul_int(&constant, w);
    if v.hi.top().abs() > MAX_RESULT_EXP {
        return Err(CalcError::Budget(
            "the bound has a binary exponent beyond 2^20".into(),
        ));
    }
    Ok(v)
}

/// One term amp * fn(freq * x) of a phase.
#[derive(Debug, Clone)]
pub struct PhaseTerm {
    pub amp: BigRational,
    pub freq: BigInt,
    pub is_cos: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HypStatus {
    Pass,
    Fail,
    Unresolved,
}

impl HypStatus {
    pub fn as_str(self) -> &'static str {
        match self {
            HypStatus::Pass => "PASS",
            HypStatus::Fail => "FAIL",
            HypStatus::Unresolved => "UNRESOLVED",
        }
    }
}

pub struct HypResult {
    pub status: HypStatus,
    pub detail: Value,
}

/// The default subdivision budget: pieces whose midpoint is evaluated.
pub const PIECE_BUDGET: usize = 4096;
/// Largest working precision for the hypothesis, in bits.
const HYP_W_CAP: u64 = 16_384;

/// One term c * T(f x) of g = omega^(k), with the matching term of g'.
struct GTerm {
    f: BigInt,
    /// coefficient in g
    c: Iv,
    /// g uses cos (true) or sin (false)
    g_cos: bool,
    /// coefficient in g'
    dc: Iv,
    /// g' uses cos (true) or sin (false)
    d_cos: bool,
}

struct Problem {
    terms: Vec<GTerm>,
    trig: Trig,
    w: u64,
    /// an enclosure of mu
    mu: Iv,
    /// an upper bound for sup |g''|, namely sum |c_j| f_j^2
    s2: Iv,
}

impl Problem {
    /// Enclosures of g(x) and g'(x) at a rational point x.
    fn eval(&self, x: &BigRational) -> Res<(Iv, Iv)> {
        let w = self.w;
        let mut g = Iv::zero();
        let mut d = Iv::zero();
        for t in &self.terms {
            let arg = Iv::from_ratio(&(BigRational::from_integer(t.f.clone()) * x), w);
            let co = self.trig.cos(&arg)?;
            let si = self.trig.sin(&arg)?;
            g = g.add(&t.c.mul(if t.g_cos { &co } else { &si }, w), w);
            d = d.add(&t.dc.mul(if t.d_cos { &co } else { &si }, w), w);
        }
        Ok((g, d))
    }

    /// Certified |g| < mu from an enclosure of g at a point.
    fn violates(&self, g: &Iv) -> bool {
        g.hi.lt(&self.mu.lo) && self.mu.lo.neg().lt(&g.lo)
    }

    /// Certified |g| >= mu from an enclosure of the range of g.
    fn satisfies(&self, range: &Iv) -> bool {
        range.lo.ge(&self.mu.hi) || range.hi.le(&self.mu.hi.neg())
    }
}

/// A piece [l, r] waiting to be examined, with g at its ends.
struct Piece {
    l: BigRational,
    r: BigRational,
    gl: Iv,
    gr: Iv,
    /// the smaller of min|g(l)|, min|g(r)|: pieces most likely to hold a
    /// violation are examined first
    key: Fl,
    seq: u64,
}

impl PartialEq for Piece {
    fn eq(&self, o: &Self) -> bool {
        self.cmp(o) == Ordering::Equal
    }
}
impl Eq for Piece {}
impl PartialOrd for Piece {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for Piece {
    fn cmp(&self, o: &Self) -> Ordering {
        // BinaryHeap is a max-heap: the smallest key must compare greatest
        o.key.compare(&self.key).then_with(|| o.seq.cmp(&self.seq))
    }
}

fn enclosure_json(iv: &Iv) -> Value {
    match iv.to_ratios() {
        Ok((lo, hi)) => json!({"lo": fmt_ratio(&lo), "hi": fmt_ratio(&hi)}),
        Err(_) => Value::Null,
    }
}

fn unresolved(reason: String, pieces: usize) -> HypResult {
    HypResult {
        status: HypStatus::Unresolved,
        detail: json!({"reason": reason, "pieces": pieces}),
    }
}

/// ceil(log2(r)) + 1 at most, for a positive rational; 0 for r <= 1/2.
fn log2_upper(r: &BigRational) -> u64 {
    let b = r.numer().bits() as i64 - r.denom().bits() as i64 + 1;
    b.max(0) as u64
}

/// Decides |omega^(k)(x)| >= mu for all x in [a, b], where
/// omega(x) = sum amp_j fn_j(freq_j x).
///
/// PASS is a proof by interval arithmetic on a finite cover of [a, b];
/// FAIL exhibits a rational point of [a, b] with a certified |omega^(k)| <
/// mu; anything else is UNRESOLVED. The caller has checked 2 <= k <= 16,
/// a <= b, mu > 0 and |freq * a|, |freq * b| <= 64.
///
/// With g = omega^(k) = sum c_j T_j(f_j x), T_j in {cos, sin}:
///  * g'(x) = sum c_j f_j T_j'(f_j x) and |g''(x)| <= S2 := sum |c_j| f_j^2.
///  * On a piece [l, r] with midpoint m and half-width h, the mean value
///    theorem gives g'(x) in g'(m) + [-S2 h, S2 h]. If that interval does
///    not contain 0 in its interior, g is monotone on the piece and its
///    range is the hull of g(l) and g(r).
///  * Otherwise Taylor's theorem with the Lagrange remainder gives
///    g(x) in g(m) + g'(m) [-h, h] + [-S2 h^2/2, S2 h^2/2].
///  * If every piece has |g| >= mu, then |g| >= mu on [a, b].
pub fn decide_hypothesis(
    phase: &[PhaseTerm],
    k: u32,
    a: &BigRational,
    b: &BigRational,
    mu: &BigRational,
    budget: usize,
) -> HypResult {
    match decide_inner(phase, k, a, b, mu, budget) {
        Ok(r) => r,
        Err(e) => unresolved(e.message(), 0),
    }
}

fn decide_inner(
    phase: &[PhaseTerm],
    k: u32,
    a: &BigRational,
    b: &BigRational,
    mu: &BigRational,
    budget: usize,
) -> Res<HypResult> {
    if !mu.is_positive() || a > b || k == 0 {
        return Err(CalcError::Internal("hypothesis outside its domain".into()));
    }
    // The k-th derivative of fn(f x) is f^k fn^(k)(f x), and the derivatives
    // of cos cycle through cos, -sin, -cos, sin; those of sin through
    // sin, cos, -sin, -cos.
    struct Exact {
        f: BigInt,
        c: BigRational,
        g_cos: bool,
    }
    let mut exact: Vec<Exact> = Vec::new();
    let mut s0 = BigRational::zero(); // sum |c_j|
    let mut s2 = BigRational::zero(); // sum |c_j| f_j^2
    for t in phase {
        let (sign, g_cos) = match (t.is_cos, k % 4) {
            (true, 0) => (1, true),
            (true, 1) => (-1, false),
            (true, 2) => (-1, true),
            (true, _) => (1, false),
            (false, 0) => (1, false),
            (false, 1) => (1, true),
            (false, 2) => (-1, false),
            (false, _) => (-1, true),
        };
        let fk = BigRational::from_integer(t.freq.pow(k) * BigInt::from(sign));
        let c = &t.amp * fk;
        if c.is_zero() {
            continue;
        }
        s0 += c.abs();
        s2 += c.abs() * BigRational::from_integer(&t.freq * &t.freq);
        exact.push(Exact {
            f: t.freq.clone(),
            c,
            g_cos,
        });
    }
    // Working precision: the absolute error of an evaluation of g is about
    // S0 * 2^-w, to be small against mu.
    let ratio = (&s0 + mu) / mu;
    let w = 128 + log2_upper(&ratio);
    if w > HYP_W_CAP {
        return Ok(unresolved(
            format!("the ratio of the coefficients to mu needs more than {HYP_W_CAP} bits"),
            0,
        ));
    }
    let terms: Vec<GTerm> = exact
        .iter()
        .map(|e| {
            let f = BigRational::from_integer(e.f.clone());
            // (c cos(f x))' = -c f sin(f x); (c sin(f x))' = c f cos(f x)
            let dc = if e.g_cos { -(&e.c * &f) } else { &e.c * &f };
            GTerm {
                f: e.f.clone(),
                c: Iv::from_ratio(&e.c, w),
                g_cos: e.g_cos,
                dc: Iv::from_ratio(&dc, w),
                d_cos: !e.g_cos,
            }
        })
        .collect();
    let p = Problem {
        terms,
        trig: Trig::new(w),
        w,
        mu: Iv::from_ratio(mu, w),
        s2: Iv::from_ratio(&s2, w),
    };
    let fail = |x: &BigRational, g: &Iv, pieces: usize| HypResult {
        status: HypStatus::Fail,
        detail: json!({
            "point": fmt_ratio(x),
            "value": enclosure_json(g),
            "mu": fmt_ratio(mu),
            "pieces": pieces,
            "reason": "the enclosure of the derivative at this point lies strictly inside (-mu, mu)",
        }),
    };
    let (ga, _) = p.eval(a)?;
    if p.violates(&ga) {
        return Ok(fail(a, &ga, 0));
    }
    if a == b {
        return Ok(if p.satisfies(&ga) {
            HypResult {
                status: HypStatus::Pass,
                detail: json!({"pieces": 0, "precision_bits": w}),
            }
        } else {
            unresolved(
                "the value at the single point a = b is too close to mu in modulus".into(),
                0,
            )
        });
    }
    let (gb, _) = p.eval(b)?;
    if p.violates(&gb) {
        return Ok(fail(b, &gb, 0));
    }
    let two = BigRational::from_integer(BigInt::from(2));
    let mut heap: BinaryHeap<Piece> = BinaryHeap::new();
    let mut seq: u64 = 0;
    let key = ga.mig().min(&gb.mig());
    heap.push(Piece {
        l: a.clone(),
        r: b.clone(),
        gl: ga,
        gr: gb,
        key,
        seq,
    });
    let mut examined: usize = 0;
    while let Some(piece) = heap.pop() {
        if examined >= budget {
            return Ok(unresolved(
                format!("the subdivision budget of {budget} pieces is exhausted"),
                examined,
            ));
        }
        examined += 1;
        let mid = (&piece.l + &piece.r) / &two;
        let (gm, dm) = p.eval(&mid)?;
        if p.violates(&gm) {
            return Ok(fail(&mid, &gm, examined));
        }
        let half = (&piece.r - &piece.l) / &two;
        let h = Iv::from_ratio(&half, w);
        // g' on the piece: g'(m) + [-S2 h, S2 h]
        let s2h = p.s2.mul(&h, w).hi;
        let dx = dm.add(
            &Iv {
                lo: s2h.neg(),
                hi: s2h.clone(),
            },
            w,
        );
        let range = if !dx.lo.is_neg() || !dx.hi.is_pos() {
            // monotone: the range is the hull of the values at the ends
            piece.gl.hull(&piece.gr)
        } else {
            // g(m) + g'(m) [-h, h] + [-S2 h^2 / 2, S2 h^2 / 2]
            let hh = Iv {
                lo: h.hi.neg(),
                hi: h.hi.clone(),
            };
            let quad = Fl::div(&s2h.mul(&h.hi), &Fl::from_int(&BigInt::from(2)), w, true)?;
            gm.add(&dm.mul(&hh, w), w).add(
                &Iv {
                    lo: quad.neg(),
                    hi: quad,
                },
                w,
            )
        };
        if p.satisfies(&range) {
            continue;
        }
        for (l, r, gl, gr) in [
            (piece.l.clone(), mid.clone(), piece.gl.clone(), gm.clone()),
            (mid.clone(), piece.r.clone(), gm.clone(), piece.gr.clone()),
        ] {
            seq += 1;
            let key = gl.mig().min(&gr.mig());
            heap.push(Piece {
                l,
                r,
                gl,
                gr,
                key,
                seq,
            });
        }
    }
    Ok(HypResult {
        status: HypStatus::Pass,
        detail: json!({"pieces": examined, "precision_bits": w}),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::num::parse_rational;

    fn rat(s: &str) -> BigRational {
        match parse_rational(s) {
            Ok(r) => r,
            Err(e) => panic!("{s}: {e:?}"),
        }
    }

    fn assert_close(iv: &Iv, value: &str, digits: usize) {
        let v = rat(value);
        let eps = BigRational::new(BigInt::one(), num_traits::pow(BigInt::from(10u32), digits));
        let (lo, hi) = iv.to_ratios().expect("in budget");
        assert!(lo <= hi);
        assert!(
            lo >= &v - &eps && hi <= &v + &eps,
            "enclosure not within 1e-{digits} of {value}"
        );
    }

    fn term(amp: &str, freq: i64, is_cos: bool) -> PhaseTerm {
        PhaseTerm {
            amp: rat(amp),
            freq: BigInt::from(freq),
            is_cos,
        }
    }

    fn decide(phase: &[PhaseTerm], k: u32, a: &str, b: &str, mu: &str) -> HypResult {
        decide_hypothesis(phase, k, &rat(a), &rat(b), &rat(mu), PIECE_BUDGET)
    }

    #[test]
    fn envelope_values() {
        // d = 0 is exactly 1; small |t| saturates at exactly 1
        for (d, t) in [(0u32, "5"), (1, "1"), (3, "-1/10"), (64, "1/1000000")] {
            let (lo, hi) = envelope(d, &rat(t), 128)
                .expect("envelope")
                .to_ratios()
                .expect("ok");
            assert!(lo == rat("1") && hi == rat("1"), "d = {d}, t = {t}");
        }
        // C*/(2 pi) = 8 (1 + sqrt 7) / (6 pi) = 1.547304...; at t = 1/2 the
        // factor (2|t|)^(-1/3) is 1, so the unclamped value is that constant
        // to the power d: clamped to 1. At t = 4: (C*/(2 pi)) / 2.
        // C* = 9.72200349617224..., 2 pi = 6.28318530717958...,
        // quotient 1.5473049..., half of it 0.7736524...
        let v = envelope(1, &rat("4"), 128).expect("envelope");
        let (lo, hi) = v.to_ratios().expect("ok");
        assert!(lo > rat("0.77365") && hi < rat("0.77366"), "{lo} {hi}");
        assert!(v.rel_width_ok(120));
        // symmetric in t, and the d-th power of the d = 1 value
        let vm = envelope(1, &rat("-4"), 128).expect("envelope");
        assert!(v.lo.compare(&vm.lo) == Ordering::Equal && v.hi.compare(&vm.hi) == Ordering::Equal);
        let v5 = envelope(5, &rat("4"), 128).expect("envelope");
        let p5 = v.powu(5, 200);
        assert!(v5.lo.le(&p5.hi) && p5.lo.le(&v5.hi));
        // decreasing in |t| and in d once below 1
        let far = envelope(2, &rat("1000"), 128).expect("envelope");
        let farther = envelope(2, &rat("1001"), 128).expect("envelope");
        assert!(farther.hi.lt(&far.lo));
        assert!(envelope(3, &rat("1000"), 128).expect("envelope").hi.lt(&far.lo));
        // an independent evaluation of the constant: (2 pi x)^2 scaled back.
        // x = C*/(2 pi) satisfies (3 pi x / 4 - 1)^2 = 7.
        let w = 200u64;
        let x = v.mul_int(&BigInt::from(2), w); // C*/(2 pi), from the value at t = 4
        let y = pi_iv(w)
            .mul(&x, w)
            .mul_int(&BigInt::from(3), w)
            .div_u(4, w)
            .expect("div");
        let z = y.sub(&Iv::one(), w).sqr(w);
        let (lo, hi) = z.to_ratios().expect("ok");
        assert!(lo <= rat("7") && rat("7") <= hi);
        assert!(&hi - &lo < rat("1/1000000000000000000000000000000"));
    }

    #[test]
    fn envelope_domain() {
        assert!(matches!(envelope(65, &rat("1"), 64), Err(CalcError::Budget(_))));
        assert!(envelope(1, &rat("0"), 64).is_err());
        // an astronomically small envelope is a budget matter, not a value
        let big = format!("1{}", "0".repeat(20_000));
        assert!(matches!(envelope(64, &rat(&big), 64), Err(CalcError::Budget(_))));
    }

    #[test]
    fn population_values() {
        // J_0(2)^2 with J_0(2) = 0.2238907791412356680518274546499486...
        let v = population(&BigInt::from(0), &rat("1"), 128).expect("population");
        let j0 = rat("0.223890779141235668051827454649948625825");
        let eps = rat("0.000000000000000000000000000000000001");
        let (lo, hi) = v.to_ratios().expect("ok");
        let (below, above) = (&j0 - &eps, &j0 + &eps);
        assert!(lo >= &below * &below && hi <= &above * &above);
        assert_close(&v, "0.05012708", 8);
        // t = 0: the datum itself
        let (lo, hi) = population(&BigInt::from(0), &rat("0"), 64)
            .expect("p")
            .to_ratios()
            .expect("ok");
        assert!(lo == rat("1") && hi == rat("1"));
        let (lo, hi) = population(&BigInt::from(3), &rat("0"), 64)
            .expect("p")
            .to_ratios()
            .expect("ok");
        assert!(lo.is_zero() && hi.is_zero());
        // populations are probabilities: the sum over sites is at most 1,
        // and the envelope squared dominates each of them
        let w = 200u64;
        for t in ["1/3", "2", "17/2"] {
            let mut sum = Iv::zero();
            let env = envelope(1, &rat(t), 128).expect("envelope").sqr(w);
            for n in -60i64..=60 {
                let pn = population(&BigInt::from(n), &rat(t), 128).expect("population");
                assert!(!pn.lo.is_neg());
                assert!(pn.lo.le(&env.hi), "envelope violated at n = {n}, t = {t}");
                sum = sum.add(&pn, w);
            }
            assert!(sum.lo.le(&Fl::one()), "sum of populations exceeds 1 at t = {t}");
        }
        assert!(matches!(
            population(&BigInt::from(0), &rat("200.5"), 64),
            Err(CalcError::Budget(_))
        ));
    }

    #[test]
    fn bound_values() {
        // k = 2, t mu = 1/4: (5*2 - 2) * 4^(1/2) = 16 exactly
        let (lo, hi) = vdc_bound(2, &rat("1/2"), &rat("1/2"), 128)
            .expect("b")
            .to_ratios()
            .expect("ok");
        assert!(lo == rat("16") && hi == rat("16"));
        // k = 3, t mu = 2: 18 / 2^(1/3) = 18 / 1.25992104989487316476721060727823
        //                 = 14.2866094535070...; checked by cubing instead
        let v = vdc_bound(3, &rat("4"), &rat("1/2"), 128).expect("b");
        let cube = v.powu(3, 300);
        let (lo, hi) = cube.to_ratios().expect("ok");
        assert!(lo <= rat("2916") && rat("2916") <= hi); // 18^3 / 2
        assert!(v.rel_width_ok(120));
        // k = 16: constant 5 * 2^15 - 2 = 163838
        let v = vdc_bound(16, &rat("1"), &rat("1"), 64).expect("b");
        let (lo, hi) = v.to_ratios().expect("ok");
        assert!(lo == rat("163838") && hi == rat("163838"));
        assert!(vdc_bound(1, &rat("1"), &rat("1"), 64).is_err());
        assert!(vdc_bound(2, &rat("0"), &rat("1"), 64).is_err());
    }

    #[test]
    fn hypothesis_simple_cases() {
        // omega = cos x, k = 2: omega'' = -cos x, |omega''| >= cos 1 on [0, 1]
        let ph = [term("1", 1, true)];
        assert_eq!(decide(&ph, 2, "0", "1", "0.54").status, HypStatus::Pass);
        let r = decide(&ph, 2, "0", "1", "0.5404");
        assert_eq!(r.status, HypStatus::Fail);
        assert_eq!(r.detail["point"], json!("1"));
        // a zero of the derivative inside the interval: FAIL for every mu
        let r = decide(&ph, 2, "0", "2", "1/1000000");
        assert_eq!(r.status, HypStatus::Fail);
        // odd order: omega''' = sin x, which vanishes at 0
        assert_eq!(decide(&ph, 3, "-1", "1", "0.01").status, HypStatus::Fail);
        assert_eq!(decide(&ph, 3, "1/2", "1", "0.479").status, HypStatus::Pass);
        assert_eq!(decide(&ph, 3, "1/2", "1", "0.48").status, HypStatus::Fail);
        // sine phases and frequencies: omega = sin 2x, k = 2: -4 sin 2x
        let ph = [term("1", 2, false)];
        assert_eq!(decide(&ph, 2, "1/2", "1", "3.3").status, HypStatus::Pass); // 4 sin 1 = 3.366
        assert_eq!(decide(&ph, 2, "1/2", "1", "3.37").status, HypStatus::Fail);
        // negative values pass as well: |g| >= mu with g < 0
        let ph = [term("-3", 1, true)];
        assert_eq!(decide(&ph, 4, "0", "1", "1.62").status, HypStatus::Pass); // -3 cos x
                                                                              // a zero phase derivative fails
        let ph = [term("0", 5, true), term("7", 0, false)];
        assert_eq!(decide(&ph, 2, "0", "1", "1/1000").status, HypStatus::Fail);
        // a single point
        let ph = [term("1", 1, true)];
        assert_eq!(decide(&ph, 2, "1", "1", "0.54").status, HypStatus::Pass);
        assert_eq!(decide(&ph, 2, "1", "1", "0.55").status, HypStatus::Fail);
    }

    /// omega = -cos x + cos(2x)/8 has omega'' = cos x - cos(2x)/2, whose
    /// minimum over [-1, 3/2] is 1/2, attained only at x = 0
    /// (g' = sin x (2 cos x - 1), g''(0) = 1 > 0; g(-1) = 0.748.., g(3/2) = 0.565..).
    fn near_degenerate_phase() -> [PhaseTerm; 2] {
        [term("-1", 1, true), term("1/8", 2, true)]
    }

    #[test]
    fn hypothesis_near_degenerate() {
        let ph = near_degenerate_phase();
        // threshold 1e-12 below the minimum: true, and provable
        let r = decide(&ph, 2, "-1", "3/2", "0.499999999999");
        assert_eq!(r.status, HypStatus::Pass, "{}", r.detail);
        // threshold 1e-12 above the minimum: false, never PASS
        let r = decide(&ph, 2, "-1", "3/2", "0.500000000001");
        assert_eq!(r.status, HypStatus::Fail, "{}", r.detail);
        let x = rat(r.detail["point"].as_str().expect("point"));
        assert!(x >= rat("-1") && x <= rat("3/2"));
        assert!(x.abs() < rat("1/100000"));
        // threshold equal to the minimum: true but not provable by
        // subdivision, and certainly not refutable
        let r = decide(&ph, 2, "-1", "3/2", "1/2");
        assert_eq!(r.status, HypStatus::Unresolved, "{}", r.detail);
        // much closer still
        let r = decide(&ph, 2, "-1", "3/2", "0.499999999999999999999999999999");
        assert_ne!(r.status, HypStatus::Fail);
        let r = decide(&ph, 2, "-1", "3/2", "0.500000000000000000000000000001");
        assert_ne!(r.status, HypStatus::Pass);
    }

    #[test]
    fn hypothesis_budget_is_respected() {
        let ph = near_degenerate_phase();
        let r = decide_hypothesis(&ph, 2, &rat("-1"), &rat("3/2"), &rat("0.499999999999"), 8);
        assert_eq!(r.status, HypStatus::Unresolved);
        assert_eq!(r.detail["pieces"], json!(8));
    }

    #[test]
    fn hypothesis_pass_is_never_contradicted_by_sampling() {
        // random small trigonometric polynomials; whenever the decision is
        // PASS, 201 sample points must all have an enclosure compatible
        // with |g| >= mu; whenever it is FAIL, the witness is re-evaluated.
        let mut state: u64 = 0x0123_4567_89AB_CDEF;
        let mut next = |modulus: u64| -> u64 {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (state >> 33) % modulus
        };
        let mut seen = [0usize; 3];
        for case in 0..60 {
            let n_terms = 1 + next(4) as usize;
            let mut ph = Vec::new();
            for _ in 0..n_terms {
                let amp = format!("{}/{}", next(41) as i64 - 20, 1 + next(7));
                ph.push(term(&amp, next(9) as i64 - 4, next(2) == 0));
            }
            let k = 2 + next(4) as u32;
            let a = BigRational::new(BigInt::from(next(33) as i64 - 16), BigInt::from(8));
            let b = &a + BigRational::new(BigInt::from(next(17)), BigInt::from(16));
            let mu = BigRational::new(BigInt::from(1 + next(60)), BigInt::from(20));
            let r = decide_hypothesis(&ph, k, &a, &b, &mu, PIECE_BUDGET);
            let w = 160u64;
            let trig = Trig::new(w);
            let g_at = |x: &BigRational| -> Iv {
                // an independent, direct evaluation of omega^(k)
                let mut g = Iv::zero();
                for t in &ph {
                    let arg = Iv::from_ratio(&(BigRational::from_integer(t.freq.clone()) * x), w);
                    let shift = if t.is_cos { k } else { k + 3 }; // sin y = cos(y - pi/2) = cos^(3)(y)
                    let val = match shift % 4 {
                        0 => trig.cos(&arg).expect("cos"),
                        1 => trig.sin(&arg).expect("sin").neg(),
                        2 => trig.cos(&arg).expect("cos").neg(),
                        _ => trig.sin(&arg).expect("sin"),
                    };
                    let c = &t.amp * BigRational::from_integer(t.freq.pow(k));
                    g = g.add(&Iv::from_ratio(&c, w).mul(&val, w), w);
                }
                g
            };
            let mu_iv = Iv::from_ratio(&mu, w);
            match r.status {
                HypStatus::Pass => {
                    seen[0] += 1;
                    for i in 0..=200u32 {
                        let x = &a + (&b - &a) * BigRational::new(BigInt::from(i), BigInt::from(200));
                        let g = g_at(&x);
                        // the enclosure must meet {|y| >= mu}
                        assert!(
                            g.hi.ge(&mu_iv.lo) || g.lo.le(&mu_iv.hi.neg()),
                            "case {case}: PASS contradicted at sample {i}"
                        );
                    }
                }
                HypStatus::Fail => {
                    seen[1] += 1;
                    let x = rat(r.detail["point"].as_str().expect("point"));
                    assert!(x >= a && x <= b, "case {case}: witness outside the interval");
                    let g = g_at(&x);
                    assert!(
                        g.hi.lt(&mu_iv.lo) && mu_iv.lo.neg().lt(&g.lo),
                        "case {case}: witness is not a certified violation"
                    );
                }
                HypStatus::Unresolved => seen[2] += 1,
            }
        }
        // the generator must exercise both decisions
        assert!(seen[0] >= 3 && seen[1] >= 3, "decisions seen: {seen:?}");
    }

    #[test]
    fn hypothesis_extreme_scales() {
        // huge and tiny coefficients against mu: decided or refused, never wrong
        let ph = [term("1000000000000000000000000000000", 1, true)];
        assert_eq!(decide(&ph, 2, "0", "1", "1").status, HypStatus::Pass);
        let ph = [term("0.000000000000000000000000000001", 1, true)];
        assert_eq!(decide(&ph, 2, "0", "1", "1").status, HypStatus::Fail);
        let tiny = format!("0.{}1", "0".repeat(6000));
        let ph = [term("1", 1, true)];
        let r = decide(&ph, 2, "0", "1", &tiny);
        assert_eq!(r.status, HypStatus::Unresolved);
    }
}
