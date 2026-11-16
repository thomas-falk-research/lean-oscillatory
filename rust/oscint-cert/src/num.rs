//! Exact numbers for the checker: rationals parsed from the contract's
//! syntax, dyadic numbers `m * 2^e` with big-integer mantissa, and closed
//! intervals with dyadic end points and outward rounding.
//!
//! There is no floating point here. Every operation either is exact or
//! rounds the lower end point down and the upper end point up, so an
//! interval always contains the exact real result.

use num_bigint::{BigInt, Sign};
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::cmp::Ordering;

/// Why a computation did not produce an enclosure.
#[derive(Debug, Clone)]
pub enum CalcError {
    /// Outside the supported range or the computation budget (verdict: UNRESOLVED).
    Budget(String),
    /// An internal invariant failed (verdict: UNRESOLVED; never CERTIFIED).
    Internal(String),
}

impl CalcError {
    pub fn message(&self) -> String {
        match self {
            CalcError::Budget(s) => format!("outside the supported range or budget: {s}"),
            CalcError::Internal(s) => format!("internal error in the checker: {s}"),
        }
    }
}

pub type Res<T> = Result<T, CalcError>;

/// Longest accepted numeral (characters). Longer ones are a budget matter.
pub const MAX_NUMERAL_LEN: usize = 100_000;

/// Largest binary exponent (in modulus) the checker will turn into a
/// rational for comparison and printing.
pub const MAX_RESULT_EXP: i64 = 1 << 20;

/// Why a string is not an accepted number.
#[derive(Debug, Clone)]
pub enum NumErr {
    Malformed(String),
    Budget(String),
}

fn all_digits(b: &[u8]) -> bool {
    !b.is_empty() && b.iter().all(|c| c.is_ascii_digit())
}

fn digits_to_int(b: &[u8]) -> Result<BigInt, NumErr> {
    BigInt::parse_bytes(b, 10).ok_or_else(|| NumErr::Malformed("not a decimal integer".into()))
}

/// Parses the contract's exact rationals (section 2), strictly:
/// `-?D+`, `-?D+/D+` with a nonzero denominator, or `-?D+.D+`, where `D`
/// is an ASCII digit. No sign `+`, no spaces, no exponent, no underscore,
/// no sign on the denominator.
pub fn parse_rational(s: &str) -> Result<BigRational, NumErr> {
    if s.len() > MAX_NUMERAL_LEN {
        return Err(NumErr::Budget(format!(
            "a numeral of {} characters exceeds the budget of {}",
            s.len(),
            MAX_NUMERAL_LEN
        )));
    }
    let b = s.as_bytes();
    let (neg, body) = match b.first() {
        Some(b'-') => (true, &b[1..]),
        _ => (false, b),
    };
    let bad = || NumErr::Malformed(format!("{:?} is not an exact rational of the contract", short(s)));
    let value = if let Some(pos) = body.iter().position(|&c| c == b'/') {
        let (p, q) = (&body[..pos], &body[pos + 1..]);
        if !all_digits(p) || !all_digits(q) {
            return Err(bad());
        }
        let q = digits_to_int(q)?;
        if q.is_zero() {
            return Err(NumErr::Malformed("zero denominator".into()));
        }
        BigRational::new(digits_to_int(p)?, q)
    } else if let Some(pos) = body.iter().position(|&c| c == b'.') {
        let (i, f) = (&body[..pos], &body[pos + 1..]);
        if !all_digits(i) || !all_digits(f) {
            return Err(bad());
        }
        let mut digits = i.to_vec();
        digits.extend_from_slice(f);
        let den = num_traits::pow(BigInt::from(10u32), f.len());
        BigRational::new(digits_to_int(&digits)?, den)
    } else {
        if !all_digits(body) {
            return Err(bad());
        }
        BigRational::from_integer(digits_to_int(body)?)
    };
    Ok(if neg { -value } else { value })
}

fn short(s: &str) -> String {
    let mut t: String = s.chars().take(40).collect();
    if s.chars().count() > 40 {
        t.push('…');
    }
    t
}

/// Prints a rational in the contract's syntax: an integer or `p/q`.
pub fn fmt_ratio(r: &BigRational) -> String {
    if r.denom().is_one() {
        r.numer().to_string()
    } else {
        format!("{}/{}", r.numer(), r.denom())
    }
}

/// floor(m / 2^s).
pub fn shr_floor(m: &BigInt, s: u64) -> BigInt {
    if s == 0 || m.is_zero() {
        return m.clone();
    }
    if s >= m.bits() {
        // |m| < 2^s
        return if m.is_negative() {
            -BigInt::one()
        } else {
            BigInt::zero()
        };
    }
    if m.is_negative() {
        // floor(-a / 2^s) = -ceil(a / 2^s) = -((a + 2^s - 1) >> s) for a > 0
        let a = -m;
        -((a + ((BigInt::one() << s) - BigInt::one())) >> s)
    } else {
        m >> s
    }
}

/// ceil(m / 2^s).
pub fn shr_ceil(m: &BigInt, s: u64) -> BigInt {
    -shr_floor(&(-m), s)
}

/// ceil(a / b) for b > 0.
pub fn div_ceil(a: &BigInt, b: &BigInt) -> BigInt {
    -((-a).div_floor(b))
}

/// floor(n^(1/k)) for n >= 0 and k >= 1, and whether the root is exact.
///
/// Integer Newton iteration from above. The start 2^ceil(bits/k) is at
/// least the real root because n < 2^bits. For x above the real root the
/// step y = floor(((k-1)x + floor(n / x^(k-1))) / k) is smaller than x, and
/// by the inequality of the arithmetic and geometric means it is never
/// below floor(n^(1/k)); so the first x that does not decrease is the
/// floor. The result does not rest on that argument: it is verified by
/// x^k <= n < (x+1)^k before it is returned.
pub fn iroot(n: &BigInt, k: u32) -> Res<(BigInt, bool)> {
    if n.is_negative() || k == 0 {
        return Err(CalcError::Internal(
            "root of a negative number or of order 0".into(),
        ));
    }
    if n.is_zero() {
        return Ok((BigInt::zero(), true));
    }
    if k == 1 {
        return Ok((n.clone(), true));
    }
    let kk = BigInt::from(k);
    let km1 = BigInt::from(k - 1);
    let mut x = BigInt::one() << n.bits().div_ceil(u64::from(k));
    loop {
        let y = (&km1 * &x + n.div_floor(&x.pow(k - 1))).div_floor(&kk);
        if y >= x {
            break;
        }
        x = y;
    }
    let xk = x.pow(k);
    let x1k = (&x + BigInt::one()).pow(k);
    if !(xk <= *n && *n < x1k) {
        return Err(CalcError::Internal("integer root failed its verification".into()));
    }
    let exact = xk == *n;
    Ok((x, exact))
}

/// A dyadic number `m * 2^e`, exact.
#[derive(Debug, Clone)]
pub struct Fl {
    pub m: BigInt,
    pub e: i64,
}

impl Fl {
    pub fn zero() -> Fl {
        Fl {
            m: BigInt::zero(),
            e: 0,
        }
    }
    pub fn one() -> Fl {
        Fl {
            m: BigInt::one(),
            e: 0,
        }
    }
    pub fn from_int(i: &BigInt) -> Fl {
        Fl { m: i.clone(), e: 0 }
    }
    pub fn is_zero(&self) -> bool {
        self.m.is_zero()
    }
    pub fn is_neg(&self) -> bool {
        self.m.is_negative()
    }
    pub fn is_pos(&self) -> bool {
        self.m.is_positive()
    }
    /// For x != 0: 2^(top-1) <= |x| < 2^top.
    pub fn top(&self) -> i64 {
        self.e + self.m.bits() as i64
    }
    pub fn neg(&self) -> Fl {
        Fl {
            m: -&self.m,
            e: self.e,
        }
    }
    pub fn abs(&self) -> Fl {
        Fl {
            m: self.m.abs(),
            e: self.e,
        }
    }
    /// Exact sum.
    pub fn add(&self, o: &Fl) -> Fl {
        if self.m.is_zero() {
            return o.clone();
        }
        if o.m.is_zero() {
            return self.clone();
        }
        let e = self.e.min(o.e);
        let a = &self.m << ((self.e - e) as u64);
        let b = &o.m << ((o.e - e) as u64);
        Fl { m: a + b, e }
    }
    /// Exact difference.
    pub fn sub(&self, o: &Fl) -> Fl {
        self.add(&o.neg())
    }
    /// Exact product.
    pub fn mul(&self, o: &Fl) -> Fl {
        Fl {
            m: &self.m * &o.m,
            e: self.e + o.e,
        }
    }
    /// Exact multiplication by 2^k.
    pub fn shift(&self, k: i64) -> Fl {
        Fl {
            m: self.m.clone(),
            e: self.e + k,
        }
    }
    /// Rounds to at most `w` significant bits, up or down (towards +inf or -inf).
    pub fn round(&self, w: u64, up: bool) -> Fl {
        let b = self.m.bits();
        if b <= w {
            return self.clone();
        }
        let s = b - w;
        let m = if up {
            shr_ceil(&self.m, s)
        } else {
            shr_floor(&self.m, s)
        };
        Fl {
            m,
            e: self.e + s as i64,
        }
    }
    /// Exact comparison.
    pub fn compare(&self, o: &Fl) -> Ordering {
        let sa = self.m.sign();
        let sb = o.m.sign();
        if sa != sb {
            return sa.cmp(&sb);
        }
        if sa == Sign::NoSign {
            return Ordering::Equal;
        }
        let (ta, tb) = (self.top(), o.top());
        if ta != tb {
            // 2^(top-1) <= |x| < 2^top separates the moduli
            let mag = ta.cmp(&tb);
            return if sa == Sign::Plus { mag } else { mag.reverse() };
        }
        let e = self.e.min(o.e);
        let a = &self.m << ((self.e - e) as u64);
        let b = &o.m << ((o.e - e) as u64);
        a.cmp(&b)
    }
    pub fn le(&self, o: &Fl) -> bool {
        self.compare(o) != Ordering::Greater
    }
    pub fn lt(&self, o: &Fl) -> bool {
        self.compare(o) == Ordering::Less
    }
    pub fn ge(&self, o: &Fl) -> bool {
        self.compare(o) != Ordering::Less
    }
    pub fn min(&self, o: &Fl) -> Fl {
        if self.le(o) {
            self.clone()
        } else {
            o.clone()
        }
    }
    pub fn max(&self, o: &Fl) -> Fl {
        if self.ge(o) {
            self.clone()
        } else {
            o.clone()
        }
    }
    /// The exact rational value. The caller bounds the exponent first.
    pub fn to_ratio(&self) -> BigRational {
        if self.e >= 0 {
            BigRational::from_integer(&self.m << (self.e as u64))
        } else {
            BigRational::new(self.m.clone(), BigInt::one() << ((-self.e) as u64))
        }
    }
    /// A rational rounded to about `w` significant bits, up or down.
    pub fn from_ratio(r: &BigRational, w: u64, up: bool) -> Fl {
        let n = r.numer();
        let d = r.denom(); // positive: num-rational keeps the sign in the numerator
        if n.is_zero() {
            return Fl::zero();
        }
        let s: i64 = w as i64 + 2 + d.bits() as i64 - n.bits() as i64;
        let (num, den) = if s >= 0 {
            (n << (s as u64), d.clone())
        } else {
            (n.clone(), d << ((-s) as u64))
        };
        let q = if up {
            div_ceil(&num, &den)
        } else {
            num.div_floor(&den)
        };
        Fl { m: q, e: -s }.round(w, up)
    }
    /// a / b rounded to about `w` significant bits, up or down; b != 0.
    pub fn div(a: &Fl, b: &Fl, w: u64, up: bool) -> Res<Fl> {
        if b.m.is_zero() {
            return Err(CalcError::Internal("division by zero".into()));
        }
        if a.m.is_zero() {
            return Ok(Fl::zero());
        }
        let (am, bm) = if b.m.is_negative() {
            (-&a.m, -&b.m)
        } else {
            (a.m.clone(), b.m.clone())
        };
        let s: i64 = (w as i64 + 2 + bm.bits() as i64 - am.bits() as i64).max(0);
        let num = am << (s as u64);
        let q = if up {
            div_ceil(&num, &bm)
        } else {
            num.div_floor(&bm)
        };
        Ok(Fl {
            m: q,
            e: a.e - b.e - s,
        }
        .round(w, up))
    }
}

/// A closed interval [lo, hi] with dyadic end points, lo <= hi.
#[derive(Debug, Clone)]
pub struct Iv {
    pub lo: Fl,
    pub hi: Fl,
}

impl Iv {
    pub fn point(x: Fl) -> Iv {
        Iv { lo: x.clone(), hi: x }
    }
    pub fn zero() -> Iv {
        Iv::point(Fl::zero())
    }
    pub fn one() -> Iv {
        Iv::point(Fl::one())
    }
    pub fn from_i64(i: i64) -> Iv {
        Iv::point(Fl::from_int(&BigInt::from(i)))
    }
    pub fn from_int(i: &BigInt) -> Iv {
        Iv::point(Fl::from_int(i))
    }
    /// An enclosure of a rational with about `w` significant bits.
    pub fn from_ratio(r: &BigRational, w: u64) -> Iv {
        Iv {
            lo: Fl::from_ratio(r, w, false),
            hi: Fl::from_ratio(r, w, true),
        }
    }
    pub fn neg(&self) -> Iv {
        Iv {
            lo: self.hi.neg(),
            hi: self.lo.neg(),
        }
    }
    pub fn add(&self, o: &Iv, w: u64) -> Iv {
        Iv {
            lo: self.lo.add(&o.lo).round(w, false),
            hi: self.hi.add(&o.hi).round(w, true),
        }
    }
    pub fn sub(&self, o: &Iv, w: u64) -> Iv {
        Iv {
            lo: self.lo.sub(&o.hi).round(w, false),
            hi: self.hi.sub(&o.lo).round(w, true),
        }
    }
    pub fn mul(&self, o: &Iv, w: u64) -> Iv {
        if !self.lo.is_neg() && !o.lo.is_neg() {
            // both intervals lie in [0, inf)
            return Iv {
                lo: self.lo.mul(&o.lo).round(w, false),
                hi: self.hi.mul(&o.hi).round(w, true),
            };
        }
        let p = [
            self.lo.mul(&o.lo),
            self.lo.mul(&o.hi),
            self.hi.mul(&o.lo),
            self.hi.mul(&o.hi),
        ];
        let mut lo = &p[0];
        let mut hi = &p[0];
        for q in &p[1..] {
            if q.lt(lo) {
                lo = q;
            }
            if hi.lt(q) {
                hi = q;
            }
        }
        Iv {
            lo: lo.round(w, false),
            hi: hi.round(w, true),
        }
    }
    /// Multiplication by an exact integer.
    pub fn mul_int(&self, k: &BigInt, w: u64) -> Iv {
        self.mul(&Iv::from_int(k), w)
    }
    /// Division by a positive machine integer.
    pub fn div_u(&self, d: u64, w: u64) -> Res<Iv> {
        if d == 0 {
            return Err(CalcError::Internal("division by zero".into()));
        }
        let df = Fl::from_int(&BigInt::from(d));
        Ok(Iv {
            lo: Fl::div(&self.lo, &df, w, false)?,
            hi: Fl::div(&self.hi, &df, w, true)?,
        })
    }
    /// Division by an interval that does not contain zero.
    pub fn div(&self, o: &Iv, w: u64) -> Res<Iv> {
        if !(o.lo.is_pos() || o.hi.is_neg()) {
            return Err(CalcError::Internal(
                "division by an interval that contains zero".into(),
            ));
        }
        // x / y is monotone in x and in y separately when y keeps its sign,
        // so the extreme values are taken at the corners.
        let mut lo: Option<Fl> = None;
        let mut hi: Option<Fl> = None;
        for a in [&self.lo, &self.hi] {
            for b in [&o.lo, &o.hi] {
                let down = Fl::div(a, b, w, false)?;
                let up = Fl::div(a, b, w, true)?;
                lo = Some(match lo {
                    Some(l) => l.min(&down),
                    None => down,
                });
                hi = Some(match hi {
                    Some(h) => h.max(&up),
                    None => up,
                });
            }
        }
        match (lo, hi) {
            (Some(lo), Some(hi)) => Ok(Iv { lo, hi }),
            _ => Err(CalcError::Internal("empty corner set".into())),
        }
    }
    /// The square, as a set: { x^2 : x in self }.
    pub fn sqr(&self, w: u64) -> Iv {
        let a = self.lo.mul(&self.lo);
        let b = self.hi.mul(&self.hi);
        if !self.lo.is_neg() {
            Iv {
                lo: a.round(w, false),
                hi: b.round(w, true),
            }
        } else if !self.hi.is_pos() {
            Iv {
                lo: b.round(w, false),
                hi: a.round(w, true),
            }
        } else {
            Iv {
                lo: Fl::zero(),
                hi: a.max(&b).round(w, true),
            }
        }
    }
    /// The n-th power by repeated multiplication (an enclosure).
    pub fn powu(&self, n: u64, w: u64) -> Iv {
        let mut result = Iv::one();
        let mut base = self.clone();
        let mut k = n;
        while k > 0 {
            if k & 1 == 1 {
                result = result.mul(&base, w);
            }
            k >>= 1;
            if k > 0 {
                base = base.mul(&base, w);
            }
        }
        result
    }
    /// The k-th root of an interval in [0, inf): the integer root of a
    /// scaled mantissa, rounded down for the lower end and up for the upper.
    pub fn root(&self, k: u32, w: u64) -> Res<Iv> {
        Ok(Iv {
            lo: root_fl(&self.lo, k, w, false)?,
            hi: root_fl(&self.hi, k, w, true)?,
        })
    }
    pub fn hull(&self, o: &Iv) -> Iv {
        Iv {
            lo: self.lo.min(&o.lo),
            hi: self.hi.max(&o.hi),
        }
    }
    /// max |x| over the interval.
    pub fn mag(&self) -> Fl {
        self.lo.abs().max(&self.hi.abs())
    }
    /// min |x| over the interval.
    pub fn mig(&self) -> Fl {
        if self.lo.is_pos() {
            self.lo.clone()
        } else if self.hi.is_neg() {
            self.hi.neg()
        } else {
            Fl::zero()
        }
    }
    pub fn width(&self) -> Fl {
        self.hi.sub(&self.lo)
    }
    /// width <= 2^-t * min |x| (true for a point, false across zero).
    pub fn rel_width_ok(&self, t: u64) -> bool {
        let wd = self.width();
        if wd.is_zero() {
            return true;
        }
        wd.shift(t as i64).le(&self.mig())
    }
    /// Rounds both ends outward to `w` significant bits.
    pub fn round(&self, w: u64) -> Iv {
        Iv {
            lo: self.lo.round(w, false),
            hi: self.hi.round(w, true),
        }
    }
    /// The end points as exact rationals, if their exponents are in budget.
    pub fn to_ratios(&self) -> Res<(BigRational, BigRational)> {
        for x in [&self.lo, &self.hi] {
            if !x.is_zero() && (x.e.abs() > MAX_RESULT_EXP || x.top().abs() > MAX_RESULT_EXP) {
                return Err(CalcError::Budget(
                    "the enclosure has a binary exponent beyond 2^20 in modulus".into(),
                ));
            }
        }
        Ok((self.lo.to_ratio(), self.hi.to_ratio()))
    }
}

/// x^(1/k) for a dyadic x >= 0, rounded up or down.
///
/// Write x = m' * 2^(e') with e' divisible by k and m' = m * 2^s. Then
/// x^(1/k) = m'^(1/k) * 2^(e'/k), and floor(m'^(1/k)) <= m'^(1/k) <=
/// floor(m'^(1/k)) + 1 with equality on the left exactly when the integer
/// root is exact. The shift s makes m' at least k(w+2) bits long, so the
/// integer root has at least w+2 significant bits.
fn root_fl(x: &Fl, k: u32, w: u64, up: bool) -> Res<Fl> {
    if x.is_neg() {
        return Err(CalcError::Internal("root of a negative number".into()));
    }
    if x.is_zero() {
        return Ok(Fl::zero());
    }
    if k == 0 {
        return Err(CalcError::Internal("root of order 0".into()));
    }
    let need = i64::from(k) * (w as i64 + 2);
    let mut s: i64 = (need - x.m.bits() as i64).max(0);
    s += (x.e - s).rem_euclid(i64::from(k));
    let mp = &x.m << (s as u64);
    let (r, exact) = iroot(&mp, k)?;
    let m = if up && !exact { r + BigInt::one() } else { r };
    let e = x.e - s;
    if e % i64::from(k) != 0 {
        return Err(CalcError::Internal("root exponent not divisible".into()));
    }
    Ok(Fl {
        m,
        e: e / i64::from(k),
    }
    .round(w, up))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(s: &str) -> BigRational {
        match parse_rational(s) {
            Ok(r) => r,
            Err(e) => panic!("{s}: {e:?}"),
        }
    }

    #[test]
    fn rationals_accepted() {
        assert_eq!(rat("-3"), BigRational::from_integer(BigInt::from(-3)));
        assert_eq!(rat("0.25"), BigRational::new(BigInt::from(1), BigInt::from(4)));
        assert_eq!(rat("-0.5"), BigRational::new(BigInt::from(-1), BigInt::from(2)));
        assert_eq!(rat("6/4"), BigRational::new(BigInt::from(3), BigInt::from(2)));
        assert_eq!(rat("-7/2"), BigRational::new(BigInt::from(-7), BigInt::from(2)));
        assert_eq!(rat("007"), BigRational::from_integer(BigInt::from(7)));
        assert_eq!(rat("-0"), BigRational::from_integer(BigInt::from(0)));
    }

    #[test]
    fn rationals_rejected() {
        for s in [
            "",
            "-",
            "+1",
            " 1",
            "1 ",
            "1e3",
            "1E3",
            "1.5e2",
            ".5",
            "5.",
            "1/0",
            "1/-2",
            "1//2",
            "1/2/3",
            "1.2/3",
            "1/2.5",
            "0x10",
            "1_000",
            "NaN",
            "Infinity",
            "-Infinity",
            "inf",
            "١٢",
            "1.",
            "--1",
            "1/",
            "/2",
            "1,5",
            "abc",
        ] {
            assert!(
                matches!(parse_rational(s), Err(NumErr::Malformed(_))),
                "{s:?} must be rejected"
            );
        }
        let long = "1".repeat(MAX_NUMERAL_LEN + 1);
        assert!(matches!(parse_rational(&long), Err(NumErr::Budget(_))));
    }

    #[test]
    fn shifts_round_correctly() {
        for m in -40i64..=40 {
            for s in 0u64..8 {
                let b = BigInt::from(m);
                let d = BigInt::from(1i64 << s);
                assert_eq!(shr_floor(&b, s), b.div_floor(&d), "floor {m} >> {s}");
                assert_eq!(shr_ceil(&b, s), div_ceil(&b, &d), "ceil {m} >> {s}");
            }
        }
        assert_eq!(div_ceil(&BigInt::from(7), &BigInt::from(2)), BigInt::from(4));
        assert_eq!(div_ceil(&BigInt::from(-7), &BigInt::from(2)), BigInt::from(-3));
        assert_eq!(div_ceil(&BigInt::from(8), &BigInt::from(2)), BigInt::from(4));
    }

    #[test]
    fn integer_roots_bracket() {
        for k in 1u32..=7 {
            for n in 0u64..600 {
                let nn = BigInt::from(n);
                let (r, exact) = iroot(&nn, k).expect("root");
                assert!(r.pow(k) <= nn);
                assert!((&r + BigInt::one()).pow(k) > nn);
                assert_eq!(exact, r.pow(k) == nn);
            }
        }
        // a large case: (10^40 + 1)^16 - 1 has floor 16th root 10^40
        let base = num_traits::pow(BigInt::from(10u32), 40) + BigInt::one();
        let n = base.pow(16) - BigInt::one();
        let (r, exact) = iroot(&n, 16).expect("root");
        assert_eq!(r, &base - BigInt::one());
        assert!(!exact);
        let (r, exact) = iroot(&base.pow(16), 16).expect("root");
        assert_eq!(r, base);
        assert!(exact);
    }

    #[test]
    fn rounding_is_outward() {
        let r = rat("1/3");
        for w in [1u64, 2, 5, 64, 200] {
            let iv = Iv::from_ratio(&r, w);
            let (lo, hi) = iv.to_ratios().expect("in budget");
            assert!(lo < r && r < hi, "w = {w}");
            assert!(iv.rel_width_ok(w.saturating_sub(2)));
        }
        let x = Fl {
            m: BigInt::from(-1000001),
            e: -3,
        };
        assert!(x.round(5, false).le(&x) && x.le(&x.round(5, true)));
        assert!(x.round(5, false).m.bits() <= 5 + 1);
    }

    fn check_contains(iv: &Iv, r: &BigRational) {
        let (lo, hi) = iv.to_ratios().expect("in budget");
        assert!(lo <= *r && *r <= hi, "{lo} <= {r} <= {hi}");
    }

    #[test]
    fn interval_operations_contain_exact_results() {
        let vals = ["-7/3", "-1/9", "0", "2/7", "5", "123456789/1000"];
        for a in vals {
            for b in vals {
                let (ra, rb) = (rat(a), rat(b));
                for w in [3u64, 17, 80] {
                    let (ia, ib) = (Iv::from_ratio(&ra, w), Iv::from_ratio(&rb, w));
                    check_contains(&ia.add(&ib, w), &(&ra + &rb));
                    check_contains(&ia.sub(&ib, w), &(&ra - &rb));
                    check_contains(&ia.mul(&ib, w), &(&ra * &rb));
                    check_contains(&ia.sqr(w), &(&ra * &ra));
                    check_contains(&ia.powu(5, w), &(&ra * &ra * &ra * &ra * &ra));
                    if !rb.is_zero() {
                        check_contains(&ia.div(&ib, w).expect("div"), &(&ra / &rb));
                    }
                }
            }
        }
        let z = Iv {
            lo: Fl::from_int(&BigInt::from(-1)),
            hi: Fl::one(),
        };
        assert!(Iv::one().div(&z, 10).is_err());
        let s = z.sqr(10);
        assert!(s.lo.is_zero() && s.hi.compare(&Fl::one()) == Ordering::Equal);
    }

    #[test]
    fn comparison_is_exact() {
        let a = Fl {
            m: BigInt::from(3),
            e: -1,
        }; // 1.5
        let b = Fl {
            m: BigInt::from(6),
            e: -2,
        }; // 1.5
        let c = Fl {
            m: BigInt::from(13),
            e: -3,
        }; // 1.625
        assert_eq!(a.compare(&b), Ordering::Equal);
        assert_eq!(a.compare(&c), Ordering::Less);
        assert_eq!(c.neg().compare(&a.neg()), Ordering::Less);
        assert_eq!(Fl::zero().compare(&a.neg()), Ordering::Greater);
        assert_eq!(
            Fl {
                m: BigInt::zero(),
                e: 99
            }
            .compare(&Fl::zero()),
            Ordering::Equal
        );
        let tiny = Fl {
            m: BigInt::one(),
            e: -100000,
        };
        assert_eq!(tiny.compare(&a), Ordering::Less);
        assert_eq!(tiny.neg().compare(&a.neg()), Ordering::Greater);
    }

    /// A decimal string as a rational, for tests.
    fn dec(s: &str) -> BigRational {
        rat(s)
    }

    fn assert_close(iv: &Iv, value: &str, digits: usize) {
        let v = dec(value);
        let eps = BigRational::new(BigInt::one(), num_traits::pow(BigInt::from(10u32), digits));
        let (lo, hi) = iv.to_ratios().expect("in budget");
        assert!(
            lo >= &v - &eps && hi <= &v + &eps,
            "enclosure not within 1e-{digits} of {value}"
        );
        assert!(lo <= &v + &eps && hi >= &v - &eps);
    }

    #[test]
    fn roots_known_values() {
        let w = 160;
        // sqrt 2, cbrt 2, sqrt 7: classical constants
        let two = Iv::from_i64(2);
        assert_close(
            &two.root(2, w).expect("root"),
            "1.41421356237309504880168872420969807856967",
            38,
        );
        assert_close(
            &two.root(3, w).expect("root"),
            "1.25992104989487316476721060727822835057025",
            38,
        );
        assert_close(
            &Iv::from_i64(7).root(2, w).expect("root"),
            "2.64575131106459059050161575363926042571026",
            38,
        );
        // exact roots stay exact
        let r = Iv::from_ratio(&rat("81/16"), w).root(4, w).expect("root");
        let (lo, hi) = r.to_ratios().expect("in budget");
        assert_eq!(lo, rat("3/2"));
        assert_eq!(hi, rat("3/2"));
    }

    #[test]
    fn roots_bracket() {
        for k in 2u32..=16 {
            for s in ["1/1000000007", "3", "0.001", "123456789123456789", "17/19"] {
                let r = rat(s);
                for w in [8u64, 70] {
                    let iv = Iv::from_ratio(&r, w).root(k, w).expect("root");
                    let (lo, hi) = iv.to_ratios().expect("in budget");
                    assert!(
                        num_traits::pow(lo.clone(), k as usize) <= r,
                        "lower, k = {k}, {s}"
                    );
                    assert!(
                        num_traits::pow(hi.clone(), k as usize) >= r,
                        "upper, k = {k}, {s}"
                    );
                    assert!(iv.rel_width_ok(w - 6), "width, k = {k}, {s}, w = {w}");
                }
            }
        }
    }
}
