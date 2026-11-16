//! Rigorous enclosures of pi, cosine and sine in fixed-point integer
//! arithmetic: a number x is held as the pair of integers
//! (floor-ish, ceil-ish) bounding x * 2^Q.

use crate::num::{div_ceil, shr_ceil, shr_floor, CalcError, Fl, Iv, Res};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

/// An enclosure [lo, hi] of 2^p * atan(1/n) for an integer n >= 2.
///
/// atan(1/n) = sum_{k>=0} (-1)^k / ((2k+1) n^(2k+1)). The terms are
/// positive, decrease and tend to 0, so by Leibniz's criterion the partial
/// sums through an even index are upper bounds and those through an odd
/// index are lower bounds. Each term is computed with a lower and an upper
/// integer bound (floor and ceiling divisions), and the two running sums
/// bound the exact partial sum from below and from above.
fn atan_inv(n: u32, p: u64) -> (BigInt, BigInt) {
    let n = BigInt::from(n);
    let n2 = &n * &n;
    let unit = BigInt::one() << p;
    // [ulo, uhi] encloses 2^p / n^(2k+1)
    let mut ulo = unit.div_floor(&n);
    let mut uhi = div_ceil(&unit, &n);
    let mut slo = BigInt::zero();
    let mut shi = BigInt::zero();
    let mut upper = shi.clone();
    let mut k: u64 = 0;
    loop {
        let d = BigInt::from(2 * k + 1);
        let tlo = ulo.div_floor(&d);
        let thi = div_ceil(&uhi, &d);
        if k % 2 == 0 {
            slo += &tlo;
            shi += &thi;
            upper = shi.clone(); // partial sum through an even index: an upper bound
        } else {
            slo -= &thi;
            shi -= &tlo;
            if thi <= BigInt::one() {
                // partial sum through an odd index: a lower bound
                return (slo, upper);
            }
        }
        ulo = ulo.div_floor(&n2);
        uhi = div_ceil(&uhi, &n2);
        k += 1;
    }
}

/// An enclosure [lo, hi] of 2^q * pi, by Machin's formula
/// pi = 16 atan(1/5) - 4 atan(1/239), with 16 guard bits.
pub fn pi_fx(q: u64) -> (BigInt, BigInt) {
    let p = q + 16;
    let (a_lo, a_hi) = atan_inv(5, p);
    let (b_lo, b_hi) = atan_inv(239, p);
    let lo = BigInt::from(16) * a_lo - BigInt::from(4) * b_hi;
    let hi = BigInt::from(16) * a_hi - BigInt::from(4) * b_lo;
    (shr_floor(&lo, 16), shr_ceil(&hi, 16))
}

/// The square of the integer interval [lo, hi], as a set.
fn sqr_int(lo: &BigInt, hi: &BigInt) -> (BigInt, BigInt) {
    let a = lo * lo;
    let b = hi * hi;
    if !lo.is_negative() {
        (a, b)
    } else if !hi.is_positive() {
        (b, a)
    } else {
        (BigInt::zero(), a.max(b))
    }
}

/// Cosine and sine at a fixed binary precision.
pub struct Trig {
    /// Number of fractional bits of the arguments and results.
    pub q: u64,
    pi_lo: BigInt,
    pi_hi: BigInt,
}

impl Trig {
    pub fn new(q: u64) -> Trig {
        let (pi_lo, pi_hi) = pi_fx(q);
        Trig { q, pi_lo, pi_hi }
    }

    /// An enclosure of pi.
    pub fn pi(&self) -> Iv {
        let e = -(self.q as i64);
        Iv {
            lo: Fl {
                m: self.pi_lo.clone(),
                e,
            },
            hi: Fl {
                m: self.pi_hi.clone(),
                e,
            },
        }
    }

    fn to_fx(&self, x: &Fl, up: bool) -> BigInt {
        let s = x.e + self.q as i64;
        if s >= 0 {
            &x.m << (s as u64)
        } else if up {
            shr_ceil(&x.m, (-s) as u64)
        } else {
            shr_floor(&x.m, (-s) as u64)
        }
    }

    /// An enclosure, at scale 2^-q, of cos y for every y with
    /// ylo <= y * 2^q <= yhi. Requires |y| < 256.
    ///
    /// Argument reduction: r = y / 2^m with |r| < 2^-s, s about sqrt(q) and
    /// at least 4, then m applications of cos 2a = 2 cos^2 a - 1. (With s
    /// near sqrt(q) the series needs about sqrt(q)/2 terms and there are
    /// about sqrt(q) doublings, which is what makes a cosine at 14000 bits
    /// affordable.) Each doubling at most quadruples the width
    /// (|d(2c^2-1)/dc| = 4|c| <= 4), hence the 2m + 16 guard bits; the
    /// rigour does not depend on that count, nor on s, because every step
    /// is carried out on an interval with outward rounding.
    ///
    /// Series: cos r = sum_{j=0}^{N} (-1)^j r^(2j)/(2j)! + R_N with
    /// |R_N| <= r^(2N+2)/(2N+2)!, by Taylor's theorem with the Lagrange
    /// remainder, since every derivative of cos is bounded by 1. So the
    /// first omitted term bounds the remainder, for every real r.
    fn cos_fx(&self, ylo: &BigInt, yhi: &BigInt) -> Res<(BigInt, BigInt)> {
        if ylo > yhi {
            return Err(CalcError::Internal("empty argument interval".into()));
        }
        let q = self.q;
        if q < 8 {
            return Err(CalcError::Internal("precision too small for the cosine".into()));
        }
        let amax = ylo.abs().max(yhi.abs());
        if amax.bits() > q + 8 {
            return Err(CalcError::Budget(
                "argument of a cosine or sine of modulus 256 or more".into(),
            ));
        }
        // s = max(4, floor(sqrt(q))) <= q / 2 because q >= 8
        let mut s: u64 = 4;
        while (s + 1) * (s + 1) <= q {
            s += 1;
        }
        // amax < 2^bits, so amax / 2^m < 2^(q-s): |r| < 2^-s
        let m = amax.bits().saturating_sub(q - s);
        let g = q + 2 * m + 16;
        let unit = BigInt::one() << g;
        // r * 2^g = y * 2^q * 2^(g - q - m), exactly
        let up = g - q - m;
        let rlo = ylo << up;
        let rhi = yhi << up;
        let (s_lo, s_hi) = sqr_int(&rlo, &rhi);
        let ulo = shr_floor(&s_lo, g);
        let uhi = shr_ceil(&s_hi, g);
        // [tlo, thi] encloses r^(2j)/(2j)! * 2^g; [slo, shi] the partial sum
        let mut tlo = unit.clone();
        let mut thi = unit.clone();
        let mut slo = unit.clone();
        let mut shi = unit.clone();
        let mut j: u64 = 0;
        loop {
            let d = BigInt::from((2 * j + 1) * (2 * j + 2));
            tlo = shr_floor(&(&tlo * &ulo), g).div_floor(&d);
            thi = div_ceil(&shr_ceil(&(&thi * &uhi), g), &d);
            j += 1;
            if thi <= BigInt::one() {
                // the term of index j is omitted; it bounds the remainder
                slo -= &thi;
                shi += &thi;
                break;
            }
            if j % 2 == 1 {
                slo -= &thi;
                shi -= &tlo;
            } else {
                slo += &tlo;
                shi += &thi;
            }
            if j > 10_000 {
                return Err(CalcError::Internal("cosine series did not terminate".into()));
            }
        }
        let neg_unit = -&unit;
        for _ in 0..m {
            let (a, b) = sqr_int(&slo, &shi);
            slo = (shr_floor(&a, g) << 1u32) - &unit;
            shi = (shr_ceil(&b, g) << 1u32) - &unit;
            // the true value lies in [-1, 1] as well
            if slo < neg_unit {
                slo = neg_unit.clone();
            }
            if shi > unit {
                shi = unit.clone();
            }
        }
        if slo < neg_unit {
            slo = neg_unit.clone();
        }
        if shi > unit {
            shi = unit.clone();
        }
        if slo > shi {
            return Err(CalcError::Internal("cosine enclosure became empty".into()));
        }
        Ok((shr_floor(&slo, g - q), shr_ceil(&shi, g - q)))
    }

    fn fx_iv(&self, lo: BigInt, hi: BigInt) -> Iv {
        let e = -(self.q as i64);
        Iv {
            lo: Fl { m: lo, e },
            hi: Fl { m: hi, e },
        }
    }

    fn check_range(y: &Iv) -> Res<()> {
        for x in [&y.lo, &y.hi] {
            if !x.is_zero() && x.top() > 7 {
                return Err(CalcError::Budget(
                    "argument of a cosine or sine of modulus 128 or more".into(),
                ));
            }
        }
        Ok(())
    }

    /// An enclosure of { cos y : y in the interval }, absolute width about
    /// 2^-q plus the width of the argument. Requires |y| < 128.
    pub fn cos(&self, y: &Iv) -> Res<Iv> {
        Self::check_range(y)?;
        let (lo, hi) = self.cos_fx(&self.to_fx(&y.lo, false), &self.to_fx(&y.hi, true))?;
        Ok(self.fx_iv(lo, hi))
    }

    /// An enclosure of { sin y : y in the interval }, from
    /// sin y = cos(y - pi/2) and the enclosure of pi. Requires |y| < 128.
    pub fn sin(&self, y: &Iv) -> Res<Iv> {
        Self::check_range(y)?;
        let half_pi_lo = shr_floor(&self.pi_lo, 1);
        let half_pi_hi = shr_ceil(&self.pi_hi, 1);
        let lo = self.to_fx(&y.lo, false) - half_pi_hi;
        let hi = self.to_fx(&y.hi, true) - half_pi_lo;
        let (lo, hi) = self.cos_fx(&lo, &hi)?;
        Ok(self.fx_iv(lo, hi))
    }
}

/// An enclosure of pi with about `w` significant bits.
pub fn pi_iv(w: u64) -> Iv {
    Trig::new(w + 4).pi()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::num::parse_rational;
    use num_rational::BigRational;

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

    const PI_50: &str = "3.14159265358979323846264338327950288419716939937510";

    #[test]
    fn pi_known_value_and_nesting() {
        assert_close(&Trig::new(200).pi(), PI_50, 49);
        // enclosures at different precisions must overlap (both contain pi)
        let mut prev: Option<(BigRational, BigRational)> = None;
        for q in [8u64, 9, 30, 64, 65, 127, 300, 1000] {
            let (lo, hi) = Trig::new(q).pi().to_ratios().expect("in budget");
            assert!(lo < hi);
            let width_bound = BigRational::new(BigInt::from(8), BigInt::one() << q);
            assert!(&hi - &lo <= width_bound, "pi width at q = {q}");
            if let Some((plo, phi)) = &prev {
                assert!(lo <= *phi && *plo <= hi, "pi enclosures disjoint at q = {q}");
            }
            prev = Some((lo, hi));
        }
    }

    #[test]
    fn cos_sin_known_values() {
        let t = Trig::new(160);
        let one = Iv::from_i64(1);
        assert_close(
            &t.cos(&one).expect("cos"),
            "0.54030230586813971740093660744297660373231",
            38,
        );
        assert_close(
            &t.sin(&one).expect("sin"),
            "0.84147098480789650665250232163029899962256",
            38,
        );
        // cos 0 = 1 and sin 0 = 0
        assert_close(&t.cos(&Iv::zero()).expect("cos"), "1", 40);
        assert_close(&t.sin(&Iv::zero()).expect("sin"), "0", 40);
        // sin(1/2) and cos(1/2)
        let half = Iv::from_ratio(&rat("1/2"), 200);
        assert_close(
            &t.sin(&half).expect("sin"),
            "0.47942553860420300027328793521557138808180",
            38,
        );
        assert_close(
            &t.cos(&half).expect("cos"),
            "0.87758256189037271611628158260382965199164",
            38,
        );
    }

    #[test]
    fn cos_sin_properties() {
        let q = 128u64;
        let t = Trig::new(q);
        let w = 200u64;
        let tol = BigRational::new(BigInt::one(), BigInt::one() << 100u32);
        // a fixed pseudo-random sequence of rationals in [-64, 64]
        let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
        for _ in 0..200 {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let num = (state >> 20) as i64 % 64_000_001 - 32_000_000;
            let x = BigRational::new(BigInt::from(num), BigInt::from(500_000));
            let xi = Iv::from_ratio(&x, w);
            let c = t.cos(&xi).expect("cos");
            let s = t.sin(&xi).expect("sin");
            for v in [&c, &s] {
                let (lo, hi) = v.to_ratios().expect("in budget");
                assert!(lo <= hi);
                assert!(lo >= rat("-1") && hi <= rat("1"));
                assert!(&hi - &lo <= tol, "width at x = {x}");
            }
            // sin^2 + cos^2 = 1
            let one = c.sqr(w).add(&s.sqr(w), w);
            let (lo, hi) = one.to_ratios().expect("in budget");
            assert!(lo <= rat("1") && rat("1") <= hi, "pythagoras at x = {x}");
            assert!(&hi - &lo <= &tol * rat("8"));
            // evenness and oddness
            let cm = t.cos(&xi.neg()).expect("cos");
            let sm = t.sin(&xi.neg()).expect("sin").neg();
            for (u, v) in [(&c, &cm), (&s, &sm)] {
                assert!(u.lo.le(&v.hi) && v.lo.le(&u.hi), "symmetry at x = {x}");
            }
            // doubling: cos 2x = 1 - 2 sin^2 x, checked through a second route
            let x2 = Iv::from_ratio(&(&x * rat("1/2")), w);
            let sh = t.sin(&x2).expect("sin");
            let alt = Iv::one().sub(&sh.sqr(w).mul_int(&BigInt::from(2), w), w);
            assert!(alt.lo.le(&c.hi) && c.lo.le(&alt.hi), "half-angle at x = {x}");
        }
    }

    #[test]
    fn cos_sin_special_points_from_pi() {
        // sin(pi) encloses 0, cos(pi) encloses -1, sin(pi/6) encloses 1/2
        let t = Trig::new(140);
        let w = 180u64;
        let pi = t.pi();
        assert_close(&t.sin(&pi).expect("sin"), "0", 38);
        assert_close(&t.cos(&pi).expect("cos"), "-1", 38);
        let sixth = pi.div_u(6, w).expect("div");
        assert_close(&t.sin(&sixth).expect("sin"), "0.5", 38);
        let s = t.sin(&sixth).expect("sin");
        let (lo, hi) = s.to_ratios().expect("in budget");
        assert!(lo <= rat("1/2") && rat("1/2") <= hi);
        // a wide argument interval is enclosed, not approximated
        let wide = Iv {
            lo: Fl::zero(),
            hi: Fl::one(),
        };
        let c = t.cos(&wide).expect("cos");
        let (lo, hi) = c.to_ratios().expect("in budget");
        assert!(lo <= rat("0.5404") && hi >= rat("1"));
    }

    #[test]
    fn large_arguments_are_refused() {
        let t = Trig::new(64);
        assert!(t.cos(&Iv::from_i64(127)).is_ok());
        assert!(matches!(t.cos(&Iv::from_i64(128)), Err(CalcError::Budget(_))));
        assert!(matches!(t.sin(&Iv::from_i64(-1000)), Err(CalcError::Budget(_))));
    }

    #[test]
    fn precision_from_8_to_14000_bits() {
        // The argument reduction depends on the precision (about sqrt(q)
        // halvings); the enclosures at all precisions must contain the same
        // number, be nested in width, and satisfy sin^2 + cos^2 = 1.
        let x = rat("-577/13"); // about -44.4, several turns
        let known_cos = "0.54030230586813971740093660744297660373231"; // cos 1
        let mut prev: Option<(Iv, Iv)> = None;
        for q in [
            8u64, 9, 15, 16, 17, 24, 25, 26, 63, 64, 100, 257, 1000, 4096, 14_000,
        ] {
            let t = Trig::new(q);
            let w = q + 40;
            let xi = Iv::from_ratio(&x, w);
            let c = t.cos(&xi).expect("cos");
            let s = t.sin(&xi).expect("sin");
            // absolute width about 2^-q: at most 2^-(q - 6) here
            let bound = Fl {
                m: BigInt::one(),
                e: 6 - q as i64,
            };
            assert!(c.width().le(&bound), "cos width at q = {q}");
            assert!(s.width().le(&bound), "sin width at q = {q}");
            let one = c.sqr(w).add(&s.sqr(w), w);
            assert!(
                one.lo.le(&Fl::one()) && Fl::one().le(&one.hi),
                "pythagoras at q = {q}"
            );
            assert!(one.width().le(&bound.shift(3)), "pythagoras width at q = {q}");
            if let Some((pc, ps)) = &prev {
                assert!(c.lo.le(&pc.hi) && pc.lo.le(&c.hi), "cos disjoint at q = {q}");
                assert!(s.lo.le(&ps.hi) && ps.lo.le(&s.hi), "sin disjoint at q = {q}");
            }
            prev = Some((c, s));
            if q >= 160 {
                assert_close(&t.cos(&Iv::from_i64(1)).expect("cos"), known_cos, 38);
            }
        }
        // cos(3x) = 4 cos^3 x - 3 cos x at 14000 bits, through another reduction
        let q = 14_000u64;
        let w = q + 40;
        let t = Trig::new(q);
        let y = rat("1234567/100000");
        let c1 = t.cos(&Iv::from_ratio(&y, w)).expect("cos");
        let c3 = t.cos(&Iv::from_ratio(&(&y * rat("3")), w)).expect("cos");
        let alt = c1
            .powu(3, w)
            .mul_int(&BigInt::from(4), w)
            .sub(&c1.mul_int(&BigInt::from(3), w), w);
        assert!(alt.lo.le(&c3.hi) && c3.lo.le(&alt.hi));
        let bound = Fl {
            m: BigInt::one(),
            e: 12 - q as i64,
        };
        assert!(alt.width().le(&bound) && c3.width().le(&bound));
    }
}
