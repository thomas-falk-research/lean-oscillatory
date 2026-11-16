//! J_n(x) for an integer order n and a rational x, from the power series
//! with an alternating-series remainder bound.

use crate::num::{CalcError, Fl, Iv, Res};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{Signed, ToPrimitive, Zero};

/// Largest |n| computed. The contract gives no bound; this is the checker's budget.
pub const N_MAX: u64 = 10_000;
/// Largest |x| supported (contract, section 4).
pub const X_MAX: i64 = 400;
/// Largest working precision tried, in bits.
const W_CAP: u64 = 1 << 15;

/// An enclosure of J_n(x). When the working-precision cap allows, its
/// relative width is at most 2^-t (exact values 0 and 1 are returned as
/// points).
pub fn bessel_j(n: &BigInt, x: &BigRational, t: u64) -> Res<Iv> {
    let n_abs = n
        .abs()
        .to_u64()
        .filter(|v| *v <= N_MAX)
        .ok_or_else(|| CalcError::Budget(format!("|n| exceeds the checker's budget of {N_MAX}")))?;
    if x.abs() > BigRational::from_integer(BigInt::from(X_MAX)) {
        return Err(CalcError::Budget(format!("|x| exceeds {X_MAX}")));
    }
    if x.is_zero() {
        // J_0(0) = 1 and J_n(0) = 0 for n != 0, exactly
        return Ok(if n_abs == 0 { Iv::one() } else { Iv::zero() });
    }
    // J_{-n}(x) = (-1)^n J_n(x) and J_n(-x) = (-1)^n J_n(x) for integer n
    // (DLMF 10.4.1 and the parity of the series below).
    let mut negate = false;
    if n.is_negative() && n_abs.is_odd() {
        negate = !negate;
    }
    if x.is_negative() && n_abs.is_odd() {
        negate = !negate;
    }
    let ax = x.abs();
    let mut w = t + 64;
    let value = loop {
        let v = series(n_abs, &ax, w)?;
        if v.rel_width_ok(t) || w >= W_CAP {
            break v;
        }
        w = (2 * w).min(W_CAP);
    };
    Ok(if negate { value.neg() } else { value })
}

/// The series for n >= 0 and x > 0 at working precision `w`:
///
///   J_n(x) = sum_{m>=0} (-1)^m s_m,   s_m = (x/2)^(2m+n) / (m! (m+n)!)
///
/// (DLMF 10.2.2). The terms are positive and s_{m+1}/s_m =
/// (x/2)^2 / ((m+1)(m+1+n)), which decreases with m. Once
/// (M+1)(M+1+n) >= (x/2)^2 the terms s_M, s_{M+1}, ... do not increase,
/// and they tend to 0, so by Leibniz's criterion the tail
/// sum_{m>=M} (-1)^m s_m has modulus at most s_M. The sum is therefore
/// enclosed by the partial sum through M-1 plus [-s_M, s_M].
fn series(n: u64, x: &BigRational, w: u64) -> Res<Iv> {
    let wi = w + 32;
    let half = x / BigRational::from_integer(BigInt::from(2));
    let y_exact = &half * &half;
    let hx = Iv::from_ratio(&half, wi);
    let y = Iv::from_ratio(&y_exact, wi);
    // s_0 = (x/2)^n / n!, built one factor (x/2)/j at a time
    let mut term = Iv::one();
    for j in 1..=n {
        term = term.mul(&hx, wi).div_u(j, wi)?;
    }
    if !term.lo.is_pos() {
        return Err(CalcError::Internal("first Bessel term not positive".into()));
    }
    // No lower limit on the size of the value: with a dyadic exponent the
    // series costs the same for J_10000(10^-98), about 10^-1018660, as for
    // any other argument, and the comparison with a claim never builds the
    // value as a fraction (see `num::cmp_ratio_fl`).
    let mut sum = term.clone();
    let mut largest: Fl = term.hi.clone();
    let mut m: u64 = 0;
    loop {
        // s_{m+1} from s_m
        let d = (m + 1)
            .checked_mul(m + 1 + n)
            .ok_or_else(|| CalcError::Internal("index overflow".into()))?;
        term = term.mul(&y, wi).div_u(d, wi)?;
        m += 1;
        // `term` encloses s_m. From m on the terms do not increase if
        // (m+1)(m+1+n) >= (x/2)^2.
        let next = (m + 1)
            .checked_mul(m + 1 + n)
            .ok_or_else(|| CalcError::Internal("index overflow".into()))?;
        let monotone = BigRational::from_integer(BigInt::from(next)) >= y_exact;
        if monotone && term.hi.top() + (wi as i64) < largest.top() {
            // s_m is below the rounding noise of the largest term: stop and
            // enclose the tail by [-s_m, s_m]
            let tail = Iv {
                lo: term.hi.neg(),
                hi: term.hi.clone(),
            };
            sum = sum.add(&tail, wi);
            break;
        }
        if largest.lt(&term.hi) {
            largest = term.hi.clone();
        }
        sum = if m % 2 == 1 {
            sum.sub(&term, wi)
        } else {
            sum.add(&term, wi)
        };
        if m > 1_000_000 {
            return Err(CalcError::Budget("Bessel series too long".into()));
        }
    }
    Ok(sum)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::num::parse_rational;
    use crate::trig::Trig;
    use num_traits::One;

    fn rat(s: &str) -> BigRational {
        match parse_rational(s) {
            Ok(r) => r,
            Err(e) => panic!("{s}: {e:?}"),
        }
    }

    fn j(n: i64, x: &str, t: u64) -> Iv {
        bessel_j(&BigInt::from(n), &rat(x), t).expect("bessel")
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

    #[test]
    fn known_values() {
        // Abramowitz and Stegun, Table 9.1, extended; standard reference values
        assert_close(&j(0, "1", 128), "0.765197686557966551449717526102663220909", 35);
        assert_close(&j(1, "1", 128), "0.440050585744933515959682203718914913127", 35);
        assert_close(&j(0, "2", 128), "0.223890779141235668051827454649948625825", 35);
        assert_close(&j(1, "2", 128), "0.576724807756873387202448242269137086920", 35);
        assert_close(&j(0, "10", 128), "-0.245935764451348335197760862485328753830", 35);
        assert_close(&j(1, "10", 128), "0.043472746168861436669748768025859288306", 35);
        // a value with heavy cancellation in the series (terms up to about 1e42)
        assert_close(&j(0, "100", 128), "0.019985850304223122", 16);
    }

    #[test]
    fn exact_values_at_zero() {
        let (lo, hi) = j(0, "0", 64).to_ratios().expect("in budget");
        assert!(lo == rat("1") && hi == rat("1"));
        for n in [-3i64, 1, 2, 77] {
            let (lo, hi) = j(n, "0", 64).to_ratios().expect("in budget");
            assert!(lo.is_zero() && hi.is_zero());
        }
    }

    #[test]
    fn relative_precision_reached() {
        for (n, x) in [
            (0i64, "1/3"),
            (5, "7/2"),
            (60, "1"),
            (60, "120"),
            (3, "400"),
            (0, "-399.5"),
            (200, "1/1000"),
            (-7, "13"),
        ] {
            for t in [64u64, 256] {
                let v = j(n, x, t);
                assert!(v.rel_width_ok(t), "n = {n}, x = {x}, t = {t}");
                assert!(v.lo.le(&v.hi));
            }
        }
        // nested: a higher precision lies inside or overlaps the lower one
        let a = j(4, "25/3", 64);
        let b = j(4, "25/3", 256);
        assert!(a.lo.le(&b.hi) && b.lo.le(&a.hi));
    }

    #[test]
    fn symmetries() {
        let t = 128;
        for n in [1i64, 2, 3, 8] {
            for x in ["3/7", "11", "57.25"] {
                let v = j(n, x, t);
                let sign_n = j(-n, x, t);
                let sign_x = j(n, &format!("-{x}"), t);
                let expect = if n % 2 == 0 { v.clone() } else { v.neg() };
                for other in [&sign_n, &sign_x] {
                    assert!(
                        expect.lo.le(&other.hi) && other.lo.le(&expect.hi),
                        "n = {n}, x = {x}"
                    );
                }
                let both = j(-n, &format!("-{x}"), t);
                assert!(v.lo.le(&both.hi) && both.lo.le(&v.hi));
            }
        }
    }

    #[test]
    fn recurrence_holds() {
        // J_{n-1}(x) + J_{n+1}(x) = (2n/x) J_n(x)  (DLMF 10.6.1)
        let t = 160u64;
        let w = 200u64;
        for x in ["1/2", "5", "37/3", "120", "400"] {
            let xr = rat(x);
            for n in [1i64, 2, 9, 40] {
                let lhs = j(n - 1, x, t).add(&j(n + 1, x, t), w);
                let factor = Iv::from_ratio(&(BigRational::from_integer(BigInt::from(2 * n)) / &xr), w);
                let rhs = factor.mul(&j(n, x, t), w);
                assert!(
                    lhs.lo.le(&rhs.hi) && rhs.lo.le(&lhs.hi),
                    "recurrence at n = {n}, x = {x}"
                );
            }
        }
    }

    #[test]
    fn generating_function_identities() {
        // 1 = J_0(x)^2 + 2 sum_{k>=1} J_k(x)^2          (DLMF 10.23.3 with nu = 0)
        // cos x = J_0(x) - 2 J_2(x) + 2 J_4(x) - ...     (DLMF 10.12.3)
        // sin x = 2 J_1(x) - 2 J_3(x) + 2 J_5(x) - ...
        // The sums are truncated at k = 150, where |J_k(x)| <= (|x|/2)^k / k!
        // is below 1e-100 for |x| <= 20, so a tolerance of 1e-60 is safe.
        let t = 256u64;
        let w = 300u64;
        let trig = Trig::new(280);
        let tol = Iv::from_ratio(
            &BigRational::new(BigInt::one(), num_traits::pow(BigInt::from(10u32), 60)),
            w,
        );
        let slack = Iv {
            lo: tol.hi.neg(),
            hi: tol.hi.clone(),
        };
        for x in ["1", "7/3", "-12.5", "20"] {
            let xr = rat(x);
            let mut sq = j(0, x, t).sqr(w);
            let mut c = j(0, x, t);
            let mut s = Iv::zero();
            for k in 1i64..=150 {
                let jk = j(k, x, t);
                let two_jk = jk.mul_int(&BigInt::from(2), w);
                sq = sq.add(&jk.sqr(w).mul_int(&BigInt::from(2), w), w);
                let plus = (k / 2) % 2 == 0;
                if k % 2 == 0 {
                    // k = 2, 6, ... enter with a minus sign
                    c = if (k / 2) % 2 == 1 {
                        c.sub(&two_jk, w)
                    } else {
                        c.add(&two_jk, w)
                    };
                } else {
                    // k = 1, 5, ... enter with a plus sign
                    s = if plus {
                        s.add(&two_jk, w)
                    } else {
                        s.sub(&two_jk, w)
                    };
                }
            }
            let sq = sq.add(&slack, w);
            let c = c.add(&slack, w);
            let s = s.add(&slack, w);
            let one = Fl::one();
            assert!(sq.lo.le(&one) && one.le(&sq.hi), "sum of squares at x = {x}");
            assert!(sq.width().lt(&tol.hi.shift(3)));
            let xi = Iv::from_ratio(&xr, w);
            let (cx, sx) = (trig.cos(&xi).expect("cos"), trig.sin(&xi).expect("sin"));
            assert!(c.lo.le(&cx.hi) && cx.lo.le(&c.hi), "cosine identity at x = {x}");
            assert!(s.lo.le(&sx.hi) && sx.lo.le(&s.hi), "sine identity at x = {x}");
        }
    }

    #[test]
    fn budget_and_range() {
        assert!(matches!(
            bessel_j(&BigInt::from(0), &rat("400.0001"), 64),
            Err(CalcError::Budget(_))
        ));
        assert!(bessel_j(&BigInt::from(0), &rat("-400"), 64).is_ok());
        assert!(matches!(
            bessel_j(&BigInt::from(10_001), &rat("1"), 64),
            Err(CalcError::Budget(_))
        ));
        let huge = num_traits::pow(BigInt::from(10u32), 30);
        assert!(matches!(
            bessel_j(&huge, &rat("1"), 64),
            Err(CalcError::Budget(_))
        ));
    }

    #[test]
    fn tiny_arguments_and_tiny_values() {
        // For 0 < x <= 2 the series alternates with decreasing terms, so
        // s_0 - s_1 <= J_n(x) <= s_0 with s_0 = (x/2)^n / n! and
        // s_1 = s_0 (x/2)^2 / (n + 1).
        let w = 400u64;
        let tiny = BigRational::new(BigInt::one(), num_traits::pow(BigInt::from(10u32), 98));
        for n in [1u64, 2, 7, 100, 9_999, 10_000] {
            for x in [tiny.clone(), rat("1/1000"), rat("3/2")] {
                let v = bessel_j(&BigInt::from(n), &x, 256).expect("no lower limit on the value");
                assert!(v.lo.is_pos(), "n = {n}");
                assert!(v.rel_width_ok(256), "n = {n}");
                let half = Iv::from_ratio(&(&x / BigRational::from_integer(BigInt::from(2))), w);
                let mut s0 = Iv::one();
                for j in 1..=n {
                    s0 = s0.mul(&half, w).div_u(j, w).expect("div");
                }
                let s1 = s0.mul(&half.sqr(w), w).div_u(n + 1, w).expect("div");
                let lower = s0.sub(&s1, w);
                assert!(lower.lo.le(&v.hi) && v.lo.le(&s0.hi), "n = {n}, x = {x}");
            }
        }
        // J_10000(10^-98) is about 10^-1018660: far below 2^-1048576, and computed
        let v = bessel_j(&BigInt::from(10_000), &tiny, 256).expect("computed");
        assert!(
            v.lo.top() < -3_000_000 && v.lo.top() > -3_500_000,
            "{}",
            v.lo.top()
        );
        // the reflections
        let minus = -tiny.clone();
        let odd = bessel_j(&BigInt::from(9_999), &minus, 128).expect("computed");
        assert!(odd.hi.is_neg());
        let even = bessel_j(&BigInt::from(-10_000), &minus, 128).expect("computed");
        assert!(even.lo.is_pos());
        // and the square, for the population
        let p = crate::quant::population(&BigInt::from(10_000), &tiny, 256).expect("computed");
        assert!(p.lo.is_pos() && p.rel_width_ok(250));
    }
}
