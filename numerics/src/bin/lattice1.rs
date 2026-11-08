// SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
//
// SPDX-License-Identifier: Apache-2.0

//! Pre-registered numeric check of batch LE (explicit constants for the 1D and 2D lattice kernels).
//! Protocol: docs/prereg/2026-11-08-LE-lattice-constants.md (registered d814381, amendment 1 d26b9a4, both before
//! this program was written). Tooling, not evidence. f64, index-order summation, single thread.

use std::f64::consts::PI;

#[derive(Clone, Copy, Debug)]
struct C {
    re: f64,
    im: f64,
}
impl C {
    fn cis(a: f64) -> C {
        C { re: a.cos(), im: a.sin() }
    }
    fn add(self, o: C) -> C {
        C { re: self.re + o.re, im: self.im + o.im }
    }
    fn sub(self, o: C) -> C {
        C { re: self.re - o.re, im: self.im - o.im }
    }
    fn mul(self, o: C) -> C {
        C { re: self.re * o.re - self.im * o.im, im: self.re * o.im + self.im * o.re }
    }
    fn scale(self, s: f64) -> C {
        C { re: self.re * s, im: self.im * s }
    }
    fn abs(self) -> f64 {
        self.re.hypot(self.im)
    }
}

const A: f64 = 24.0;
const B: f64 = 36.0;
fn a_const() -> f64 {
    A * 2f64.powf(0.25)
}
fn b_const() -> f64 {
    B * 2f64.powf(1.0 / 6.0)
}
fn bound1(t: f64) -> f64 {
    a_const() * t.powf(-0.5) + b_const() * t.powf(-1.0 / 3.0)
}

/// Q1: trapezoid rule on [-pi, pi) for integer n, N = 2(ceil t + |n|) + 256.
fn q1(t: f64, n: i64) -> C {
    let nn = 2 * (t.ceil() as i64 + n.abs()) as usize + 256;
    let h = 2.0 * PI / nn as f64;
    let mut s = C { re: 0.0, im: 0.0 };
    for j in 0..nn {
        let k = -PI + j as f64 * h;
        s = s.add(C::cis(t * k.cos() + n as f64 * k));
    }
    s.scale(h)
}

/// Gauss-Legendre nodes and weights on [-1, 1] by Newton iteration on P_m.
fn gauss_legendre(m: usize) -> (Vec<f64>, Vec<f64>) {
    let mut x = vec![0.0; m];
    let mut w = vec![0.0; m];
    for i in 0..m {
        let mut z = (PI * (i as f64 + 0.75) / (m as f64 + 0.5)).cos();
        let mut dp = 0.0;
        for _ in 0..100 {
            let (mut p0, mut p1) = (1.0, z);
            for k in 2..=m {
                let p2 = ((2 * k - 1) as f64 * z * p1 - (k - 1) as f64 * p0) / k as f64;
                p0 = p1;
                p1 = p2;
            }
            dp = m as f64 * (z * p1 - p0) / (z * z - 1.0);
            let dz = p1 / dp;
            z -= dz;
            if dz.abs() < 1e-16 {
                break;
            }
        }
        x[i] = z;
        w[i] = 2.0 / ((1.0 - z * z) * dp * dp);
    }
    (x, w)
}

/// Q2: composite Gauss-Legendre, 16 nodes per panel, P = ceil(4(t + |xi|)) + 64 panels on [-pi, pi].
fn q2(gl: &(Vec<f64>, Vec<f64>), t: f64, xi: f64) -> C {
    let p = (4.0 * (t + xi.abs())).ceil() as usize + 64;
    let width = 2.0 * PI / p as f64;
    let mut s = C { re: 0.0, im: 0.0 };
    for q in 0..p {
        let mid = -PI + (q as f64 + 0.5) * width;
        for (xn, wn) in gl.0.iter().zip(gl.1.iter()) {
            let k = mid + 0.5 * width * xn;
            s = s.add(C::cis(t * k.cos() + xi * k).scale(0.5 * width * wn));
        }
    }
    s
}

/// 2D kernel by the rank-1 Fibonacci lattice rule (amendment 1): N = F26, generator F25.
fn kernel2_lattice(t: f64, x1: i64, x2: i64) -> C {
    let n: u64 = 121393;
    let g: u64 = 75025;
    let mut s = C { re: 0.0, im: 0.0 };
    for j in 0..n {
        let k1 = 2.0 * PI * (j as f64 / n as f64) - PI;
        let k2 = 2.0 * PI * (((j * g) % n) as f64 / n as f64) - PI;
        s = s.add(C::cis(t * (k1.cos() + k2.cos()) + x1 as f64 * k1 + x2 as f64 * k2));
    }
    s.scale(4.0 * PI * PI / n as f64)
}

fn slope(xs: &[f64], ys: &[f64]) -> f64 {
    let n = xs.len() as f64;
    let mx = xs.iter().sum::<f64>() / n;
    let my = ys.iter().sum::<f64>() / n;
    let mut sxy = 0.0;
    let mut sxx = 0.0;
    for (x, y) in xs.iter().zip(ys) {
        sxy += (x - mx) * (y - my);
        sxx += (x - mx) * (x - mx);
    }
    sxy / sxx
}

fn main() {
    let gl = gauss_legendre(16);
    let landau = 0.7858;
    let (ac, bc) = (a_const(), b_const());
    println!("batch LE numeric check (docs/prereg/2026-11-08-LE-lattice-constants.md)");
    println!("A = 24*2^(1/4) = {ac:.10}  B = 36*2^(1/6) = {bc:.10}  A+B = {:.10}  (A+B)^2 = {:.6}", ac + bc, (ac + bc).powi(2));

    let nt = 120;
    let (t0, t1): (f64, f64) = (0.1, 2000.0);
    let mut max_ratio_a: f64 = 0.0;
    let mut argmax_a = (0.0, 0.0);
    let mut max_ratio_e: f64 = 0.0;
    let mut max_landau: f64 = 0.0;
    let mut argmax_landau = (0.0, 0i64);
    let mut max_q12: f64 = 0.0;
    let mut max_sym: f64 = 0.0;
    let mut c2_fails = 0usize;
    let mut slope_x = vec![];
    let mut slope_y = vec![];
    for it in 0..nt {
        let t = t0 * (t1 / t0).powf(it as f64 / (nt - 1) as f64);
        let nmax = (1.2 * t).ceil() as i64 + 30;
        let b1 = bound1(t);
        let mut sup_n: f64 = 0.0;
        let mut q1v = Vec::with_capacity(nmax as usize + 1);
        for n in 0..=nmax {
            let v = q1(t, n);
            let a = v.abs();
            q1v.push(v);
            sup_n = sup_n.max(a);
            if a / b1 > max_ratio_a {
                max_ratio_a = a / b1;
                argmax_a = (t, n as f64);
            }
            let l = t.powf(1.0 / 3.0) * a / (2.0 * PI);
            if l > max_landau {
                max_landau = l;
                argmax_landau = (t, n);
            }
            if a > 0.9 * 2.0 * PI * landau * t.powf(-1.0 / 3.0) {
                c2_fails += 1;
            }
        }
        // Q2 on n in {0,1} and the band |n - t| <= 5 t^(1/3) + 5, compared with Q1.
        let band = 5.0 * t.powf(1.0 / 3.0) + 5.0;
        let lo = ((t - band).floor() as i64).max(0);
        let hi = ((t + band).ceil() as i64).min(nmax);
        let mut ns: Vec<i64> = vec![0, 1];
        ns.extend(lo..=hi);
        for &n in &ns {
            let d = q2(&gl, t, n as f64).sub(q1v[n as usize]).abs();
            max_q12 = max_q12.max(d);
        }
        // |I(t, -n)| = |I(t, n)| by Q2 at n = 1, 2, 3, floor t.
        for n in [1i64, 2, 3, t.floor() as i64] {
            let d = (q2(&gl, t, -(n as f64)).abs() - q1(t, n).abs()).abs();
            max_sym = max_sym.max(d);
        }
        // Non-integer xi by Q2.
        for xi in [0.5, 2f64.sqrt(), t / 2.0 + 0.3, t + 0.37, t + 2.0 * t.powf(1.0 / 3.0) + 0.11] {
            let a = q2(&gl, t, xi).abs();
            if a / b1 > max_ratio_a {
                max_ratio_a = a / b1;
                argmax_a = (t, xi);
            }
        }
        if t >= 1.0 {
            let r = sup_n * sup_n / ((ac + bc).powi(2) * t.powf(-2.0 / 3.0));
            max_ratio_e = max_ratio_e.max(r);
        }
        if (100.0..=2000.0 + 1e-9).contains(&t) {
            slope_x.push(t.ln());
            slope_y.push(sup_n.ln());
        }
        if it % 10 == 0 || it == nt - 1 {
            println!(
                "t = {t:>10.4}  sup_n|I| = {sup_n:.6e}  bound T0E = {b1:.6e}  ratio = {:.4e}  t^(1/3) sup/(2pi) = {:.6}",
                sup_n / b1,
                t.powf(1.0 / 3.0) * sup_n / (2.0 * PI)
            );
        }
    }
    let unresolved = max_q12 > 1e-9;
    println!("Q1 vs Q2 max |difference| = {max_q12:.3e} (tolerance 1e-9): {}", if unresolved { "UNRESOLVED" } else { "agree" });
    println!("symmetry max ||I(t,-n)| - |I(t,n)|| = {max_sym:.3e}");
    let pa = max_ratio_a < 1.0;
    println!("(a) max |I| / T0E bound = {max_ratio_a:.6} at (t, xi) = ({:.4}, {:.4}): {}", argmax_a.0, argmax_a.1, pf(pa));
    let s = slope(&slope_x, &slope_y);
    let pb = (-0.36..=-0.31).contains(&s);
    println!("(b) slope of log sup_n|I| vs log t over t in [100, 2000] ({} points) = {s:.5}: {}", slope_x.len(), pf(pb));
    let pc = max_landau <= landau + 1e-4;
    println!(
        "(c) max t^(1/3)|I|/(2pi) = {max_landau:.6} at (t, n) = ({:.4}, {}) vs Landau 0.7858: {}",
        argmax_landau.0, argmax_landau.1, pf(pc)
    );

    // (d) and (c3): 2D by the Fibonacci lattice rule against Q1 products.
    let mut max_d: f64 = 0.0;
    let mut min_c3: f64 = f64::INFINITY;
    for t in [0.7, 3.0, 25.0] {
        for (x1, x2) in [(0i64, 0i64), (1, -2), (3, 3), (-5, 2)] {
            let k = kernel2_lattice(t, x1, x2);
            let prod = q1(t, x1).mul(q1(t, x2));
            let d = k.sub(prod).abs();
            max_d = max_d.max(d);
            let wrong = q1(t, x1 + x2).mul(q1(t, 0));
            let dw = k.sub(wrong).abs();
            if x1 * x2 != 0 {
                min_c3 = min_c3.min(dw);
            }
            println!("  2D t = {t:>5}  x = ({x1:>2}, {x2:>2})  |K| = {:.10e}  |K - I I| = {d:.3e}  |K - wrong| = {dw:.3e}", k.abs());
        }
    }
    let pd = max_d <= 1e-9;
    println!("(d) max |K - I(t,x1) I(t,x2)| = {max_d:.3e} (tolerance 1e-9): {}", pf(pd));
    let pe = max_ratio_e < 1.0;
    println!("(e) max over t >= 1 of (sup_n|I|)^2 / ((A+B)^2 t^(-2/3)) = {max_ratio_e:.6}: {}", pf(pe));

    let c1_fails = !(-0.55..=-0.45).contains(&s);
    println!("(c1) control exponent -1/2: slope {s:.5} outside [-0.55, -0.45]: {}", if c1_fails { "control FAILS (good)" } else { "control passes (NOT DISCRIMINATING)" });
    let c2f = c2_fails > 0;
    println!("(c2) control 0.9 * 2pi * 0.7858 * t^(-1/3): violated at {c2_fails} grid points: {}", if c2f { "control FAILS (good)" } else { "control passes (NOT DISCRIMINATING)" });
    let c3f = min_c3 > 1e-9;
    println!("(c3) control wrong factorisation: min |K - I(t,x1+x2) I(t,0)| over x1 x2 != 0 = {min_c3:.3e}: {}", if c3f { "control FAILS (good)" } else { "control passes (NOT DISCRIMINATING)" });
    println!("reported: (A+B) / (2pi * 0.7858) = {:.3}", (ac + bc) / (2.0 * PI * landau));
    let pass = !unresolved && pa && pb && pc && pd && pe && c1_fails && c2f && c3f;
    println!("OVERALL: {}", if pass { "PASS" } else { "NOT PASS (see the lines above)" });
}

fn pf(b: bool) -> &'static str {
    if b {
        "PASS"
    } else {
        "FAIL"
    }
}
