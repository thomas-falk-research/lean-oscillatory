// SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
//
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]
//! S4.2 constant probes (IEEE-754 binary64, round-to-nearest; tooling, never evidence for a theorem).
//!
//! For a binary cubic C = (a, b, c, d) with Disc ≠ 0, the Gamma-free constant is
//!   c_C = (1/3) · I · J(C),   I = ∫_0^∞ cos u · u^{-1/3} du,   J(C) = ∫_0^{2π} |C(cos θ, sin θ)|^{-2/3} dθ
//! (polar coordinates: ∫_0^∞ e^{i s r³} r dr = (1/3)|s|^{-2/3} ∫_0^∞ e^{±iu} u^{-1/3} du, and C(−z) = −C(z) cancels
//! the sine part). Checked here against
//!   (i)  the closed forms Γ(1/3)²/(√3 |Disc|^{1/6}) (Disc < 0) and Γ(1/3)²/|Disc|^{1/6} (Disc > 0);
//!   (ii) I = Γ(2/3)/2 and the alternating-series structure of I (S4.3 route);
//!   (iii) the limit t^{2/3} ∫∫ e^{itC} A → c_C A(0) by direct 2D quadrature, for one cubic of each sign.
//! Quadrature: tanh-sinh (double exponential) between consecutive roots of θ ↦ C(cos θ, sin θ), levels doubled until
//! two successive levels agree to 1e-13 relative; Γ by the Lanczos approximation (g = 7, n = 9), checked against
//! Γ(1/2) = √π and Γ(1/3) = 2.678938534707747633…; 2D integrals by composite Simpson at n and 2n nodes.

use std::f64::consts::PI;

fn gamma(x: f64) -> f64 {
    const G: [f64; 9] = [
        0.999_999_999_999_809_9, 676.520_368_121_885_1, -1_259.139_216_722_402_8, 771.323_428_777_653_1,
        -176.615_029_162_140_6, 12.507_343_278_686_905, -0.138_571_095_265_720_12, 9.984_369_578_019_572e-6,
        1.505_632_735_149_311_6e-7,
    ];
    if x < 0.5 {
        return PI / ((PI * x).sin() * gamma(1.0 - x));
    }
    let x = x - 1.0;
    let mut a = G[0];
    let t = x + 7.5;
    for (i, g) in G.iter().enumerate().skip(1) {
        a += g / (x + i as f64);
    }
    (2.0 * PI).sqrt() * t.powf(x + 0.5) * (-t).exp() * a
}

type Q = (f64, f64, f64, f64);

fn cubic(q: Q, x: f64, y: f64) -> f64 { q.0 * x * x * x + q.1 * x * x * y + q.2 * x * y * y + q.3 * y * y * y }
fn disc(q: Q) -> f64 {
    let (a, b, c, d) = q;
    b * b * c * c - 4.0 * a * c * c * c - 4.0 * b * b * b * d - 27.0 * a * a * d * d + 18.0 * a * b * c * d
}
fn g(q: Q, th: f64) -> f64 { cubic(q, th.cos(), th.sin()) }

/// Tanh-sinh on [lo, hi]; f receives (x, distance to the nearer endpoint, true if that endpoint is lo).
fn tanh_sinh(lo: f64, hi: f64, f: &dyn Fn(f64, f64, bool) -> f64) -> (f64, f64) {
    let w = hi - lo;
    let mut prev = f64::NAN;
    let mut h = 0.5;
    let mut sum;
    loop {
        sum = 0.0;
        let n = (4.5 / h) as i64;
        for k in -n..=n {
            let t = k as f64 * h;
            let u = 0.5 * PI * t.sinh();
            let wt = 0.5 * w * 0.5 * PI * t.cosh() / (u.cosh() * u.cosh());
            // distance from the nearer endpoint, computed without cancellation
            let (dist, left) =
                if t <= 0.0 { (w / (1.0 + (-2.0 * u).exp()), true) } else { (w / (1.0 + (2.0 * u).exp()), false) };
            let x = if left { lo + dist } else { hi - dist };
            if dist <= 0.0 || wt == 0.0 {
                continue;
            }
            sum += wt * f(x, dist, left);
        }
        sum *= h;
        if (sum - prev).abs() <= 1e-13 * sum.abs() || h < 1.0 / 1024.0 {
            return (sum, (sum - prev).abs());
        }
        prev = sum;
        h *= 0.5;
    }
}

fn roots(q: Q) -> Vec<f64> {
    let n = 200_000;
    let mut r = Vec::new();
    for i in 0..n {
        let (a, b) = (2.0 * PI * i as f64 / n as f64, 2.0 * PI * (i + 1) as f64 / n as f64);
        let (ga, gb) = (g(q, a), g(q, b));
        if ga == 0.0 || ga * gb < 0.0 {
            let (mut lo, mut hi) = (a, b);
            for _ in 0..200 {
                let m = 0.5 * (lo + hi);
                if g(q, lo) * g(q, m) <= 0.0 { hi = m } else { lo = m }
            }
            let x = 0.5 * (lo + hi);
            if r.last().map_or(true, |&l: &f64| x - l > 1e-9) { r.push(x) }
        }
    }
    r
}

/// C(cos(θ0 + s δ), sin(θ0 + s δ)) at a root θ0 (s = ±1), as P'(0) + P''(0)/2 + P'''(0)/6 with
/// P(τ) = C(z0 + τ v), z0 = (cos θ0, sin θ0), v the exact chord; no cancellation against C(z0) ≈ 0.
fn g_near(q: Q, th0: f64, sd: f64) -> f64 {
    let (x, y) = (th0.cos(), th0.sin());
    let h = 2.0 * (0.5 * sd).sin();
    let (vx, vy) = (-h * (th0 + 0.5 * sd).sin(), h * (th0 + 0.5 * sd).cos());
    let (a, b, c, d) = q;
    let cx = 3.0 * a * x * x + 2.0 * b * x * y + c * y * y;
    let cy = b * x * x + 2.0 * c * x * y + 3.0 * d * y * y;
    let hxx = 6.0 * a * x + 2.0 * b * y;
    let hxy = 2.0 * b * x + 2.0 * c * y;
    let hyy = 2.0 * c * x + 6.0 * d * y;
    (cx * vx + cy * vy) + 0.5 * (hxx * vx * vx + 2.0 * hxy * vx * vy + hyy * vy * vy) + cubic(q, vx, vy)
}

/// J(C) = ∫_0^{2π} |C(cos θ, sin θ)|^{-2/3} dθ, split at the roots.
fn angular(q: Q) -> (f64, f64) {
    let r = roots(q);
    assert!(r.len() >= 2 && r.len() % 2 == 0, "roots: {r:?}");
    let (mut s, mut e) = (0.0, 0.0);
    for i in 0..r.len() {
        let lo = r[i];
        let hi = if i + 1 < r.len() { r[i + 1] } else { r[0] + 2.0 * PI };
        let (v, ev) = tanh_sinh(lo, hi, &|_, dist, left| {
            let gv = if left { g_near(q, lo, dist) } else { g_near(q, hi, -dist) };
            gv.abs().powf(-2.0 / 3.0)
        });
        s += v;
        e += ev;
    }
    (s, e)
}

/// I = ∫_0^∞ cos u · u^{-1/3} du as a_0 + a_1 + …, a_0 = ∫_0^{π/2}, a_k = ∫ over [π/2 + (k−1)π, π/2 + kπ];
/// the a_k alternate in sign with decreasing modulus; the tail is summed by repeated averaging of partial sums.
fn cos_moment() -> (f64, Vec<f64>) {
    let f = |u: f64, _: f64, _: bool| u.cos() * u.powf(-1.0 / 3.0);
    let mut a = vec![tanh_sinh(0.0, 0.5 * PI, &f).0];
    for k in 1..=60 {
        let lo = 0.5 * PI + (k - 1) as f64 * PI;
        a.push(tanh_sinh(lo, lo + PI, &f).0);
    }
    let mut partial: Vec<f64> = a.iter().scan(0.0, |s, x| { *s += x; Some(*s) }).collect();
    for _ in 0..30 {
        partial = partial.windows(2).map(|w| 0.5 * (w[0] + w[1])).collect();
    }
    (*partial.last().unwrap(), a)
}

fn bump(s: f64) -> f64 { if s.abs() >= 1.0 { 0.0 } else { (-1.0 / (1.0 - s * s)).exp() } }

/// t^{2/3} ∫∫ e^{itC} bump(x) bump(y), composite Simpson on [-1,1]² with n intervals per side.
fn limit2d(q: Q, t: f64, n: usize) -> (f64, f64) {
    limit2d_gen(&|x, y| cubic(q, x, y), &|x, y| bump(x) * bump(y), t, n)
}

/// t^{2/3} ∫∫ e^{itφ} A for general φ, A supported in [-1,1]².
fn limit2d_gen(phi: &dyn Fn(f64, f64) -> f64, amp: &dyn Fn(f64, f64) -> f64, t: f64, n: usize) -> (f64, f64) {
    let n = n + n % 2;
    let h = 2.0 / n as f64;
    let w = |i: usize| if i == 0 || i == n { 1.0 } else if i % 2 == 1 { 4.0 } else { 2.0 };
    let (mut re, mut im) = (0.0, 0.0);
    for i in 1..n {
        let x = -1.0 + h * i as f64;
        for j in 1..n {
            let y = -1.0 + h * j as f64;
            let a = amp(x, y) * w(i) * w(j);
            if a == 0.0 { continue; }
            let ph = t * phi(x, y);
            re += a * ph.cos();
            im += a * ph.sin();
        }
    }
    let s = t.powf(2.0 / 3.0) * h * h / 9.0;
    (re * s, im * s)
}

fn main() {
    let fail = std::cell::Cell::new(false);
    let check = |name: &str, got: f64, want: f64, tol: f64| {
        let ok = (got - want).abs() <= tol * want.abs().max(1.0);
        fail.set(fail.get() | !ok);
        println!("{}  {name}: {got:.12} vs {want:.12} (rel diff {:.1e})", if ok { "PASS" } else { "FAIL" },
            (got - want).abs() / want.abs());
    };
    println!("== Gamma (Lanczos)");
    check("Γ(1/2) vs √π", gamma(0.5), PI.sqrt(), 1e-13);
    check("Γ(1/3)", gamma(1.0 / 3.0), 2.678_938_534_707_747_6, 1e-13);
    let g13 = gamma(1.0 / 3.0);
    let g23 = gamma(2.0 / 3.0);

    println!("\n== I = ∫_0^∞ cos u u^(-1/3) du  (S4.3: alternating series)");
    let (i_cos, a) = cos_moment();
    check("I vs Γ(2/3)/2", i_cos, g23 / 2.0, 1e-10);
    println!("      a_0 = {:.6}, a_1 = {:.6}, a_2 = {:.6}, a_3 = {:.6}; a_0 + a_1 = {:.6} (> 0: lower bound for I)",
        a[0], a[1], a[2], a[3], a[0] + a[1]);
    let alt = a.windows(2).skip(1).all(|w| w[0] * w[1] < 0.0 && w[1].abs() < w[0].abs());
    println!("{}  a_k (k ≥ 1) alternate in sign with strictly decreasing modulus, k ≤ 60", if alt { "PASS" } else { "FAIL" });
    fail.set(fail.get() | !alt);

    println!("\n== c_C = I · J(C) / 3 vs closed forms");
    let cases: [(&str, Q); 8] = [
        ("x³ + y³", (1.0, 0.0, 0.0, 1.0)),
        ("x²y + y³", (0.0, 1.0, 0.0, 1.0)),
        ("x³ + 2x²y + 3xy² + 5y³", (1.0, 2.0, 3.0, 5.0)),
        ("−2x³ + x²y − 0.5y³", (-2.0, 1.0, 0.0, -0.5)),
        ("x³ − 3xy² (elliptic)", (1.0, 0.0, -3.0, 0.0)),
        ("x²y − xy²", (0.0, 1.0, -1.0, 0.0)),
        ("2x³ − x²y − 5xy² + y³", (2.0, -1.0, -5.0, 1.0)),
        ("0.3x³ − 4xy² + y³", (0.3, 0.0, -4.0, 1.0)),
    ];
    let mut consts = Vec::new();
    for (name, q) in cases {
        let dq = disc(q);
        let (j, ej) = angular(q);
        let c = i_cos * j / 3.0;
        let closed = if dq < 0.0 { g13 * g13 / (3f64.sqrt() * dq.abs().powf(1.0 / 6.0)) } else { g13 * g13 / dq.powf(1.0 / 6.0) };
        check(&format!("{name}  (Disc = {dq}, J = {j:.10}, quad err {ej:.0e})"), c, closed, 1e-9);
        consts.push((name, q, c));
    }

    println!("\n== Limit t^(2/3) ∫∫ e^(itC) A → c_C A(0), A = bump ⊗ bump (2D Simpson; trend, not a check)");
    let a0 = bump(0.0) * bump(0.0);
    for idx in [0usize, 4] {
        let (name, q, c) = consts[idx];
        print!("{name}: c_C A(0) = {:.6};", c * a0);
        let mut last = Vec::new();
        for t in [10.0, 30.0, 100.0, 300.0] {
            let n = (14.0 * t) as usize + 400;
            let (re, im) = limit2d(q, t, n);
            let (re2, _) = limit2d(q, t, 2 * n);
            print!("  t={t}: {re:.6}{im:+.6}i (Δn {:.0e})", (re - re2).abs());
            last.push(re);
        }
        // Richardson with an assumed t^{-2/3} correction, from t = 100 and t = 300
        let r = 3f64.powf(2.0 / 3.0);
        let ext = (r * last[3] - last[2]) / (r - 1.0);
        println!();
        check(&format!("{name}: Richardson (t^(-2/3) correction) from t = 100, 300"), ext, c * a0, 1e-3);
    }
    println!("\n== Referee NIT: quartic terms and a non-even amplitude (trend toward c_C A(0); correction O(t^(-1/3)))");
    for idx in [0usize, 4] {
        let (name, q, c) = consts[idx];
        let phi = |x: f64, y: f64| cubic(q, x, y) + 0.5 * x.powi(4) + 0.3 * x * x * y * y;
        let amp = |x: f64, y: f64| bump(x) * bump(y) * (1.0 + 0.5 * x + 0.3 * y);
        print!("{name} + 0.5x⁴ + 0.3x²y², A = bump⊗bump·(1 + 0.5x + 0.3y): c_C A(0) = {:.6};", c * a0);
        for t in [30.0, 100.0, 300.0, 1000.0] {
            let n = (14.0 * t) as usize + 400;
            let (re, im) = limit2d_gen(&phi, &amp, t, n);
            print!("  t={t}: {re:.6}{im:+.6}i");
        }
        println!();
    }
    println!("\nRESULT {}", if fail.get() { "FAIL" } else { "PASS" });
    std::process::exit(fail.get() as i32);
}
