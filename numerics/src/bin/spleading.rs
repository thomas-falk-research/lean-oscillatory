// SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
//
// SPDX-License-Identifier: Apache-2.0

//! Pre-registered numeric check of the 2D nondegenerate stationary-phase leading term (P3b).
//! Protocol: docs/prereg/2026-11-08-P3b-leading-term.md (fixed before this program was run). Tooling, not evidence.
//! Trapezoid rule on [-1, 1]^2 (the integrand vanishes to all orders on the boundary), n and 2n panels, f64.

use std::f64::consts::PI;

fn bump(s: f64) -> f64 {
    if s.abs() >= 1.0 { 0.0 } else { (-1.0 / (1.0 - s * s)).exp() }
}

struct Case {
    name: &'static str,
    phi: fn(f64, f64) -> f64,
    grad: fn(f64, f64) -> (f64, f64),
    amp: fn(f64, f64) -> f64,
    k0: (f64, f64),
    hess: [[f64; 2]; 2],
}

fn amp_even(x: f64, y: f64) -> f64 { bump(x) * bump(y) }
fn amp_tilt(x: f64, y: f64) -> f64 { bump(x) * bump(y) * (1.0 + 0.5 * x + 0.3 * y) }

fn c1(x: f64, y: f64) -> f64 { x * x + 2.0 * y * y + 0.3 * x * x * x + 0.2 * x * y * y }
fn g1(x: f64, y: f64) -> (f64, f64) { (2.0 * x + 0.9 * x * x + 0.2 * y * y, 4.0 * y + 0.4 * x * y) }
fn c2(x: f64, y: f64) -> f64 { x * x - 3.0 * y * y + 0.4 * x * x * y }
fn g2(x: f64, y: f64) -> (f64, f64) { (2.0 * x + 0.8 * x * y, -6.0 * y + 0.4 * x * x) }
fn c3(x: f64, y: f64) -> f64 { -(x * x + x * y + y * y) + 0.25 * x.powi(4) }
fn g3(x: f64, y: f64) -> (f64, f64) { (-2.0 * x - y + x.powi(3), -x - 2.0 * y) }
fn c4(x: f64, y: f64) -> f64 {
    let (u, v) = (x - 0.2, y + 0.1);
    u * u - 2.0 * v * v + 0.3 * u * u * u + 0.7
}
fn g4(x: f64, y: f64) -> (f64, f64) {
    let (u, v) = (x - 0.2, y + 0.1);
    (2.0 * u + 0.9 * u * u, -4.0 * v)
}

/// Trapezoid sums of e^{i m Ψ} A for every m at once, n panels per axis.
fn integrals(c: &Case, ms: &[f64], n: usize) -> Vec<(f64, f64)> {
    let h = 2.0 / n as f64;
    let mut acc = vec![(0.0f64, 0.0f64); ms.len()];
    for i in 1..n {
        let x = -1.0 + i as f64 * h;
        let mut row = vec![(0.0f64, 0.0f64); ms.len()];
        for j in 1..n {
            let y = -1.0 + j as f64 * h;
            let a = (c.amp)(x, y);
            if a == 0.0 { continue; }
            let p = (c.phi)(x, y);
            for (r, &m) in row.iter_mut().zip(ms) {
                let (s, co) = (m * p).sin_cos();
                r.0 += a * co;
                r.1 += a * s;
            }
        }
        for (a, r) in acc.iter_mut().zip(&row) { a.0 += r.0; a.1 += r.1; }
    }
    acc.iter().map(|&(re, im)| (re * h * h, im * h * h)).collect()
}

fn leading(c: &Case, m: f64, with_phase_factor: bool) -> (f64, f64) {
    let [[a, b], [b2, d]] = c.hess;
    let det = a * d - b * b2;
    let tr = a + d;
    let sgn = if det < 0.0 { 0.0 } else if tr > 0.0 { 2.0 } else { -2.0 };
    let arg = m * (c.phi)(c.k0.0, c.k0.1) + if with_phase_factor { PI * sgn / 4.0 } else { 0.0 };
    let modulus = 2.0 * PI / m / det.abs().sqrt() * (c.amp)(c.k0.0, c.k0.1);
    (modulus * arg.cos(), modulus * arg.sin())
}

fn unique_critical(c: &Case) -> (bool, f64) {
    // min |∇Ψ| over a 401 x 401 grid outside a 0.05-ball around k0, and the gradient at k0
    let mut minfar = f64::INFINITY;
    for i in 0..=400 {
        for j in 0..=400 {
            let (x, y) = (-1.0 + i as f64 / 200.0, -1.0 + j as f64 / 200.0);
            if ((x - c.k0.0).powi(2) + (y - c.k0.1).powi(2)).sqrt() < 0.05 { continue; }
            let (gx, gy) = (c.grad)(x, y);
            minfar = minfar.min((gx * gx + gy * gy).sqrt());
        }
    }
    let (gx, gy) = (c.grad)(c.k0.0, c.k0.1);
    ((gx * gx + gy * gy).sqrt() < 1e-12 && minfar > 1e-3, minfar)
}

fn slope(xs: &[f64], ys: &[f64]) -> f64 {
    let n = xs.len() as f64;
    let (mx, my) = (xs.iter().sum::<f64>() / n, ys.iter().sum::<f64>() / n);
    let num: f64 = xs.iter().zip(ys).map(|(x, y)| (x - mx) * (y - my)).sum();
    let den: f64 = xs.iter().map(|x| (x - mx).powi(2)).sum();
    num / den
}

fn main() {
    let ms = [10.0, 20.0, 40.0, 80.0, 160.0, 320.0, 640.0];
    let (n1, n2) = (4096usize, 8192usize);
    let cases = [
        Case { name: "C1 elliptic sgn +2", phi: c1, grad: g1, amp: amp_even, k0: (0.0, 0.0), hess: [[2.0, 0.0], [0.0, 4.0]] },
        Case { name: "C2 hyperbolic sgn 0", phi: c2, grad: g2, amp: amp_even, k0: (0.0, 0.0), hess: [[2.0, 0.0], [0.0, -6.0]] },
        Case { name: "C3 negative definite sgn -2", phi: c3, grad: g3, amp: amp_even, k0: (0.0, 0.0), hess: [[-2.0, -1.0], [-1.0, -2.0]] },
        Case { name: "C4 shifted k0, tilted amplitude", phi: c4, grad: g4, amp: amp_tilt, k0: (0.2, -0.1), hess: [[2.0, 0.0], [0.0, -4.0]] },
    ];
    let mut all_pass = true;
    let mut c5_rel = f64::NAN;
    for (ci, c) in cases.iter().enumerate() {
        let (uniq, minfar) = unique_critical(c);
        println!("== {}  (unique critical point in [-1,1]^2: {uniq}; min |grad| outside B(k0, 0.05): {minfar:.3e})", c.name);
        let i1 = integrals(c, &ms, n1);
        let i2 = integrals(c, &ms, n2);
        let (mut lx, mut ly) = (vec![], vec![]);
        let mut rel640 = f64::NAN;
        let mut unresolved = 0;
        for (k, &m) in ms.iter().enumerate() {
            let (lr, li) = leading(c, m, true);
            let (r_re, r_im) = (i2[k].0 - lr, i2[k].1 - li);
            let r = (r_re * r_re + r_im * r_im).sqrt();
            let q = ((i1[k].0 - i2[k].0).powi(2) + (i1[k].1 - i2[k].1).powi(2)).sqrt();
            let lead = (lr * lr + li * li).sqrt();
            let resolved = q < 1e-3 * r;
            if !resolved { unresolved += 1; }
            println!("  m = {m:>5}: I = {:+.12e} {:+.12e}i  leading = {:+.12e} {:+.12e}i  |R| = {r:.4e}  m^2|R| = {:.5e}  |R|/|lead| = {:.3e}  quad |I_n - I_2n| = {q:.2e}{}",
                i2[k].0, i2[k].1, lr, li, m * m * r, r / lead, if resolved { "" } else { "  UNRESOLVED" });
            if resolved && m >= 40.0 { lx.push(m.ln()); ly.push(r.ln()); }
            if m == 640.0 { rel640 = r / lead; }
        }
        let s = if lx.len() >= 2 { slope(&lx, &ly) } else { f64::NAN };
        let p1 = rel640 < 0.05;
        let p2 = (-2.2..=-1.8).contains(&s);
        println!("  (i) |R(640)|/|lead| = {rel640:.3e} < 0.05: {}   (ii) slope over resolved m >= 40 ({} points) = {s:.4} in [-2.2, -1.8]: {}   unresolved: {unresolved}",
            if p1 { "PASS" } else { "FAIL" }, lx.len(), if p2 { "PASS" } else { "FAIL" });
        all_pass &= p1 && p2 && uniq;
        if ci == 0 {
            let (lr, li) = leading(c, 640.0, false);
            let k = ms.len() - 1;
            let r = ((i2[k].0 - lr).powi(2) + (i2[k].1 - li).powi(2)).sqrt();
            c5_rel = r / (lr * lr + li * li).sqrt();
        }
    }
    let c5_fails = c5_rel > 0.5;
    println!("== C5 control (C1 without e^(i pi sgn/4)): |R(640)|/|lead| = {c5_rel:.3e} > 0.5 (must fail (i)): {}",
        if c5_fails { "yes, discriminating" } else { "NO: NOT DISCRIMINATING" });
    println!("RESULT {}", if all_pass && c5_fails { "PASS" } else if !c5_fails { "NOT DISCRIMINATING" } else { "FAIL" });
}
