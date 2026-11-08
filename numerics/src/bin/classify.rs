// SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
//
// SPDX-License-Identifier: Apache-2.0

//! Numeric classification of critical-point types (N, F, D4, X) of 2D phases.
//! Protocol: docs/prereg/2026-11-08-P1-classify.md (registered before the first run). Tooling, never evidence.
//! f64, closed-form derivatives; no dependencies.

use std::f64::consts::PI;

#[derive(Clone, Copy)]
enum Phase {
    /// arccos(a cos x + b cos y); `ident = true` gives a cos x + b cos y (the lattice Laplacian for a = b = 1).
    Comp { a: f64, b: f64, ident: bool },
    /// x²y + y² (control).
    Control,
}

/// Hessian [h11, h12, h22] and third derivatives [t111, t112, t122, t222].
fn derivs(ph: Phase, x: f64, y: f64) -> ([f64; 3], [f64; 4]) {
    match ph {
        Phase::Control => ([2.0 * y, 2.0 * x, 2.0], [0.0, 2.0, 0.0, 0.0]),
        Phase::Comp { a, b, ident } => {
            let u = a * x.cos() + b * y.cos();
            let (f1, f2, f3) = if ident {
                (1.0, 0.0, 0.0)
            } else {
                let w = 1.0 - u * u;
                (-w.powf(-0.5), -u * w.powf(-1.5), -(1.0 + 2.0 * u * u) * w.powf(-2.5))
            };
            let ux = [-a * x.sin(), -b * y.sin()];
            let uxx = [[-a * x.cos(), 0.0], [0.0, -b * y.cos()]];
            let uxxx = |i: usize, j: usize, k: usize| -> f64 {
                if i == j && j == k {
                    if i == 0 { a * x.sin() } else { b * y.sin() }
                } else {
                    0.0
                }
            };
            let h = |i: usize, j: usize| f2 * ux[i] * ux[j] + f1 * uxx[i][j];
            let t = |i: usize, j: usize, k: usize| {
                f3 * ux[i] * ux[j] * ux[k]
                    + f2 * (uxx[i][j] * ux[k] + uxx[i][k] * ux[j] + uxx[j][k] * ux[i])
                    + f1 * uxxx(i, j, k)
            };
            ([h(0, 0), h(0, 1), h(1, 1)], [t(0, 0, 0), t(0, 0, 1), t(0, 1, 1), t(1, 1, 1)])
        }
    }
}

fn det(h: &[f64; 3]) -> f64 { h[0] * h[2] - h[1] * h[1] }
fn tcube(t: &[f64; 4], v: [f64; 2]) -> f64 {
    t[0] * v[0].powi(3) + 3.0 * t[1] * v[0] * v[0] * v[1] + 3.0 * t[2] * v[0] * v[1] * v[1] + t[3] * v[1].powi(3)
}
fn tnorm(t: &[f64; 4]) -> f64 {
    (0..360).map(|i| { let th = i as f64 * PI / 180.0; tcube(t, [th.cos(), th.sin()]).abs() }).fold(0.0, f64::max)
}
fn hnorm(h: &[f64; 3]) -> f64 { (h[0] * h[0] + 2.0 * h[1] * h[1] + h[2] * h[2]).sqrt() }
/// Unit eigenvector of the eigenvalue of smaller absolute value.
fn kernel(h: &[f64; 3]) -> [f64; 2] {
    let (p, q, r) = (h[0], h[1], h[2]);
    let tr = p + r;
    let disc = ((p - r) * (p - r) + 4.0 * q * q).sqrt();
    let l1 = (tr + disc) / 2.0;
    let l2 = (tr - disc) / 2.0;
    let l = if l1.abs() < l2.abs() { l1 } else { l2 };
    // (H - l) v = 0: rows (p - l, q), (q, r - l)
    let v1 = [q, l - p];
    let v2 = [l - r, q];
    let v = if v1[0].hypot(v1[1]) >= v2[0].hypot(v2[1]) { v1 } else { v2 };
    let n = v[0].hypot(v[1]);
    if n == 0.0 { [1.0, 0.0] } else { [v[0] / n, v[1] / n] }
}
/// Discriminant of the binary cubic T[κ,κ,κ]/6 = a x³ + b x²y + c xy² + d y³.
fn cubic_disc(t: &[f64; 4]) -> f64 {
    let (a, b, c, d) = (t[0] / 6.0, t[1] / 2.0, t[2] / 2.0, t[3] / 6.0);
    b * b * c * c - 4.0 * a * c.powi(3) - 4.0 * b.powi(3) * d - 27.0 * a * a * d * d + 18.0 * a * b * c * d
}

struct Domain { x0: f64, x1: f64, torus: bool }

fn dist(dm: &Domain, p: [f64; 2], q: [f64; 2]) -> f64 {
    let mut dx = (p[0] - q[0]).abs();
    let mut dy = (p[1] - q[1]).abs();
    if dm.torus {
        let w = dm.x1 - dm.x0;
        dx = dx.min(w - dx);
        dy = dy.min(w - dy);
    }
    dx.hypot(dy)
}

fn bisect(ph: Phase, mut a: [f64; 2], mut b: [f64; 2]) -> [f64; 2] {
    let mut fa = det(&derivs(ph, a[0], a[1]).0);
    for _ in 0..200 {
        let m = [(a[0] + b[0]) / 2.0, (a[1] + b[1]) / 2.0];
        if (b[0] - a[0]).abs() + (b[1] - a[1]).abs() < 1e-13 { return m; }
        let fm = det(&derivs(ph, m[0], m[1]).0);
        if fm == 0.0 { return m; }
        if (fa < 0.0) == (fm < 0.0) { a = m; fa = fm; } else { b = m; }
    }
    [(a[0] + b[0]) / 2.0, (a[1] + b[1]) / 2.0]
}

/// Gauss–Newton on H = 0 (three equations, two unknowns).
fn newton_h0(ph: Phase, mut p: [f64; 2]) -> [f64; 2] {
    for _ in 0..100 {
        let (h, _) = derivs(ph, p[0], p[1]);
        let e = 1e-7;
        let hx = derivs(ph, p[0] + e, p[1]).0;
        let hxm = derivs(ph, p[0] - e, p[1]).0;
        let hy = derivs(ph, p[0], p[1] + e).0;
        let hym = derivs(ph, p[0], p[1] - e).0;
        let j: Vec<[f64; 2]> = (0..3).map(|i| [(hx[i] - hxm[i]) / (2.0 * e), (hy[i] - hym[i]) / (2.0 * e)]).collect();
        // normal equations
        let (mut a11, mut a12, mut a22, mut b1, mut b2) = (0.0, 0.0, 0.0, 0.0, 0.0);
        for i in 0..3 {
            a11 += j[i][0] * j[i][0]; a12 += j[i][0] * j[i][1]; a22 += j[i][1] * j[i][1];
            b1 += j[i][0] * h[i]; b2 += j[i][1] * h[i];
        }
        let d = a11 * a22 - a12 * a12;
        if d.abs() < 1e-300 { break; }
        let dx = (a22 * b1 - a12 * b2) / d;
        let dy = (a11 * b2 - a12 * b1) / d;
        p = [p[0] - dx, p[1] - dy];
        if dx.abs() + dy.abs() < 1e-15 { break; }
    }
    p
}

/// Newton on (det H, T[w,w,w]) = 0 with the unnormalised kernel vector choice fixed at the start.
fn newton_cusp(ph: Phase, p0: [f64; 2]) -> Option<[f64; 2]> {
    let (h0, t0) = derivs(ph, p0[0], p0[1]);
    let first = (h0[1].hypot(h0[0])) >= (h0[2].hypot(h0[1])); // (q,-p) vs (r,-q)
    let g = |p: [f64; 2]| -> [f64; 2] {
        let (h, t) = derivs(ph, p[0], p[1]);
        let w = if first { [h[1], -h[0]] } else { [h[2], -h[1]] };
        [det(&h), tcube(&t, w)]
    };
    let s1 = hnorm(&h0).powi(2).max(1e-300);
    let s2 = (hnorm(&h0).powi(3) * tnorm(&t0)).max(1e-300);
    let mut p = p0;
    for _ in 0..50 {
        let v = g(p);
        if (v[0] / s1).abs() < 1e-10 && (v[1] / s2).abs() < 1e-10 { return Some(p); }
        let e = 1e-7;
        let gx = g([p[0] + e, p[1]]); let gxm = g([p[0] - e, p[1]]);
        let gy = g([p[0], p[1] + e]); let gym = g([p[0], p[1] - e]);
        let j = [[(gx[0] - gxm[0]) / (2.0 * e), (gy[0] - gym[0]) / (2.0 * e)],
                 [(gx[1] - gxm[1]) / (2.0 * e), (gy[1] - gym[1]) / (2.0 * e)]];
        let d = j[0][0] * j[1][1] - j[0][1] * j[1][0];
        if d.abs() < 1e-300 { return None; }
        let dx = (j[1][1] * v[0] - j[0][1] * v[1]) / d;
        let dy = (j[0][0] * v[1] - j[1][0] * v[0]) / d;
        p = [p[0] - dx, p[1] - dy];
        if !(p[0].is_finite() && p[1].is_finite()) { return None; }
    }
    None
}

fn run(name: &str, ph: Phase, dm: Domain) {
    let n = 2048usize;
    let step = (dm.x1 - dm.x0) / n as f64;
    let np = if dm.torus { n } else { n + 1 };
    let coord = |i: usize| dm.x0 + step * i as f64;
    let mut d = vec![0.0f64; np * np];
    let mut hn = vec![0.0f64; np * np];
    for i in 0..np { for j in 0..np {
        let (h, _) = derivs(ph, coord(i), coord(j));
        d[i * np + j] = det(&h); hn[i * np + j] = hnorm(&h);
    }}
    // Hessian-zero candidates: grid local minima of ‖H‖ below 1e-2 (relative to the median-ish scale 1).
    let mut h0pts: Vec<[f64; 2]> = Vec::new();
    for i in 0..np { for j in 0..np {
        let v = hn[i * np + j];
        if v > 5e-2 { continue; }
        let mut is_min = true;
        for (di, dj) in [(-1i64, 0i64), (1, 0), (0, -1), (0, 1), (-1, -1), (1, 1), (-1, 1), (1, -1)] {
            let (ii, jj) = (i as i64 + di, j as i64 + dj);
            let (ii, jj) = if dm.torus { (((ii + np as i64) % np as i64) as usize, ((jj + np as i64) % np as i64) as usize) }
                else { if ii < 0 || jj < 0 || ii >= np as i64 || jj >= np as i64 { continue; } (ii as usize, jj as usize) };
            if hn[ii * np + jj] < v { is_min = false; }
        }
        if !is_min { continue; }
        let p = newton_h0(ph, [coord(i), coord(j)]);
        let (h, _) = derivs(ph, p[0], p[1]);
        if hnorm(&h) < 1e-6 && !h0pts.iter().any(|q| dist(&dm, *q, p) < 1e-4) { h0pts.push(p); }
    }}
    // Degenerate set: sign changes of det H along grid edges, bisected.
    let mut pts: Vec<[f64; 2]> = Vec::new();
    for i in 0..np { for j in 0..np {
        let a = d[i * np + j];
        let p = [coord(i), coord(j)];
        if a == 0.0 { pts.push(p); continue; }
        let nbrs: [(usize, usize, [f64; 2]); 2] = [
            (if dm.torus { (i + 1) % np } else { i + 1 }, j, [p[0] + step, p[1]]),
            (i, if dm.torus { (j + 1) % np } else { j + 1 }, [p[0], p[1] + step]),
        ];
        for (ii, jj, q) in nbrs {
            if ii >= np || jj >= np { continue; }
            let b = d[ii * np + jj];
            if a * b < 0.0 { pts.push(bisect(ph, p, q)); }
        }
    }}
    let near_h0 = |p: [f64; 2], r: f64| h0pts.iter().any(|q| dist(&dm, *q, p) < r);
    let (mut mf_far, mut at_far, mut mf_all, mut at_all) = (f64::INFINITY, [0.0, 0.0], f64::INFINITY, [0.0, 0.0]);
    let mut cusps: Vec<[f64; 2]> = Vec::new();
    for &p in &pts {
        let (h, t) = derivs(ph, p[0], p[1]);
        if hnorm(&h) < 1e-6 { continue; } // a Hessian-zero point itself
        let f = tcube(&t, kernel(&h)).abs() / tnorm(&t).max(1e-300);
        if f < mf_all { mf_all = f; at_all = p; }
        if !near_h0(p, 0.05) && f < mf_far { mf_far = f; at_far = p; }
        if f < 1e-2 && !near_h0(p, 1e-3) {
            if let Some(c) = newton_cusp(ph, p) {
                if !near_h0(c, 1e-3) && !cusps.iter().any(|q| dist(&dm, *q, c) < 1e-6) { cusps.push(c); }
            }
        }
    }
    println!("== {name}");
    println!("degenerate points refined: {}", pts.len());
    println!("Hessian-zero points: {}", h0pts.len());
    let mut disc_ok = true;
    for p in &h0pts {
        let (_, t) = derivs(ph, p[0], p[1]);
        let rel = cubic_disc(&t).abs() / (tnorm(&t).powi(4)).max(1e-300);
        if rel <= 1e-6 { disc_ok = false; }
        println!("  ({:+.12}, {:+.12}) disc = {:+.6e}  |disc|/|T|^4 = {:.3e}", p[0], p[1], cubic_disc(&t), rel);
    }
    println!("minfold_far = {:.3e} at ({:+.6}, {:+.6})", mf_far, at_far[0], at_far[1]);
    println!("minfold_all = {:.3e} at ({:+.6}, {:+.6})", mf_all, at_all[0], at_all[1]);
    println!("cusp-type common zeros of (det H, T[w,w,w]): {}", cusps.len());
    for c in &cusps { println!("  ({:+.10}, {:+.10})", c[0], c[1]); }
    let verdict = if !cusps.is_empty() { "CUSP" }
        else if disc_ok && mf_far > 1e-3 && mf_all > 1e-3 { "NFD4" } else { "UNCLEAR" };
    println!("VERDICT {name}: {verdict}");
}


/// ∫_{−π}^{π} e^{i(n cos s + n s)} ds by the trapezoid rule with p points (periodic integrand).
fn line_integral(n: f64, p: usize) -> (f64, f64) {
    let h = 2.0 * PI / p as f64;
    let (mut re, mut im) = (0.0, 0.0);
    for j in 0..p {
        let s = -PI + h * j as f64;
        let ph = n * s.cos() + n * s;
        re += ph.cos(); im += ph.sin();
    }
    (re * h, im * h)
}
fn cmul(a: (f64, f64), b: (f64, f64)) -> (f64, f64) { (a.0 * b.0 - a.1 * b.1, a.0 * b.1 + a.1 * b.0) }

fn part_b() {
    let g13: f64 = 2.678938534707747633;
    let cstar = g13 * g13 * 48f64.powf(1.0 / 6.0) / 3f64.sqrt();
    println!("== Part B: (-1)^n n^(2/3) K(n,(n,n)) vs c* = {cstar:.12}");
    let mut prev = f64::INFINITY;
    let (mut mono, mut imag_ok, mut resolved) = (true, true, true);
    let mut last_rel = 0.0;
    for n in [10usize, 40, 160, 640, 2560] {
        let p = 4 * n + 512;
        let a = line_integral(n as f64, p);
        let a2 = line_integral(n as f64, 2 * p);
        let k = cmul(a, a);
        let k2 = cmul(a2, a2);
        let qerr = (k.0 - k2.0).hypot(k.1 - k2.1) / k.0.hypot(k.1);
        if qerr >= 1e-12 { resolved = false; }
        let sgn = if n % 2 == 0 { 1.0 } else { -1.0 };
        let sc = (n as f64).powf(2.0 / 3.0) * sgn;
        let v = (k.0 * sc, k.1 * sc);
        let rel = (v.0 - cstar).hypot(v.1) / cstar;
        if rel >= prev { mono = false; }
        if v.1.abs() >= 1e-9 { imag_ok = false; }
        prev = rel; last_rel = rel;
        println!("n = {n:5}: value = {:+.12} {:+.3e}i  rel.err = {rel:.4e}  quad.check = {qerr:.2e}", v.0, v.1);
    }
    let n = 2559usize;
    let a = line_integral(n as f64, 4 * n + 512);
    let k = cmul(a, a);
    let sc = (n as f64).powf(2.0 / 3.0);
    let ctl = (k.0 * sc - cstar).hypot(k.1 * sc) / cstar;
    println!("control (no (-1)^n, n = 2559): rel.err = {ctl:.4e} (must be > 1)");
    let pass = resolved && last_rel < 0.02 && mono && imag_ok;
    println!("criteria: (i) {} (ii) {} (iii) {} resolved {} control-fails {}", last_rel < 0.02, mono, imag_ok, resolved, ctl > 1.0);
    println!("VERDICT part B: {}", if !(ctl > 1.0) { "NOT DISCRIMINATING" } else if pass { "PASS" } else { "FAIL" });
}

fn main() {
    println!("classify (protocol docs/prereg/2026-11-08-P1-classify.md); grid 2048x2048, f64");
    run("control x^2 y + y^2 on [-1,1]^2", Phase::Control, Domain { x0: -1.0, x1: 1.0, torus: false });
    run("L: cos x + cos y", Phase::Comp { a: 1.0, b: 1.0, ident: true }, Domain { x0: -PI, x1: PI, torus: true });
    for (a, b) in [(0.5, 0.3), (0.45, 0.45), (0.2, 0.7), (-0.3, 0.6), (0.6, -0.35), (0.05, 0.9)] {
        run(&format!("A(a={a}, b={b}): arccos(a cos x + b cos y)"), Phase::Comp { a, b, ident: false },
            Domain { x0: -PI, x1: PI, torus: true });
    }
    part_b();
}
