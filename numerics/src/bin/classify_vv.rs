// SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
//
// SPDX-License-Identifier: Apache-2.0

//! Numeric classification of critical-point types (N, F, D4, X) of 2D phases.
//! Protocol: docs/prereg/2026-11-08-P1-classify.md (registered before the first run). Tooling, never evidence.
//! f64, closed-form derivatives; no dependencies.

use std::f64::consts::PI;

#[derive(Clone, Copy)]
enum Phase {
    /// x²y + y² (control C of P1).
    Control,
    /// Upper QWZ band √P, P = 2 + m² + 2m(c₁ + c₂) + 2c₁c₂.
    Qwz { m: f64 },
    /// Triangular-lattice symbol c₁ + c₂ + cos(x + y).
    Tri,
    /// Separable-band trap √((c₁ + c₂)² + m²) (control S).
    Trap { m: f64 },
}

/// Value, gradient [px, py], Hessian [pxx, pxy, pyy], third derivatives [pxxx, pxxy, pxyy, pyyy] of the inner
/// function, and whether the outer function is √· (true) or the identity (false).
fn inner(ph: Phase, x: f64, y: f64) -> (f64, [f64; 2], [f64; 3], [f64; 4], bool) {
    let (sx, cx, sy, cy) = (x.sin(), x.cos(), y.sin(), y.cos());
    match ph {
        Phase::Control => (x * x * y + y * y, [2.0 * x * y, x * x + 2.0 * y], [2.0 * y, 2.0 * x, 2.0], [0.0, 2.0, 0.0, 0.0], false),
        Phase::Qwz { m } => (
            2.0 + m * m + 2.0 * m * (cx + cy) + 2.0 * cx * cy,
            [-2.0 * m * sx - 2.0 * sx * cy, -2.0 * m * sy - 2.0 * cx * sy],
            [-2.0 * m * cx - 2.0 * cx * cy, 2.0 * sx * sy, -2.0 * m * cy - 2.0 * cx * cy],
            [2.0 * m * sx + 2.0 * sx * cy, 2.0 * cx * sy, 2.0 * sx * cy, 2.0 * m * sy + 2.0 * cx * sy],
            true,
        ),
        Phase::Tri => {
            let (s, c) = ((x + y).sin(), (x + y).cos());
            (cx + cy + c, [-sx - s, -sy - s], [-cx - c, -c, -cy - c], [sx + s, s, s, sy + s], false)
        }
        Phase::Trap { m } => {
            let w = cx + cy;
            (
                w * w + m * m,
                [-2.0 * w * sx, -2.0 * w * sy],
                [2.0 * sx * sx - 2.0 * w * cx, 2.0 * sx * sy, 2.0 * sy * sy - 2.0 * w * cy],
                [6.0 * sx * cx + 2.0 * w * sx, 2.0 * cx * sy, 2.0 * sx * cy, 6.0 * sy * cy + 2.0 * w * sy],
                true,
            )
        }
    }
}

fn value(ph: Phase, x: f64, y: f64) -> f64 {
    let (p, _, _, _, sq) = inner(ph, x, y);
    if sq { p.sqrt() } else { p }
}

/// Hessian [h11, h12, h22] and third derivatives [t111, t112, t122, t222] by the chain rule.
fn derivs(ph: Phase, x: f64, y: f64) -> ([f64; 3], [f64; 4]) {
    let (p, g, h, t, sq) = inner(ph, x, y);
    let (f1, f2, f3) = if sq { (0.5 * p.powf(-0.5), -0.25 * p.powf(-1.5), 0.375 * p.powf(-2.5)) } else { (1.0, 0.0, 0.0) };
    let hh = |i: usize, j: usize| h[i + j];
    let tt = |i: usize, j: usize, k: usize| t[i + j + k];
    let hm = |i: usize, j: usize| f2 * g[i] * g[j] + f1 * hh(i, j);
    let tm = |i: usize, j: usize, k: usize| {
        f3 * g[i] * g[j] * g[k] + f2 * (hh(i, j) * g[k] + hh(i, k) * g[j] + hh(j, k) * g[i]) + f1 * tt(i, j, k)
    };
    ([hm(0, 0), hm(0, 1), hm(1, 1)], [tm(0, 0, 0), tm(0, 0, 1), tm(0, 1, 1), tm(1, 1, 1)])
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


fn selftest(name: &str, ph: Phase) -> bool {
    let mut st: u64 = 20261108;
    let mut next = || {
        st = st.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        -PI + 2.0 * PI * ((st >> 11) as f64) / ((1u64 << 53) as f64)
    };
    let (mut eh, mut et) = (0.0f64, 0.0f64);
    for _ in 0..200 {
        let x = next();
        let y = next();
        let (h, t) = derivs(ph, x, y);
        for ang in [0.0f64, 0.7, 1.9, 2.6] {
            let u = [ang.cos(), ang.sin()];
            let f = |s: f64| value(ph, x + s * u[0], y + s * u[1]);
            let hq = h[0] * u[0] * u[0] + 2.0 * h[1] * u[0] * u[1] + h[2] * u[1] * u[1];
            let tq = tcube(&t, u);
            let d = 1e-3;
            let fd2 = (-f(2.0 * d) + 16.0 * f(d) - 30.0 * f(0.0) + 16.0 * f(-d) - f(-2.0 * d)) / (12.0 * d * d);
            let e = 1e-2;
            let fd3 = (-f(3.0 * e) + 8.0 * f(2.0 * e) - 13.0 * f(e) + 13.0 * f(-e) - 8.0 * f(-2.0 * e) + f(-3.0 * e))
                / (8.0 * e * e * e);
            eh = eh.max((hq - fd2).abs() / hq.abs().max(1.0));
            et = et.max((tq - fd3).abs() / tq.abs().max(1.0));
        }
    }
    let ok = eh < 1e-5 && et < 1e-4;
    println!("self-test {name}: max rel err Hessian {eh:.3e} (< 1e-5), third {et:.3e} (< 1e-4): {}", if ok { "ok" } else { "DERIVATIVES WRONG" });
    ok
}

fn min_inner(ph: Phase) -> f64 {
    let n = 1024;
    let mut mn = f64::INFINITY;
    for i in 0..n { for j in 0..n {
        let (p, _, _, _, _) = inner(ph, -PI + 2.0 * PI * i as f64 / n as f64, -PI + 2.0 * PI * j as f64 / n as f64);
        mn = mn.min(p);
    }}
    mn
}

fn main() {
    println!("classify_vv (protocol docs/prereg/2026-11-08-VV-classify.md); classifier copied from classify.rs; grid 2048x2048, f64");
    let torus = || Domain { x0: -PI, x1: PI, torus: true };
    let phases: Vec<(String, Phase)> = vec![
        ("Q(m=1): QWZ upper band".into(), Phase::Qwz { m: 1.0 }),
        ("Q(m=0.5): QWZ upper band".into(), Phase::Qwz { m: 0.5 }),
        ("Q(m=3): QWZ upper band".into(), Phase::Qwz { m: 3.0 }),
        ("T: triangular c1 + c2 + cos(x+y)".into(), Phase::Tri),
        ("S(m=0.5): separable-band trap (control)".into(), Phase::Trap { m: 0.5 }),
    ];
    let mut ok = true;
    for (n, ph) in &phases { ok &= selftest(n, *ph); }
    if !ok { println!("STOP: DERIVATIVES WRONG"); return; }
    for (n, ph) in &phases {
        if let Phase::Qwz { .. } | Phase::Trap { .. } = ph { println!("min P on a 1024^2 grid for {n}: {:.6}", min_inner(*ph)); }
    }
    run("C: control x^2 y + y^2 on [-1,1]^2", Phase::Control, Domain { x0: -1.0, x1: 1.0, torus: false });
    for (n, ph) in &phases { run(n, *ph, torus()); }
}
