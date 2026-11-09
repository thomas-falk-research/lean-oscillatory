// SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
//
// SPDX-License-Identifier: Apache-2.0

//! Pre-registered check of the decay rate of the QWZ (m = 3) propagator kernel.
//! Protocol: docs/prereg/2026-11-08-VV-qwz-decay.md (registered before this program existed). Tooling, not evidence.
//! Trapezoid rule on the torus by inverse 2D DFT (radix-2 FFT below), f64.

use std::f64::consts::PI;

#[derive(Clone, Copy, Debug, Default)]
struct C {
    re: f64,
    im: f64,
}
impl C {
    fn new(re: f64, im: f64) -> C {
        C { re, im }
    }
    fn add(self, o: C) -> C {
        C::new(self.re + o.re, self.im + o.im)
    }
    fn sub(self, o: C) -> C {
        C::new(self.re - o.re, self.im - o.im)
    }
    fn mul(self, o: C) -> C {
        C::new(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)
    }
    fn scale(self, s: f64) -> C {
        C::new(self.re * s, self.im * s)
    }
    fn abs(self) -> f64 {
        self.re.hypot(self.im)
    }
}

/// In-place radix-2 FFT with sign `s` (+1: sum of e^{+2πi jk/n}).
fn fft(a: &mut [C], s: f64) {
    let n = a.len();
    let mut j = 0;
    for i in 1..n {
        let mut bit = n >> 1;
        while j & bit != 0 {
            j ^= bit;
            bit >>= 1;
        }
        j |= bit;
        if i < j {
            a.swap(i, j);
        }
    }
    let mut len = 2;
    while len <= n {
        let ang = s * 2.0 * PI / len as f64;
        let wl = C::new(ang.cos(), ang.sin());
        for i in (0..n).step_by(len) {
            let mut w = C::new(1.0, 0.0);
            for k in 0..len / 2 {
                let u = a[i + k];
                let v = a[i + k + len / 2].mul(w);
                a[i + k] = u.add(v);
                a[i + k + len / 2] = u.sub(v);
                w = w.mul(wl);
            }
        }
        len <<= 1;
    }
}

/// G(x) = Σ_j e^{i x·k_j} f(k_j) (2π/N)², k_j = −π + 2πj/N, for x in [−N/2, N/2)², from samples f.
/// e^{i x·k_j} = e^{−iπ(x₁+x₂)} e^{2πi x·j/N}; returns a map indexed by (x₁ + N/2, x₂ + N/2).
fn kernel(f: &[C], n: usize) -> Vec<C> {
    let mut a = f.to_vec();
    for r in 0..n {
        fft(&mut a[r * n..(r + 1) * n], 1.0);
    }
    let mut col = vec![C::default(); n];
    for c in 0..n {
        for r in 0..n {
            col[r] = a[r * n + c];
        }
        fft(&mut col, 1.0);
        for r in 0..n {
            a[r * n + c] = col[r];
        }
    }
    let h2 = (2.0 * PI / n as f64).powi(2);
    let mut out = vec![C::default(); n * n];
    for i in 0..n {
        for j in 0..n {
            let x1 = i as i64 - (n / 2) as i64;
            let x2 = j as i64 - (n / 2) as i64;
            let src = (((x1 + n as i64) % n as i64) as usize) * n + ((x2 + n as i64) % n as i64) as usize;
            let sign = if (x1 + x2).rem_euclid(2) == 0 { 1.0 } else { -1.0 };
            out[i * n + j] = a[src].scale(sign * h2);
        }
    }
    out
}

#[derive(Clone, Copy)]
enum Model {
    Qwz,
    Trap,
    Lap,
}

/// The entries of U(t, k) (four for the two-band models, one for the Laplacian).
fn samples(model: Model, t: f64, n: usize) -> Vec<Vec<C>> {
    let ne = if let Model::Lap = model { 1 } else { 4 };
    let mut out = vec![vec![C::default(); n * n]; ne];
    for r in 0..n {
        for c in 0..n {
            let k1 = -PI + 2.0 * PI * r as f64 / n as f64;
            let k2 = -PI + 2.0 * PI * c as f64 / n as f64;
            let idx = r * n + c;
            if let Model::Lap = model {
                let ph = -t * (k1.cos() + k2.cos());
                out[0][idx] = C::new(ph.cos(), ph.sin());
                continue;
            }
            let (d1, d2, d3) = match model {
                Model::Qwz => (k1.sin(), k2.sin(), 3.0 + k1.cos() + k2.cos()),
                _ => (0.5, 0.0, k1.cos() + k2.cos()),
            };
            let w = (d1 * d1 + d2 * d2 + d3 * d3).sqrt();
            let (cs, sn) = ((t * w).cos(), (t * w).sin() / w);
            // U = cos(tω) 1 − i (sin(tω)/ω) H, H = [[d3, d1 − i d2], [d1 + i d2, −d3]]
            let mi = |h: C| C::new(h.im * sn, -h.re * sn); // −i·sn·h
            out[0][idx] = C::new(cs, 0.0).add(mi(C::new(d3, 0.0)));
            out[1][idx] = mi(C::new(d1, -d2));
            out[2][idx] = mi(C::new(d1, d2));
            out[3][idx] = C::new(cs, 0.0).add(mi(C::new(-d3, 0.0)));
        }
    }
    out
}

/// sup over x of the max-entry norm, its location's |x|∞, and the kernels.
fn sup_norm(model: Model, t: f64, n: usize) -> (f64, i64, Vec<Vec<C>>) {
    let ks: Vec<Vec<C>> = samples(model, t, n).iter().map(|f| kernel(f, n)).collect();
    let (mut best, mut at) = (0.0, 0);
    for idx in 0..n * n {
        let v = ks.iter().map(|k| k[idx].abs()).fold(0.0, f64::max);
        if v > best {
            best = v;
            let (i, j) = (idx / n, idx % n);
            at = ((i as i64 - (n / 2) as i64).abs()).max((j as i64 - (n / 2) as i64).abs());
        }
    }
    (best, at, ks)
}

fn slope(xs: &[f64], ys: &[f64]) -> f64 {
    let n = xs.len() as f64;
    let mx = xs.iter().sum::<f64>() / n;
    let my = ys.iter().sum::<f64>() / n;
    let (mut a, mut b) = (0.0, 0.0);
    for (x, y) in xs.iter().zip(ys) {
        a += (x - mx) * (y - my);
        b += (x - mx) * (x - mx);
    }
    a / b
}

fn main() {
    let ts = [1.0, 1.5, 2.0, 3.0, 4.0, 6.0, 8.0, 11.0, 16.0, 23.0, 32.0, 45.0, 64.0];
    let n = 1024;
    println!("qwz_decay (protocol docs/prereg/2026-11-08-VV-qwz-decay.md); N = {n}, f64");
    let mut unresolved = false;
    let mut slopes = vec![];
    let mut profile_ratio = 0.0;
    for (name, model) in [("QWZ m=3", Model::Qwz), ("control L: lattice Laplacian", Model::Lap), ("control S: separable trap", Model::Trap)] {
        println!("== {name}");
        let (mut lx, mut ly, mut prof) = (vec![], vec![], vec![]);
        for &t in &ts {
            let (s, at, _) = sup_norm(model, t, n);
            println!("  t = {t:>5}: sup_x ||G|| = {s:.8e}  at |x|inf = {at:>4}  t^(5/6) sup = {:.6}  t^(2/3) sup = {:.6}", t.powf(5.0 / 6.0) * s, t.powf(2.0 / 3.0) * s);
            if at as usize >= n / 2 - 32 {
                unresolved = true;
                println!("    UNRESOLVED: sup near the edge");
            }
            if t >= 8.0 {
                lx.push(t.ln());
                ly.push(s.ln());
                prof.push(t.powf(5.0 / 6.0) * s);
            }
        }
        // accuracy check at the largest t: N vs 2N
        let tl = *ts.last().unwrap();
        let (_, _, k1) = sup_norm(model, tl, n);
        let (_, _, k2) = sup_norm(model, tl, 2 * n);
        let mut d: f64 = 0.0;
        for e in 0..k1.len() {
            for i in 0..n {
                for j in 0..n {
                    let (ii, jj) = (i + n / 2, j + n / 2);
                    d = d.max(k1[e][i * n + j].sub(k2[e][ii * 2 * n + jj]).abs());
                }
            }
        }
        println!("  accuracy at t = {tl}: max |G_N - G_2N| = {d:.3e} (< 1e-8)");
        if d >= 1e-8 {
            unresolved = true;
            println!("    UNRESOLVED: accuracy");
        }
        let s = slope(&lx, &ly);
        println!("  slope of log sup ||G|| over t in [8, 64] = {s:.5}");
        slopes.push(s);
        if let Model::Qwz = model {
            let mx = prof.iter().cloned().fold(0.0, f64::max);
            let mn = prof.iter().cloned().fold(f64::INFINITY, f64::min);
            profile_ratio = mx / mn;
            println!("  max/min of t^(5/6) sup ||G|| over t in [8, 64] = {profile_ratio:.4}; sup of t^(5/6) sup ||G|| = {mx:.6}");
        }
    }
    let inside = |s: f64| (-0.92..=-0.75).contains(&s);
    let pa = inside(slopes[0]);
    let pb = profile_ratio <= 3.0;
    let cl = !inside(slopes[1]);
    let cs = !inside(slopes[2]);
    println!("(a) QWZ slope {:.5} in [-0.92, -0.75]: {}", slopes[0], if pa { "PASS" } else { "FAIL" });
    println!("(b) QWZ profile ratio {profile_ratio:.4} <= 3: {}", if pb { "PASS" } else { "FAIL" });
    println!("control L slope {:.5} outside [-0.92, -0.75]: {}", slopes[1], if cl { "distinguished (good)" } else { "NOT DISCRIMINATING" });
    println!("control S slope {:.5} outside [-0.92, -0.75]: {}", slopes[2], if cs { "distinguished (good)" } else { "NOT DISCRIMINATING" });
    println!("OVERALL: {}", if pa && pb && cl && cs && !unresolved { "PASS" } else { "NOT PASS (see above)" });
}
