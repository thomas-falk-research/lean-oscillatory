#![forbid(unsafe_code)]
//! Numerical probes of the OscInt statements (IEEE-754 binary64, round-to-nearest; tooling, never evidence for a
//! theorem). Integrals by composite Simpson; each value is computed at n and 2n nodes and the difference is
//! printed as `err`, an estimate (not a bound) of the quadrature error. A probe FAILs if a stated constant is
//! exceeded by more than that error estimate.
//!
//! Part 1 (explicit constants, S1): ratio |∫ e^{iφ}ψ| / bound over sweeps of the frequency and a linear term.
//! Part 2 (rates, S2–S4, constants existential): sup over p of m^r |∫∫ e^{im(Ψ+p·k)} A| for growing m, and the
//! D4 limit t^{2/3} ∫∫ e^{itφ} A → Γ(1/3)²/(√3 |Disc|^{1/6}) A(0).

#[derive(Clone, Copy)]
struct C(f64, f64);
impl C {
    fn abs(self) -> f64 { self.0.hypot(self.1) }
    fn mul(self, o: C) -> C { C(self.0 * o.0 - self.1 * o.1, self.0 * o.1 + self.1 * o.0) }
}
fn cis(t: f64) -> C { C(t.cos(), t.sin()) }

fn simpson(f: &dyn Fn(f64) -> C, a: f64, b: f64, n: usize) -> C {
    let n = n + n % 2;
    let h = (b - a) / n as f64;
    let (mut re, mut im) = (0.0, 0.0);
    for i in 0..=n {
        let w = if i == 0 || i == n { 1.0 } else if i % 2 == 1 { 4.0 } else { 2.0 };
        let v = f(a + h * i as f64);
        re += w * v.0;
        im += w * v.1;
    }
    C(re * h / 3.0, im * h / 3.0)
}

/// Value and error estimate (difference between n and 2n nodes).
fn integral(f: &dyn Fn(f64) -> C, a: f64, b: f64, n: usize) -> (C, f64) {
    let x = simpson(f, a, b, n);
    let y = simpson(f, a, b, 2 * n);
    (y, C(y.0 - x.0, y.1 - x.1).abs())
}

/// Smooth bump exp(-1/(1-s²)) on (-1, 1).
fn bump(s: f64) -> f64 { if s.abs() >= 1.0 { 0.0 } else { (-1.0 / (1.0 - s * s)).exp() } }

fn gamma_one_third() -> f64 {
    // Γ(1/3) = 3 Γ(4/3); Γ(4/3) = ∫_0^∞ e^{-u³} du (substitute u = t^{1/3}), integrated on [0, 6].
    let f = |u: f64| C((-u * u * u).exp(), 0.0);
    3.0 * integral(&f, 0.0, 6.0, 20_000).0 .0
}

struct Row { name: String, worst: f64, err: f64 }

fn s1_probes() -> Vec<Row> {
    let lams = [1.0, 3.0, 10.0, 30.0, 100.0, 300.0, 1e3, 3e3, 1e4];
    let mut rows = Vec::new();
    let mut run = |name: &str, f: &dyn Fn(f64, f64) -> (C, f64, f64)| {
        let (mut worst, mut err) = (0.0f64, 0.0f64);
        for &l in &lams {
            for k in -8..=8 {
                let (v, e, bound) = f(l, k as f64 / 4.0);
                if v.abs() / bound > worst { worst = v.abs() / bound; err = e / bound; }
            }
        }
        rows.push(Row { name: name.into(), worst, err });
    };
    let nodes = |l: f64, span: f64| (200.0 * (1.0 + l) * span) as usize + 2000;
    // First derivative: φ = λ(x + x² + p'x) on [0,1] with p' = |p|, so φ' = λ(1 + 2x + |p|) ≥ λ(1+|p|) =: ν, φ' monotone.
    run("S1 k=1  φ=λ(x+x²+|p|x) on [0,1], ψ=1, bound 3/ν", &|l, p| {
        let q = p.abs();
        let (v, e) = integral(&|x| cis(l * (x + x * x + q * x)), 0.0, 1.0, nodes(l * (3.0 + q), 1.0));
        (v, e, 3.0 / (l * (1.0 + q)))
    });
    run("S1 k=1  same phase, ψ=1+x², bound 3/ν·(|ψ(1)|+∫|ψ'|)=9/ν", &|l, p| {
        let q = p.abs();
        let (v, e) = integral(&|x| cis(l * (x + x * x + q * x)).mul(C(1.0 + x * x, 0.0)), 0.0, 1.0, nodes(l * (3.0 + q), 1.0));
        (v, e, 9.0 / (l * (1.0 + q)))
    });
    // Second derivative: φ = λx² + λp x on subintervals [a,b] ⊂ [-1,1]; μ = 2λ.
    for (a, b) in [(-1.0, 1.0), (-1.0, 0.3), (0.0, 1.0), (-0.05, 0.05)] {
        run(&format!("S1 k=2  φ=λ(x²+px) on [{a},{b}], ψ=1, bound 8/√μ"), &|l, p| {
            let (v, e) = integral(&|x| cis(l * (x * x + p * x)), a, b, nodes(l * (2.0 + p.abs()), b - a));
            (v, e, 8.0 / (2.0 * l).sqrt())
        });
    }
    run("S1 k=2  φ=λ(x²+px) on [-1,1], ψ=cos x, bound 8/√μ·(cos1+∫|sin|)", &|l, p| {
        let (v, e) = integral(&|x| cis(l * (x * x + p * x)).mul(C(x.cos(), 0.0)), -1.0, 1.0, nodes(l * (2.0 + p.abs()), 2.0));
        (v, e, 8.0 / (2.0 * l).sqrt() * (1f64.cos() + 2.0 * (1.0 - 1f64.cos())))
    });
    // Third derivative: φ = λ(x³ + 3p x) on [-1,1]; |φ'''| = 6λ = μ; p < 0 gives two stationary points, p = 0 a degenerate one.
    run("S1 k=3  φ=λ(x³+3px) on [-1,1], ψ=1, bound 18 μ^{-1/3}", &|l, p| {
        let (v, e) = integral(&|x| cis(l * (x * x * x + 3.0 * p * x)), -1.0, 1.0, nodes(l * (3.0 + 3.0 * p.abs()), 2.0));
        (v, e, 18.0 * (6.0 * l).powf(-1.0 / 3.0))
    });
    run("S1 k=3  same phase, ψ=cos x, bound 18 μ^{-1/3}·(cos1+∫|sin|)", &|l, p| {
        let (v, e) = integral(&|x| cis(l * (x * x * x + 3.0 * p * x)).mul(C(x.cos(), 0.0)), -1.0, 1.0, nodes(l * (3.0 + 3.0 * p.abs()), 2.0));
        (v, e, 18.0 * (6.0 * l).powf(-1.0 / 3.0) * (1f64.cos() + 2.0 * (1.0 - 1f64.cos())))
    });
    rows
}

/// ∫_{-1}^{1} e^{i m g(x)} bump(x) dx.
fn one(m: f64, g: &dyn Fn(f64) -> f64, slope: f64) -> (C, f64) {
    integral(&|x| cis(m * g(x)).mul(C(bump(x), 0.0)), -1.0, 1.0, (40.0 * m * slope) as usize + 4000)
}

/// Separable 2D integral with A(x,y) = bump(x) bump(y): product of two 1D integrals.
fn sep(m: f64, gx: &dyn Fn(f64) -> f64, gy: &dyn Fn(f64) -> f64, slope: f64) -> (C, f64) {
    let (a, ea) = one(m, gx, slope);
    let (b, eb) = one(m, gy, slope);
    (a.mul(b), ea * b.abs() + eb * a.abs() + ea * eb)
}

/// Genuinely 2D Simpson for φ = x²y + y³ (+ p·k), A = bump ⊗ bump.
fn d4_nonsep(t: f64, p: (f64, f64), n: usize) -> C {
    let n = n + n % 2;
    let h = 2.0 / n as f64;
    let w = |i: usize| if i == 0 || i == n { 1.0 } else if i % 2 == 1 { 4.0 } else { 2.0 };
    let (mut re, mut im) = (0.0, 0.0);
    for i in 0..=n {
        let x = -1.0 + h * i as f64;
        let bx = bump(x) * w(i);
        if bx == 0.0 { continue; }
        for j in 0..=n {
            let y = -1.0 + h * j as f64;
            let a = bx * bump(y) * w(j);
            if a == 0.0 { continue; }
            let ph = t * (x * x * y + y * y * y + p.0 * x + p.1 * y);
            re += a * ph.cos();
            im += a * ph.sin();
        }
    }
    C(re * h * h / 9.0, im * h * h / 9.0)
}

fn main() {
    let mut fail = false;
    println!("== Part 1: S1 constants (worst ratio |I|/bound over λ ∈ [1,1e4], 17 linear terms; must be ≤ 1)");
    for r in s1_probes() {
        let ok = r.worst <= 1.0 + r.err;
        fail |= !ok;
        println!("{}  worst {:.4} (err {:.1e})  {}", if ok { "PASS" } else { "FAIL" }, r.worst, r.err, r.name);
    }
    println!("\n== Part 2: rates (sup over p ∈ {{-2,…,2}}², step 0.5, of m^r|I|; bounded in m is the claim)");
    let ps: Vec<f64> = (-4..=4).map(|k| k as f64 / 2.0).collect();
    let cases: [(&str, f64, &dyn Fn(f64) -> f64, &dyn Fn(f64) -> f64); 4] = [
        ("S2  Ψ = x² − y² (indefinite), r = 1", 1.0, &|x| x * x, &|y| -y * y),
        ("S2  Ψ = x² + y² + 10x (large linear term), r = 1", 1.0, &|x| x * x + 10.0 * x, &|y| y * y),
        ("S3  Ψ = y² + x³ (fold at 0), r = 5/6", 5.0 / 6.0, &|x| x * x * x, &|y| y * y),
        ("S4  Ψ = x³ + y³ (D4, Disc = −27), r = 2/3", 2.0 / 3.0, &|x| x * x * x, &|y| y * y * y),
    ];
    for (name, r, gx, gy) in cases {
        print!("{name}:");
        for m in [10.0, 30.0, 100.0, 300.0, 1000.0] {
            let mut sup = 0.0f64;
            let mut err = 0.0f64;
            for &p in &ps {
                for &q in &ps {
                    let (v, e) = sep(m, &|x| gx(x) + p * x, &|y| gy(y) + q * y, 15.0);
                    if v.abs() > sup { sup = v.abs(); err = e; }
                }
            }
            print!("  m={m}: {:.4} (err {:.0e})", sup * m.powf(r), err * m.powf(r));
        }
        println!();
    }
    print!("S4  Ψ = x²y + y³ (D4, Disc = −4), r = 2/3, 2D quadrature:");
    for t in [10.0, 30.0, 100.0, 300.0] {
        let n = (12.0 * t) as usize + 400;
        let mut sup = 0.0f64;
        for &p in &[-2.0, -1.0, 0.0, 1.0, 2.0] {
            for &q in &[-2.0, -1.0, 0.0, 1.0, 2.0] {
                sup = sup.max(d4_nonsep(t, (p, q), n).abs());
            }
        }
        print!("  t={t}: {:.4}", sup * t.powf(2.0 / 3.0));
    }
    println!();
    let g = gamma_one_third();
    let a0 = bump(0.0) * bump(0.0);
    println!("\n== D4 limit: t^{{2/3}} ∫∫ e^{{itφ}} A vs c_C A(0), c_C = Γ(1/3)²/(√3|Disc|^{{1/6}}), Γ(1/3) = {g:.10}");
    for (name, disc) in [("x³ + y³", 27.0f64), ("x²y + y³", 4.0)] {
        let c = g * g / (3f64.sqrt() * disc.powf(1.0 / 6.0)) * a0;
        print!("{name}: c_C A(0) = {c:.6};");
        for t in [100.0, 300.0, 1000.0, 3000.0] {
            let v = if disc == 27.0 {
                sep(t, &|x| x * x * x, &|y| y * y * y, 15.0).0
            } else if t <= 300.0 {
                d4_nonsep(t, (0.0, 0.0), (12.0 * t) as usize + 400)
            } else {
                continue;
            };
            let s = t.powf(2.0 / 3.0);
            print!("  t={t}: {:.6}{:+.6}i", v.0 * s, v.1 * s);
        }
        println!();
    }
    println!("\nRESULT {}", if fail { "FAIL" } else { "PASS (Part 1 constants; Part 2 is a table for inspection)" });
    std::process::exit(fail as i32);
}
