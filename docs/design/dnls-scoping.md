# Scoping: from dispersive decay to nonlinear lattice dynamics (discrete NLS)

Status: **scoping, not a commitment** (owner request 2026-11-12, "bet 2"). Written by the session-10 lead. Nothing here
is frozen or proved. Promotion follows ROADMAP "Candidates" (four gates).

Revised 2026-11-12 after the adversarial review of batch HC (`review/2026-11-12-HC-post-proof-answers.md`, finding 1):
the first version's admissibility condition "σ < 1 and σ(2p − 1) > 1" was only sufficient; it wrongly excluded d = 3 and
said nothing for d ≥ 4. The condition below, σ(2p − 1) > 1, holds in every dimension.

## Goal

Batches LE2 and HC give explicit, machine-checked bounds for the lattice kernel on ℤ^d (TdE′):

  |K_d(t, x)| ≤ C*^d t^{−d/3} for t > 0, C* = 8(1 + √7)/3.

With the discrete Laplacian (Δu)(x) = Σ_j (u(x + e_j) + u(x − e_j) − 2u(x)), the kernel of e^{itΔ} is
(2π)^{−d} e^{−2idt} K_d(2t, x) (a hand computation, not formalised). It would give the ℓ¹ → ℓ^∞ decay

  ‖e^{itΔ} f‖_∞ ≤ (2π)^{−d} C*^d (2|t|)^{−d/3} ‖f‖_1.

**Only the kernel bound is machine-checked.** The identification of the kernel with the group e^{itΔ}, and hence the
ℓ¹ → ℓ^∞ bound for the group, is a planned lemma (ingredient 2 below).

The classical next step is nonlinear: small solutions of the discrete nonlinear Schrödinger equation (DNLS),

  i u̇ + Δu + λ|u|^{2p}u = 0, u(0) = u₀, on ℤ^d, λ ∈ ℝ, p ≥ 1 an integer,

disperse like the linear flow when the nonlinearity is weak enough. DNLS models:
- coupled optical waveguide arrays;
- Bose–Einstein condensates in deep optical lattices;
- molecular chains.

A machine-checked theorem of this kind would be OscInt's first statement about a **nonlinear** evolution equation.

## Prior art (logged 2026-11-12)

- **A. Stefanov and P. G. Kevrekidis**, *Asymptotic behaviour of small solutions for the discrete nonlinear Schrödinger
  and Klein–Gordon equations*, Nonlinearity 18 (2005) 1841–1857, arXiv nlin/0409009 (CITED-ABSTRACT: read at abstract
  level). They prove:
  - the ℓ¹ → ℓ^∞ decay (1 + |t|)^{−d/3}, with a non-explicit constant;
  - restricted Strichartz estimates;
  - energy (excitation) thresholds for localized solutions.
- According to a web-search summary of a 2012 paper by T. Mizumachi (title and venue not recorded; CITED-UNREAD), the
  earlier work proved scattering of small ℓ² data for 2p + 1 ≥ 7 using Strichartz estimates. Later work also uses the
  Stefanov–Kevrekidis decay, for example Kevrekidis–Pelinovsky–Stefanov (2009/10) on asymptotic stability of small
  bound states (CITED-UNREAD).
- **Formalisation:** no Lean or Mathlib formalisation of Strichartz estimates or of a dispersive nonlinear PDE theorem
  was found. A web-search summary reported a February 2026 Lean Zulip thread saying Strichartz estimates and the
  Christ–Kiselev lemma are not in Mathlib; the thread's URL was not recorded and it was not read (CITED-UNREAD).
  Novelty wording if built: "machine-checked, with explicit constants". The mathematics is classical.
- Before any statement is frozen, the Stefanov–Kevrekidis paper and the Mizumachi paper must be read (gate 3).

## Two routes

**Route 1, recommended first: decay bootstrap with no Strichartz estimates.**
- On the lattice ‖·‖_∞ ≤ ‖·‖_2 ≤ ‖·‖_1, so the linear bound improves to
  ‖e^{itΔ}f‖_∞ ≤ min(1, c_d |t|^{−σ}) ‖f‖_1, with σ = d/3.
- Mass ‖u(t)‖_2 = ‖u₀‖_2 is conserved, since the generator is self-adjoint and the nonlinearity is gauge invariant.
- Duhamel and ‖|u|^{2p}u‖_1 ≤ ‖u‖_2² ‖u‖_∞^{2p−1} give, for N(t) = sup_{s≤t} (1 + s)^σ ‖u(s)‖_∞ and a = σ(2p − 1):
  N(t) ≤ c ‖u₀‖_1 + c |λ| ‖u₀‖_2² N(t)^{2p−1} · (1 + t)^σ ∫₀^t min(1, (t − s)^{−σ}) (1 + s)^{−a} ds.
- **The integral is O((1 + t)^{−σ}) whenever a > 1, in every dimension** (PROVEN-BY-HAND, sketch). Split at t/2:
  - on [0, t/2], t − s ≥ t/2, so the factor min(1, (t − s)^{−σ}) is O((1 + t)^{−σ}), and ∫₀^∞ (1 + s)^{−a} ds is finite
    because a > 1;
  - on [t/2, t], (1 + s)^{−a} ≤ c (1 + t)^{−a}, and ∫₀^{t/2} min(1, r^{−σ}) dr is O(t^{1−σ}) for σ < 1, O(log(2 + t))
    for σ = 1, and O(1) for σ > 1. The product is O((1 + t)^{−σ}): for σ < 1 because a > 1; for σ = 1 because a > 1
    absorbs the logarithm; for σ > 1 because a = σ(2p − 1) ≥ σ when p ≥ 1.
- A continuity argument then gives ‖u(t)‖_∞ ≤ 2c ‖u₀‖_1 (1 + t)^{−d/3} for small ‖u₀‖_1 (the constants are to be
  tracked; not yet done).
- Admissible cases, σ(2p − 1) > 1, i.e. real p > (1 + 3/d)/2:
  - d = 1 (σ = 1/3): p > 2, so integer p ≥ 3, the septic nonlinearity and above (the classical threshold 2p + 1 ≥ 7);
  - d = 2 (σ = 2/3): p > 5/4, so p ≥ 2;
  - d = 3 (σ = 1): p > 1, so p ≥ 2; only the cubic case p = 1 is borderline (a = 1, a logarithmic loss);
  - d ≥ 4 (σ > 1): every p ≥ 1.
- Numerical check of the integral bound (FLOAT, not evidence): `numerics/review/hc_interface_checks.py` H3 finds the
  quantity bounded for (σ, a) = (1/3, 5/3), (2/3, 2), (1, 3) and (4/3, 4/3), and growing like log t for the control
  (1, 1).
- Ingredients and their Lean status:
  1. **Well-posedness of DNLS in ℓ²(ℤ^d)** as an ODE in a Banach space. Mathlib has Picard–Lindelöf in Banach spaces
     (`IsPicardLindelof`) and `lp` spaces. The nonlinearity is locally Lipschitz on ℓ², and the solution is global by
     mass conservation. Status: ASSUMED feasible; the Mathlib names have not been `#check`ed (lessons 1).
  2. **The linear group e^{itΔ} on ℓ¹ and ℓ²** as convolution with the kernel. Unitarity on ℓ² comes from Plancherel
     on the torus. Mathlib has Fourier series on `AddCircle` with Parseval, and the bridge to ℤ^d needs a product.
     The ℓ¹ → ℓ^∞ bound comes from TdE′ once the kernel is identified with the group; that identification is a new
     lemma (`examples/consumer/ConsumerLattice.lean` stops short of it, "kernel-defined propagator").
  3. **Duhamel's formula** in ℓ²; the continuity argument is real analysis.
  4. **The integral estimate** above, with explicit constants. Elementary.
- Effort estimate: large but bounded. Items 1–2 are the infrastructure; item 2 is the risky one.

**Route 2, later: discrete Strichartz estimates.**
- These are the non-endpoint TT* estimates from decay plus unitarity (Keel–Tao style).
- They need interpolation (Riesz–Thorin or Marcinkiewicz) on ℓ^p and a discrete Hardy–Littlewood–Sobolev inequality
  in time.
- They give small-ℓ² data results with lower powers.
- Mathlib status of Riesz–Thorin: not checked (ASSUMED absent).
- Much larger. Route 1 should prove the infrastructure first.

## Candidate first statement (draft, not frozen)

DNLS-S. For every d ≥ 1, λ ∈ ℝ and integer p ≥ 1 with (d/3)(2p − 1) > 1, there are explicit ε₀ > 0 and C such that
every u₀ ∈ ℓ¹(ℤ^d) with ‖u₀‖_1 ≤ ε₀ gives a global ℓ² solution with sup_x |u(t, x)| ≤ C ‖u₀‖_1 (1 + t)^{−d/3} for all
t ≥ 0.

Bite data:
- the standing-wave (breather) obstruction: for λ ≠ 0 and large data there are spatially localized solutions
  u(t, x) = e^{iωt} φ(x), which do not decay, so a smallness condition is necessary. For λ > 0 (focusing in this sign
  convention) φ solves Δφ − ωφ + λ|φ|^{2p}φ = 0 with ω > 0; for λ < 0 the staggering map u(x) ↦ (−1)^{x₁+⋯+x_d} u(x),
  with a gauge factor, exchanges the signs (FOLKLORE, not checked here). The excitation thresholds of
  Stefanov–Kevrekidis make the size quantitative (CITED-ABSTRACT);
- d = 3, p = 1 (a = 1): no decay claim is made.

## Gates

- Gate 1 (need): a named consumer (photonics, cold atoms) or the owner's decision.
- Gate 2: met for the mathematics (classical; re-derive Route 1 with explicit constants first).
- Gate 3: logged above, at abstract or search-summary level only. The two papers named above must be read before any
  statement is frozen.
- Gate 4: owner.
- Recommended next step: a route document for infrastructure items 1–2, with every Mathlib name `#check`ed. That step
  is the go/no-go.
