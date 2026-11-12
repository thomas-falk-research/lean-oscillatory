# Scoping: from dispersive decay to nonlinear lattice dynamics (discrete NLS)

Status: **scoping, not a commitment** (owner request 2026-11-12, "bet 2"). Written by the session-10 lead. Nothing here
is frozen or proved. Promotion follows ROADMAP "Candidates" (four gates).

## Goal

Batches LE2 and HC give explicit, machine-checked ℓ¹ → ℓ^∞ decay for the free lattice Schrödinger group on ℤ^d:

  ‖e^{itΔ} f‖_∞ ≤ (2π)^{−d} C*^d (2|t|)^{−d/3} ‖f‖_1, C* = 8(1 + √7)/3,

where Δ is the discrete Laplacian. The kernel is (2π)^{−d} e^{−2idt} K_d(2t, x), up to sign conventions, and TdE′ bounds
K_d. The classical next step is nonlinear: small solutions of the discrete nonlinear Schrödinger equation (DNLS),

  i u̇ + Δu + λ|u|^{2p}u = 0, u(0) = u₀, on ℤ^d,

disperse like the linear flow when the nonlinearity is weak enough. DNLS models:
- coupled optical waveguide arrays;
- Bose–Einstein condensates in deep optical lattices;
- molecular chains.

A machine-checked theorem of this kind would be OscInt's first statement about a **nonlinear** evolution equation.

## Prior art (logged 2026-11-12; read at abstract or search-summary level, CITED-ABSTRACT)

- **A. Stefanov and P. G. Kevrekidis**, *Asymptotic behaviour of small solutions for the discrete nonlinear Schrödinger
  and Klein–Gordon equations*, Nonlinearity 18 (2005) 1841–1857, arXiv nlin/0409009. They prove:
  - the ℓ¹ → ℓ^∞ decay (1 + |t|)^{−d/3}, with a non-explicit constant;
  - restricted Strichartz estimates;
  - energy (excitation) thresholds for localized solutions.
- Later work uses these estimates, for example Kevrekidis–Pelinovsky–Stefanov (2009/10) on asymptotic stability of
  small bound states. Mizumachi (2012) records small-ℓ² scattering for 2p + 1 ≥ 7 via Strichartz.
- **Formalisation:** no Lean or Mathlib formalisation of Strichartz estimates or of a dispersive nonlinear PDE theorem
  was found. A February 2026 Lean Zulip thread notes Strichartz and Christ–Kiselev are not in Mathlib.
  Novelty wording if built: "machine-checked, with explicit constants". The mathematics is classical.

## Two routes

**Route 1, recommended first: decay bootstrap with no Strichartz estimates.**
- On the lattice ‖·‖_∞ ≤ ‖·‖_2 ≤ ‖·‖_1, so the linear bound improves to
  ‖e^{itΔ}f‖_∞ ≤ min(1, c_d |t|^{−σ}) ‖f‖_1, with σ = d/3.
- Mass ‖u(t)‖_2 = ‖u₀‖_2 is conserved, since the generator is self-adjoint and the nonlinearity is gauge invariant.
- Duhamel and ‖|u|^{2p}u‖_1 ≤ ‖u‖_2² ‖u‖_∞^{2p−1} give, for N(t) = sup_{s≤t} (1 + s)^σ ‖u(s)‖_∞:
  N(t) ≤ c ‖u₀‖_1 + c |λ| ‖u₀‖_2² N(t)^{2p−1} ∫₀^t min(1, (t − s)^{−σ}) (1 + s)^{−σ(2p−1)} ds · (1 + t)^σ.
- The integral is O((1 + t)^{−σ}) when σ < 1 and σ(2p − 1) > 1.
- A continuity argument then gives ‖u(t)‖_∞ ≤ 2c ‖u₀‖_1 (1 + t)^{−d/3} for small ‖u₀‖_1.
- Admissible cases:
  - d = 1 (σ = 1/3): p ≥ 3, the septic nonlinearity and above, matching the classical threshold 2p + 1 ≥ 7;
  - d = 2 (σ = 2/3): p ≥ 2;
  - d = 3: σ = 1 is borderline, a log loss, so it is excluded or done separately.
- Ingredients and their Lean status:
  1. **Well-posedness of DNLS in ℓ²(ℤ^d)** as an ODE in a Banach space. Mathlib has Picard–Lindelöf in Banach spaces
     (`IsPicardLindelof`) and `lp` spaces. The nonlinearity is locally Lipschitz on ℓ², and the solution is global by
     mass conservation. Status: ASSUMED feasible; the Mathlib names have not been `#check`ed (lessons 1).
  2. **The linear group e^{itΔ} on ℓ¹ and ℓ²** as convolution with the kernel. Unitarity on ℓ² comes from Plancherel
     on the torus. Mathlib has Fourier series on `AddCircle` with Parseval, and the bridge to ℤ^d needs a product.
     The ℓ¹ → ℓ^∞ bound comes from TdE′, and the identification of the kernel with the group is a new lemma
     (`examples/consumer/ConsumerLattice.lean` stops short of it, "kernel-defined propagator").
  3. **Duhamel's formula** in ℓ²; the continuity argument is real analysis.
  4. **The integral estimate** for the two-power convolution. This is elementary and has explicit constants.
- Effort estimate: large but bounded. Items 1–2 are the infrastructure; item 2 is the risky one.

**Route 2, later: discrete Strichartz estimates.**
- These are the non-endpoint TT* estimates from decay plus unitarity (Keel–Tao style).
- They need interpolation (Riesz–Thorin or Marcinkiewicz) on ℓ^p and a discrete Hardy–Littlewood–Sobolev inequality
  in time.
- They give small-ℓ² data results with lower powers.
- Mathlib status of Riesz–Thorin: not checked (ASSUMED absent).
- Much larger. Route 1 should prove the infrastructure first.

## Candidate first statement (draft, not frozen)

DNLS-S. For d ∈ {1, 2} and p with (d/3)(2p − 1) > 1, there are explicit ε₀ > 0 and C such that every u₀ ∈ ℓ¹(ℤ^d) with
‖u₀‖_1 ≤ ε₀ gives a global ℓ² solution with sup_x |u(t, x)| ≤ C ‖u₀‖_1 (1 + t)^{−d/3} for all t ≥ 0.

Bite data:
- the flat-band/standing-wave obstruction: large data have stationary breathers, so a smallness condition is necessary;
- p below the threshold: no decay claim is made.

## Gates

- Gate 1 (need): a named consumer (photonics, cold atoms) or the owner's decision.
- Gate 2: met for the mathematics (classical; re-derive Route 1 with explicit constants first).
- Gate 3: logged above, at abstract level only. The two papers must be read before any statement is frozen.
- Gate 4: owner.
- Recommended next step: a route document for infrastructure items 1–2, with every Mathlib name `#check`ed. That step
  is the go/no-go.
