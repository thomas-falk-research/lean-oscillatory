# Answers to the external research packet of 2026-11-12 (tracks B and C: lattice NLS and domain connections)

Subject: one packet from the same external reviewer as `review/2026-11-12-R2-KG-answers.md`, written against this
branch at bd91e2c and `main` at f63458b, in answer to the lead's second research prompt. The packet, the prompt and the
chat are not recorded (owner privacy rule, lessons 46). Each claim is restated below in the lead's words, with the
evidence the lead produced. Written by the session-10 lead.

- **What the reviewer chose.** Track B (nonlinear lattice dynamics, ROADMAP candidate "discrete NLS") and Track C (a
  domain survey). It did not attempt Track A (the A3 cusp parts) or the stretch track.
- **Lean.** The reviewer could not install Lean (HTTP 403 on the toolchain downloads). Its Lean files are proposed
  statement definitions with no proofs, labelled UNCOMPILED.
- **Packaging.** The packet was finished after a workspace interruption, and the reviewer said so. The proof files were
  reconstructed after the interruption; the packet says so too.

## Verdict

**B1, B2, B3 and the standing-wave bite are TRUE (hand proofs; not machine-checked).** The mathematics is classical,
and the reviewer says so. What it adds is an explicit, checkable connection to OscInt's proved constant.
The Lean statement file **does not elaborate** as written (finding 1). Track C is careful and correctly bounded; its
spot-checked claims hold.

### The results, in the lead's words

Δ is the nearest-neighbour Laplacian on ℤ^d, (Δf)(x) = Σ_j (f(x + e_j) + f(x − e_j) − 2f(x)), so that i u̇ + Δu = 0
means u̇ = iΔu. C* = 8(1 + √7)/3 and τ = (C*/(2π))³/2 = 1.85224… < 2.

- **B1, the kernel-to-group identification.** For every real t, every f ∈ ℓ²(ℤ^d) and every site x:

  e^{itΔ}f(x) = Σ_y (2π)^{−d} e^{−2idt} K_d(2t, x − y) f(y),

  with K_d the frozen hypercubic kernel of batch HC and an absolutely convergent series. Consequences:
  - e^{itΔ} is unitary.
  - For d ≥ 1, f ∈ ℓ¹ and t ≠ 0, ‖e^{itΔ}f‖_∞ ≤ min{1, c_d |t|^{−d/3}} ‖f‖_1, with c_d = τ^{d/3}, from TdE′.
  - For every t, the weaker form ‖e^{itΔ}f‖_∞ ≤ L_d (1 + |t|)^{−d/3} ‖f‖_1 holds with L_d = (1 + τ)^{d/3}.

  The proof expands e^{itΔ} as an ℓ¹-convolution exponential and identifies the coefficients by integer Fourier
  orthogonality. This is the bridge that `examples/consumer/ConsumerLattice.lean` stops short of. The kernel formula
  itself is classical (Stefanov–Kevrekidis, eq. (6) of arXiv nlin/0409009v1).
- **B2, global ℓ² dynamics.** For d ≥ 1, integer p ≥ 1, real λ and u₀ ∈ ℓ², the equation
  i u̇ + Δu + λ|u|^{2p}u = 0 has a unique global C¹ solution. Its mass ‖u(t)‖₂ is conserved, and Duhamel's formula
  holds with sign +iλ:

  u(t) = e^{itΔ}u₀ + iλ ∫₀^t e^{i(t−s)Δ} |u(s)|^{2p}u(s) ds.

  The proof is Picard iteration on balls (local Lipschitz constant 4d + |λ|(2p + 1)R^{2p}), then continuation by mass
  conservation.
- **B3, explicit small-data decay.** Let σ = d/3 and a = σ(2p − 1) > 1. The admissible integer pairs are d = 1, p ≥ 3;
  d = 2 or 3, p ≥ 2; and d ≥ 4, p ≥ 1. Then:

  ‖u₀‖₁ ≤ ε₀ implies ‖u(t)‖_∞ ≤ 2L_d ‖u₀‖₁ (1 + t)^{−d/3} for all t ≥ 0,

  where ε₀ = (2^{2p} |λ| J_{σ,a} L_d^{2p−1})^{−1/(2p)} for λ ≠ 0, and J_{σ,a} is an explicit three-case constant.
  - This bound improves on the trivial ‖u(t)‖_∞ ≤ ‖u₀‖₁ for t > 2^{3/d}(1 + τ) − 1; t ≥ 24 suffices in every dimension.
  - **Borderline d = 3, p = 1.** The bootstrap provably fails, even for any weaker power rate: the time integral grows
    like log t. This obstructs the method, not decay. Stefanov–Kevrekidis, Theorem 3 of the arXiv version, already
    covers small ℓ² data there with Strichartz estimates and qualitative decay.
- **The bite (smallness is necessary).** For d = 4, p = 1, λ = 1 and Ω = 4608, a contraction in ℓ¹ produces a real
  φ ∈ ℓ¹ with Δφ − Ωφ + φ³ = 0 and φ(0)² ≥ 40328/9. So u = e^{iΩt}φ is a non-decaying solution in an admissible
  case.

## What the lead checked

**1. Integrity.** The archive's SHA-256 matches the one the owner relayed. The packet's verifier was run on a copy of
the packet, in default mode, under Python 3.13.18 with the packet's pinned numpy, scipy, sympy and mpmath:
- integrity passed before and after;
- all five computation scripts passed.

**2. The lead's re-derivation (by hand).** Every step of B1–B3 and of the bite:
- B1: the kernel identity, its signs, gauge and normalisation, and the envelope constant L_d, attained at |t| = τ.
- B2: the Lipschitz estimate, and the Duhamel sign (from iu̇ = −Δu − λN(u)).
- B3: all three branches of the time-convolution bound, the closing inequality (at the first crossing, the bound is
  at most (3/2)L b₀ < 2L b₀), and the borderline integral 2 log(1 + t)/(t + 2).
- The bite: the linearisation at δ₀, the bound ‖D⁻¹‖ ≤ 1, the contraction constants and the scaling φ = Ω^{1/(2p)} v.

**3. The lead's own checks**, `numerics/review/dnls_checks.py`, written without reusing the packet's code. Record:
`numerics/results-dnls-checks-2026-11-12.txt`, RESULT PASS.
- **D1 (FLOAT):** e^{itΔ}δ₀ by matrix exponential on a periodic box agrees with (2π)^{−d} e^{−2idt} K_d(2t, x), via
  Bessel functions and TdF, to 4.2e−16. This covers d = 1, 2 and t = ±0.7, ±2.9. Dropping the gauge factor or the
  factor 2 is rejected.
- **D2 (EXACT):** C* < 146/15; τ < 2; the bite's 145/288, 73/288 and 40328/9.
- **D3 (FLOAT):** L_d is the supremum of the envelope, attained at t = τ, for d = 1–4.
  - A first run omitted t = τ from its grid and failed D3 at a 1e−6 tolerance for d = 2, 3, 4. The sampled maxima were
    just below L_d.
  - The grid was fixed, and the record says so.
- **D4 (FLOAT):** the time-convolution supremum is below J_{σ,a} for five representative (σ, a); the borderline
  identity holds to 1e−16.
- **D5 (Track C spot checks):**
  - Whistler: h = q²/(1 + q²) has h″(1/√3) = 0, and min |h‴| = 2.04 on [1/2, 2/3], above the packet's 43740/28561.
  - Kelvin wake: the reduced phase has ψ′ = ψ″ = 0 and ψ‴ = −4√6/9 (symbolic) at the cusp line.

**4. Lean, the statement file.** The lead read the packet's two Lean files in full. They contain only definitions and
`#check` commands. Running them was not done: the session's auto-mode classifier blocks executing externally supplied
code, and the lead did not work around it (owner item). Instead the lead compiled a two-line probe of its own,
`def lambdaBinderProbe (λ : Nat) : Nat := λ`, which Lean v4.35.0 rejects with "unexpected token 'λ'; expected '_' or
identifier". The packet's `IsDNLSSolution` and `DNLSGlobalStatement` bind `λ` in exactly this way, so the file cannot
elaborate as written (finding 1).

**5. Prior art, spot-checked in the primary texts** (read by the lead from text extracted from the fetched PDFs):
- **Mielke–Patz**, WIAS preprint 1448, §4.1. The paragraph after the Klein–Gordon theorem says that the 1D theory
  "can be easily transferred" to dNLS with |u|^{β−1}u, and that dispersive stability for β > 4 is "not difficult to
  show". So it is a sketch, not a written proof. In the notation here, β = 2p + 1 > 4 means p ≥ 2 in d = 1, which is
  better than B3's p ≥ 3. The packet reports this correctly.
- **Watabe–Kobayashi–Katori–Konno**, arXiv 0802.2749v3, "Limit distributions of two-dimensional quantum walks". This is
  the Grover-walk source of Track C's C4, as cited.
- **Stefanov–Kevrekidis**, arXiv nlin/0409009v1, Theorem 3 (§4.1), read by the lead.
  - It covers |u|^{2p}u with p ≥ 3/d and small ℓ² data: a unique global solution, Strichartz bounds, and
    ‖u(t)‖_{ℓ^r} → 0 for every r > 2.
  - Its constants are not explicit, and no ℓ^∞ rate is stated there.
  - So every integer pair that B3 covers is already covered qualitatively, and so is d = 3, p = 1, where B3's bootstrap
    fails.
  - B3 adds the explicit rate (1 + t)^{−d/3} for ℓ¹ data with explicit constants.
- **Not re-read by the lead:** the other Track C sources (Eliasson–Shukla, Mouhot–Villani, Nguyen 2026,
  Trombettoni–Smerzi, Liang–Li–Chen, Hong–Yang, Krishnan–Quinto) and the Mizumachi–Pelinovsky paper.

**6. Fresh-context referee** (a Claude instance, like the lead; lessons 48):

| Referee | Launched at commit | Launched | Finished | Run time |
|---|---|---|---|---|
| B1–B3 and the bite | bd91e2c | 20:32:31 | 20:58:08 | 1533 s |

- **Verdicts:** B1, B2, B3 (including the borderline obstruction, as worded) and the bite are TRUE. It found no sign,
  constant or branch error.
- **By hand** it re-derived every constant and sign listed under item 2, independently of the lead.
- **Kernel:** a matrix exponential matches the kernel formula to about 1e−15 in d = 1 (201-site ring) and d = 2
  (31×31 torus, against a direct double integral), and ‖U*U − I‖ ≈ 3e−15.
- **The decay bound:** the ratio of the kernel's supremum to min{1, c_d t^{−d/3}} reaches 0.9999 (d = 1) to 0.9996
  (d = 4) for t ≤ 150, so that envelope is nearly sharp.
- **Constants:** the time-convolution suprema are below J_{σ,a} for five pairs.
- **The bite:** Newton's method on a box gives φ(0)² = 4615.998, above 40328/9.
- **Small-data simulation:** a split-step simulation (d = 2, p = 2 and d = 4, p = 1) stays below the B3 bound, by a
  factor of at least 4. The referee notes that these runs are nearly linear and do not test the bound hard.
- **Lean file:** it independently found the `λ` parse error (finding 1). It also gave the minor findings 2 and 3
  below.

## Findings on the packet

1. **MAJOR (lead; found independently by the referee): the Lean statement file cannot elaborate.** `λ` is the `fun` keyword in Lean 4 and cannot be a
   binder name (checked by the probe above). Other problems cannot be seen until this is fixed. The packet's own
   "source-only syntax review found no defect" did not catch it, which is the risk of uncompiled Lean that the prompt
   warned about. The mathematical results do not depend on the file.
2. **MINOR (referee): `GroupDispersiveStatement` needs `KernelToGroupStatement`.** It quantifies over every Δ with
   the stencil property, so on its own it does not assert that such a Δ exists; the two must be cited together.
   - The existential in `KernelToGroupStatement` is not weak: the stencil property fixes Δ uniquely, as an element of
     lp, so "∃ Δ" and "∀ Δ" are equivalent here (the referee's argument, which the lead accepts).
   - A frozen statement should still name the operator. Then fidelity review is direct.
3. **MINOR (referee): the all-time bound B1.2 has no Lean counterpart.** B3 uses L_d (1 + |t|)^{−d/3}; the candidate
   file states only the min{1, c_d|t|^{−d/3}} form for t ≠ 0.
4. **NOTE: B3 does not extend the known range.**
   - Stefanov–Kevrekidis Theorem 3 covers every pair B3 covers, and also d = 3, p = 1. It does so qualitatively, with
     small ℓ² data.
   - Mielke–Patz (sketch) gives decay with rates for p ≥ 2 in d = 1.
   - The packet says the substance of this itself. B3's contribution is an explicit rate and explicit constants, tied
     to a machine-checked kernel bound.
5. **NOTE: the proofs were reconstructed after the workspace interruption.** The packet says so. The lead checked the
   reconstructed text, which is what is in the archive.

## Scope

- **Mathematics:** B1–B3 as stated.
- **Model:** the idealised homogeneous infinite lattice. For example, coupled waveguide arrays, or a Bose–Einstein
  condensate in a deep optical lattice in the tight-binding approximation. Note that the cubic case (p = 1) is
  admissible only for d ≥ 4, so the physically common cubic DNLS in d ≤ 3 is outside B3 (C3 in the packet says so).
- **Engineering:** none claimed.

## Track C, briefly

The packet maps eight connections. Each is given with its exact integral, singularity class, the OscInt statement that
applies or the gap, the observable, its sources, and an explicit "no advantage claimed" where none is shown.
- **C1.** Whistler waves at the inflection of the parallel branch: an S1.3 consumer (spot-checked above).
- **C2.** Three-dimensional free streaming: FE-S2.1 after a marginalisation step. Not Landau damping.
- **C3.** Linear hopping in an optical lattice: TdE′ plus B1.
- **C4.** The 2D Grover walk: flat bands block decay; projections are needed first.
- **C5.** The Kelvin wake: the cusp line is a fold, A2, for the reduced phase (spot-checked above). Amplitude
  uniformity remains open.
- **C6.** The pinned Klein–Gordon chain: R2, plus the sin(tω)/ω kernel.
- **C7.** Numerical dispersion at fixed mesh: TdE′ plus B1. Not uniform in the mesh.
- **C8.** SAR: the canonical-relation fold is not a scalar OscInt fold; an interface gap.

Its ranking puts the whistler consumer first, then the B1 package (optical hopping and numerical dispersion), then 3D
free streaming. The lead agrees that B1 is the common dependency.

## Proposed next steps (owner decision)

1. **Promote B1** (kernel-to-group identification, plus the ℓ¹ → ℓ^∞ bound for the group) as a batch. It is small, it
   is the dependency shared by C3, C7 and the DNLS candidate, and it turns TdE′ into a statement about the evolution
   group itself. The statement must be written fresh, not taken from the packet (finding 1).
2. **DNLS (B2, B3):** the candidate row is updated with this evidence. Promotion waits on B1 and on the owner. The
   Lean work is ℓ² Picard–Lindelöf with continuation, mass conservation and Duhamel. It is larger than B1.
3. **C1 (whistler)** is a small consumer of the proved S1.3 that could be written as an example without new
   statements.
