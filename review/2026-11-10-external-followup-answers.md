# Answers to the external reviewer's follow-up submissions of 2026-11-10

Subject: four packets from the same external reviewer (the one of `review/2026-11-10-external-results-answers.md`),
all against `main` at f63458b. They are not recorded (owner privacy rule, lessons 46). Each claim is restated below in
the lead's words, with the evidence the lead produced. Written by the session-10 lead.

1. A follow-up research packet with two results: a cube-root bound for the 1D lattice kernel with constant
   8(1 + √7)/3 (Result 1), and a sharp localized t^{−4/5} matrix estimate for QWZ at the critical mass m = 2 (Result 2).
2. An audit of that packet, with one further hand-proved theorem: the next term t^{−4/3} on the QWZ rays where the
   leading terms of the two bands cancel.
3. An application study: single-photon propagation in two photonic lattice models, bounded with T0E.
4. An application study: a cold-plasma wave packet bounded with GD-N, and the gyroaverage bounded with T0E.

## Verdict

- **Result 1 is correct and is the most useful item.** The lead re-derived it line by line; no gap was found. It makes
  the explicit lattice bounds useful from t ≈ 3.70 instead of t > 518 (1D) and t > 1321 (2D). By owner decision of
  2026-11-10 it becomes batch LE2 (statements T0E′ and T6E′, `docs/statements.md`), frozen and reviewed before any
  Lean proof. Nothing is proved in Lean yet.
- **Both application studies are correct.** They are careful about scope. Neither shows a device-level, simulation or
  control benefit, and neither claims one. Their main quantitative weakness was T0E's constant, which Result 1 removes.
- Result 2 and the cubic-ray theorem: see their own section below.

## Evidence the lead produced

- **Package integrity.**
  - No archive member has an absolute path, a `..` component or a symlink.
  - The audit packet's SHA-256 is the value its summary states (`49a76685…7b323`). The follow-up packet's is the value
    the audit names (`957cbd5d…17b3`).
  - The follow-up packet's 716-file repository snapshot is identical to the git tree of f63458b: `git hash-object
    --no-filters` of every file against `git ls-tree -r f63458b`, 0 differences.
- **Lead's exact checks:** `numerics/review/followup_checks.py`, record `numerics/results-followup-checks-2026-11-10.txt`.
  - R1a–R1g: every rational and algebraic step of Result 1.
  - Q1–Q3: the two-orbital matrix identities, the T0E usefulness threshold, and the escape-path length of the
    finite-chain comparison.
- **Lean (compiled, not yet replayed):** `OscInt/Front/LatticeCubeRootSanity.lean` proves, unconditionally,
  ‖I(t, 0)‖ ≥ 2π − πt²/2 for every t. At t = (7/8)³ this makes the bound with half the constant false. So the best
  constant exceeds C*/2: Result 1's "within a factor 2 of optimal" is now machine-checked on its lower side.
- **Plasma study:** checked by a fresh-context checker with its own scripts. It found no FATAL or MAJOR issue
  (details below). The lead checked its claims against the Lean statements and read its report.

## Result 1: the cube-root cosine bound, re-derived by the lead

**Claim.** For every t > 0 and every real ξ, |I(t, ξ)| ≤ C* t^{−1/3}, where I(t, ξ) = ∫_{−π}^{π} e^{i(t cos k + ξk)} dk
and C* = 8(1 + √7)/3 ≈ 9.72200.

**Proof, in the lead's words.**
- *Symmetry.* Substituting k ↦ −k gives I(t, −ξ) = I(t, ξ), so take ξ ≥ 0. Put v = ξ/t and g(k) = t(v − sin k), the
  derivative of the phase.
- *One integration by parts on each set where |g| ≥ tδ.* On such an interval [a, b],
  |∫_a^b e^{iφ}| ≤ 1/|g(a)| + 1/|g(b)| + ∫_a^b |g′|/g².
  - The variation integral equals the total variation of 1/g, computed by splitting at ±π/2.
  - Splitting the integral itself at ±π/2 would add boundary terms 2/(t(1 ± v)) that cancel in the exact formula. The
    constant C* needs them to cancel.
  - The boundary values at ±π are 1/(tv) each. Combined, they are 2e^{−it} sin(πξ)/(tv), at most 2/(tv) in size. For
    non-integer ξ they do not vanish; the proof keeps them.
- *Band and cap bounds.* With p = arcsin(v − δ) and q = arcsin(v + δ):
  - band: |I| ≤ 2(q − p) + 8/(tδ) − 4/(t(1 − v²)) + [2/(tv) if v > δ];
  - cap: |I| ≤ π − 2p + 4/(tδ) − 2/(t(1 + v)) + [2/(tv) if v > δ].
  - If v − δ ≥ 1, the whole interval has g > 0. The cap bound with the arcsine term 0 still holds.
- *t ≥ 8, τ = t^{−1/3} ≤ 1/2.*
  - v ≥ 1 − 2τ²: cap with δ = 2τ². Then 2 arccos(1 − 4τ²) = 4 arcsin(√2τ) ≤ 2πτ, so t^{1/3}|I| ≤ 2π + 2 + 2/3 < 9.
  - 1/2 ≤ v < 1 − 2τ²: band with δ = (3/2)τ², and Δ = (1 − v)/τ² > 2.
    - The substitution s = 1 − zτ² and 1 + s ≥ 9/8 give L/τ ≤ (8√2/3)(√(Δ + 3/2) − √(Δ − 3/2)).
    - The other terms add at most 16/3 − 2/Δ + 1.
    - F(Δ) = (8√2/3)(√(Δ + 3/2) − √(Δ − 3/2)) − 2/Δ is decreasing for Δ ≥ 1/2. Its derivative is at most
      2Δ^{−2}(1 − √(2Δ)), by the rationalisation 1/√(Δ − a) − 1/√(Δ + a) ≥ aΔ^{−3/2}.
    - F(2) + 16/3 + 1 = C* exactly (check R1b-F2). **This is the only regime where C* is attained** (as Δ ↓ 2).
  - 0 ≤ v ≤ 1/2: band with δ = (3/2)τ².
    - v ↦ L(v, δ) is increasing and convex, because the arcsine derivative h(s) = (1 − s²)^{−1/2} is even and convex.
    - With the convex term 2τ²/v, the maximum over v ≤ 1/2 is at v = δ or v = 1/2.
    - The chord bounds arcsin(3/4) ≤ 6/7, arcsin(7/8) ≤ 11/10 and arcsin(1/8) ≥ 1/8 come from sin x ≥ x − x³/6.
    - The result is t^{1/3}|I| ≤ max(191/21, 277/30) < 97/10 < C*.
- *3 ≤ t ≤ 8, δ = 1/2.* Each bound has the form A + B/t, and t^{1/3}(A + B/t) is largest at t = 3 or t = 8. The six
  endpoint values (5486/567, 188/21, 4940/567, 65/7, 1742/189, 163/21) are all below 97/10, using π < 22/7 and
  3^{1/3} < 13/9.
- *0 < t ≤ 3.* |I| ≤ 2π and 2π·3^{1/3} < 572/63 < 97/10.

**The lead's checks of the delicate points.**
- The boundary-plus-variation algebra of each set: R1f-3b, 3c, 5.
- The combined endpoint term: R1f-endpts.
- The band substitution and the factor 8√2/3: R1e.
- The cap length at τ = 1/2: R1f-cap21.
- Every rational comparison: R1a–R1d, with √7 and π enclosed exactly (Machin's formula).
- The regimes cover every v ≥ 0 for each t > 0. Every use of the band bound has −1 < v − δ and v + δ < 1. Every use of
  the cap bound has v − δ < 1, or the whole-interval branch.

**How good the constant is.**
- C* > 97/10 (check R1a-97/10).
- The best constant C_opt satisfies C_opt > 4.9336 (the reviewer's Taylor witness at t = 4/5; check R1g, exact).
- C_opt ≥ 2π·0.80366 ≈ 5.0495 (floating point; batch LE review B, at (5.797…, 4.404)).
- So C* is about 1.93 times too large at most. For integer ξ, Landau's constant 2π·0.7857 ≈ 4.937 is better and is
  sharp.

**Bins.**
- Result 1: **result**. Accepted as batch LE2: T0E′ and T6E′ = T6F + T0E′, by owner decision. Frozen LE files are not
  edited. Bite data: half the constant fails (compiled); at t = 0 the bound fails (compiled).
- The reviewer's failed triangular extension (a stationary-phase chart amplitude R^{−1/4} with no uniform C² bound at
  R = 0): **correct as a negative statement**, not a counterexample to anything. It is recorded for ROADMAP I1/I3, not
  acted on.

## The quantum-photonics application study

**What it shows (correct).**
- *One-photon sector.* For a passive number-conserving Hamiltonian, the one-photon sector evolves by e^{−ith}.
- *OAM lattice.* For the homogeneous lossless OAM lattice (negative hopping, as in the published version of the
  source), the site-to-site amplitude is e^{−iω₀t}e^{inφ} I(2κt, n)/(2π). So T0E bounds every single-site transition
  probability by min(1, b(2κt)²), where b = T0E's right side divided by 2π.
- *Two-orbital S/P ladder.* At its zero-detuning parameters (C_s : C_p : C_sp = 1 : −2 : 3/2) the full 2×2 propagator
  has a closed form: e^{izB} = e^{−iτ cos k}[cos 3τ I + i sin 3τ Q(k)], with Q² = I. In a fixed basis the cell-to-cell
  kernel has the entries cos 3τ·b_n and i sin 3τ·b_{n±1}. Its operator norm is therefore ≤ √2 b(τ).

**The lead's checks.**
- All matrix identities: Q1. This includes the ODE −i∂_z E = BE with E(0) = I, and a control showing the wrong
  propagation sign fails.
- The threshold:
  - b(519) < 0.999715 and b(518) > 1.00007 (Q2, exact). So "t > 518", rounded in `docs/HANDOFF.md` and
    `OscInt/Front/LatticeExplicitFinal.lean`, is right to the integer: the first sufficient integer is 519.
  - The reviewer's point is correct. The rounded comment is not a sufficient condition at t = 518.
- The four-site cycle returns exactly at τ = 200π (Q2-cycle).
- In the finite-chain comparison, the shortest walk that leaves [−L, L] has length 2(L + 1) − |m + n| (Q3).

**Its limits (correct as stated by the reviewer).**
- It is an idealised infinite lossless lattice.
- The zero-detuning S/P parameters are the source's effective-ribbon limit, not a demonstrated device.
- Phase-modulated hopping can refocus (|C(t)| = 0), finite chains recur, and flat bands do not disperse. So no
  memory, routing or fidelity claim follows.

**The new constant's effect.**
- With T0E′ the amplitude coefficient is C*/(2π) ≈ 1.5473, useful from τ ≈ 3.70.
- The probability bounds are 0.111 at τ = 100, 0.0239 at τ = 1000 and 0.00516 at τ = 10⁴. With T0E they are 1, 0.619
  and 0.118. Landau's sharp bounds are 0.0287, 0.00617 and 0.00133 (FLOAT, in the record).
- For integer site displacements Landau's classical bound remains better by a factor about 3.9 in probability. OscInt's
  contribution is a machine-checked bound, not a sharper one.

**Bin.**
- Correct application, classical mathematics.
- Candidate: a compiled consumer for the scalar OAM lattice, once T0E′ is proved.
- The two-orbital closed form is model-specific; recorded, no roadmap change.

## The plasma application study

Checked by a fresh-context checker with its own SymPy/mpmath scripts. Each claim was derived before the study's
scripts were compared. The lead read the report and checked the Lean-facing claims against the source.

**Physics.**
- The linear cold collisionless electron plasma with fixed ions and E along z gives
  ∂_t²E_z − c²ΔE_z + ω_p²E_z = 0. The compatible magnetic field, velocity, current, Gauss and continuity equations
  were all checked, with exact residual 0.
- The dispersion relation is ω = (ω_p² + c²|k|²)^{1/2}, and its Hessian determinant (in dimensionless form) is
  (1 + |κ|²)^{−2} > 0.

**Theorem mapping.**
- GD-N (`OscInt/Statements/Global.lean`) chooses C after Ψ, K and U, and before the amplitude, M, the linear term and
  t. The linear term carries the observation point, so the bound is uniform in X.
- −(λ² + |κ|²)^{1/2} is C^∞ on ℝ² for λ > 0.
- The amplitude bounds are on `iteratedFDeriv` in Mathlib's operator norm, over ℝ × ℝ with the max norm.
- The integral is unnormalised; the factor (2π)^{−2} is the user's.
- The uniformity over λ in a compact positive interval was correctly assembled from S2.2F/S2.1F. It needs no ∀∃ swap.

**The explicit packet** A = (1 − |κ|²)³₊.
- A is C², not C³.
- In the max-norm operator norms, the derivative budget is exactly M = 12: the second derivative at 0, with
  H = −6I and h = g = (1, 1). In Euclidean norms it would be 6.
- The centre value reduces exactly to (1/2π)∫_1^{√2} s(2 − s²)³ e^{−iτs} ds.
- Two integrations by parts give the bound 1/(2π(√(τ² + 25) − 5)). This beats the trivial bound for τ > 12 and gives
  ratio ≤ 0.1 from τ ≥ 60√2.
- The leading term −ie^{−iτ}/(2πτ) has an error ≤ 5/(πτ²).
- No violation in 4200 values of τ in [0.1, 10⁶] (mpmath, 50 digits). The actual ratio last exceeds 0.1 at τ ≈ 80.1,
  so 60√2 is sufficient, not sharp.

**Zero-gap obstruction.**
- Confirmed numerically: √τ|w| → 0.012549 along the ray at zero gap, equal to the predicted F(0)/(2π)^{3/2}.
- The positive lower bound on λ is needed.

**Gyroaverage.**
- (1/2π)∫e^{iz cos θ}dθ = J₀(z) is `latticeKernel1 z 0`/(2π).
- T0E gives 1, 0.948 and 0.787 at z = 100, 600, 1000. It crosses 1 at z ≈ 518.525.
- The classical envelope |J₀(z)| ≤ (2/(πz))^{1/2} is true for all z > 0. The study's monotone-quantity proof was
  re-derived. The local maxima of √z|J₀| increase to (2/π)^{1/2} from below.
- With T0E′: 1, 0.718, 0.333, 0.183, 0.155 at z = 1, 10, 100, 600, 1000. That is better than T0E, and still worse than
  the classical envelope.

**Findings.**
- MINOR: Lean's ‖·‖ on ℝ × ℝ is the max norm. A consumer that writes the phase or amplitude with ‖κ‖² would silently
  change both (the phase would not even be smooth). They must be written coordinatewise.
- MINOR: the annular counterexample's derivative budget 960 is valid but loose. The true max-norm budget is ≈ 192.
  The argument is unaffected.

**Bin.**
- Correct application, classical physics and mathematics.
- Candidate: a compiled GD-N consumer for the cold-plasma phase, with the max-norm hazard as a bite datum.
- No plasma-simulation or control claim follows, and none is made.

## On the dimension discussion (the reviewer's correction of its own earlier framing)

The reviewer withdrew its earlier suggestion that reaching 5–6 integration dimensions would by itself give a plasma or
fusion capability. The lead agrees.
- A kinetic phase space of dimension 5 or 6 does not make a 5- or 6-dimensional oscillatory integral. The reviewer's
  free-transport example gives a 3-dimensional integral with a linear phase per Fourier mode.
- ROADMAP I3b already says 5D and 6D are instances of a dimension-generic theorem, with no application claim.
- No change.
