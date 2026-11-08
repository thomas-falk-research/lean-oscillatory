b71615cacaa5b250f625a4f55f0d1ee373f6bd4a

# Blind pre-proof statement review, batch GD: referee A

Reviewed: `OscInt/Statements/Global.lean` at b71615c (HEAD unchanged during the review), against `docs/statements.md` ("Batch GD", front-end batches 2 and 3, S2/S3, S4), with `Family.lean`, `Convert.lean`, `FrontEnd.lean`, `D4Limit.lean`, `StationaryPhase.lean`, `OscInt/Front/GlobalSanity.lean`, `docs/replay/2026-11-08-GD-sanity-plants.txt`, the P1 pre-registration and its results, and lessons 11, 12, 17, 24, 33.

I did not prove any statement under review. Scratch files are under `/tmp/refA/`:
- `chk.lean` checks small facts about definitions: what `∞` elaborates to, how SH parses, the two discriminants, and that `closedBall 0 4` is the box.
- `num.py` checks T6 and T6L numerically through Bessel functions.
- `d4.py` searches numerically for cusps near perturbed D4 points.

One Lean process ran at a time, and I wrote nothing in the repository.

## Summary

All eight statements are **TRUE**. Each is FAITHFUL to the docs and to the classical result. There are **no BLOCKER and no MAJOR findings**. Each statement follows from the frozen statements by the route the docs suggest, and I found no step where that route fails. There are some MINOR findings about sanity coverage and documentation.

## Per statement

### GD-C `GlobalDecayCritStatement`

**Verdict: FAITHFUL (docs). TRUE.**
- The quantifiers are in the right order: `∃ C` comes after Ψ, K, U, K′, D and before A, M, L, m. C does not depend on the amplitude, on L ∈ K′ or on m.
- The rate is `m ^ (-(2:ℝ)/3)`, which equals −2/3.

**Derivation.** It follows from FE-S4.1′L, FE-S3l, a partition of unity, translation invariance and Leibniz bounds.

1. **Near each point of D.** For each k₀ ∈ D (all of D lies in U, so this works even when k₀ ∉ K):
   - Put φ(κ) = Ψ(k₀+κ). It is C⁴ on U − k₀, which is open and contains 0.
   - Its iterated derivatives at 0 are those of Ψ at k₀, so `IsD4Point Ψ k₀` is exactly FE-S4.1′L's hypothesis.
   - The phase becomes m(Ψ(k₀+κ) + L(k₀+κ)) = mφ(κ) + (mL)(κ) + mL(k₀). The constant term gives a unimodular factor.
   - FE-S4.1′L's linear term is not scaled by t, but the statement is uniform over **all** L, so mL is covered. This is uniform in L ∈ K′, and in fact over every L.
   - The amplitude piece χ_{k₀}·A is supported in B̄(k₀, δ). By Leibniz its bound is M times a constant depending on χ.
2. **Away from D.** The remainder (∏(1−χ_{k₀}))·A is supported in the compact set K₁ = K ∖ ⋃ B(k₀, δ′), with K₁ ⊆ U.
   - Every critical point of Ψ + L in K₁ with L ∈ K′ lies in K ∖ D, so `ClassifiedCrit` gives FE-S3l's hypothesis on K₁.
   - FE-S3l gives the rate m^{−5/6}, which is at most m^{−2/3} for m ≥ 1.

**On the cusp question.** H(k) and D³Ψ(k) do not depend on L. So "some critical point of Ψ + L (for some L) is a cusp" is a property of Ψ at a point, not of L.

Near a D4 point there are no cusps, by the following argument:
- H(k₀+κ) = T₀·κ + O(|κ|²), where T₀ = D³Ψ(k₀) and the cubic has nonzero discriminant.
- Up to GL₂, the cubic is x³+y³ or x³−3xy². The condition "D³Ψ[e,e,e] ≠ 0 on ker H" is GL-covariant.
- For x³−3xy²: det H = −36|κ|² + O(|κ|³) < 0, so every point is nondegenerate in a punctured neighbourhood.
- For x³+y³: det H = 36xy + O(|κ|³). Its zero set is close to the axes, the kernel is close to e₂ (resp. e₁), and T[e,e,e] ≈ 6 ≠ 0.

So every point of a punctured neighbourhood of a D4 point is nondegenerate or a fold. The hypothesis near D4 points can therefore always be met, and cusps never make it false there. `d4.py` agrees: for 8 random cubics with quartic perturbations, on circles of radius down to 10⁻³, the minimum |T[e,e,e]| on {det H = 0} stayed bounded away from 0. The docs call this "CONJECTURED" (finding m2).

### GD `GlobalDecayStatement`

**Verdict: FAITHFUL (docs). TRUE.**

The pointwise hypothesis loses nothing. Every k ∈ K is a critical point of Ψ + L for L = −DΨ(k). So "fold or nondegenerate at every point of K ∖ D" is equivalent to "at every critical point, for every L". That is the classical hypothesis for a bound uniform over all L, which is what a dispersive estimate needs.

**Bound over all L, including large ‖L‖.** Let R = sup_K ‖DΨ‖ + 1. R is finite because DΨ is continuous on the open set U ⊇ K and K is compact.
- For ‖L‖ ≤ R, use GD-C with K′ = B̄(0, R) in the dual space. K′ is compact because the dual is finite-dimensional, hence proper. `Classified` implies `ClassifiedCrit`.
- For ‖L‖ > R, ‖DΨ(k) + L‖ ≥ 1 on K. FE-S2.1l with N = 1 applies (C² on U suffices, a C² amplitude is C¹, and the bounds for j ≤ 1 follow) and gives C·M/m ≤ C·M·m^{−2/3}. If that C is negative, replace it by max(C, 0).

No compactness is needed beyond K's. The statement is true.

### GD-F `GlobalFoldStatement`

**Verdict: FAITHFUL. TRUE.** Use FE-S3l with K′ = B̄(0, R) plus FE-S2.1l with N = 1 (m^{−1} ≤ m^{−5/6}). The pointwise hypothesis is again equivalent to the critical-point hypothesis over all L.

### GD-N `GlobalNondegStatement`

**Verdict: FAITHFUL. TRUE.** Use FE-S2.2l with K′ = B̄(0, R) plus FE-S2.1l with N = 1. The rate is `C * M / m`.

### SH `SharpnessStatement`

**Verdict: FAITHFUL. TRUE (elementary).**
- `#print` confirms the parse: the "no faster rate" conjunct sits inside each of the two parts, the real-variable part and the sequence part.
- For m ≤ 0, m^σ is Mathlib's rpow junk value, which is irrelevant under `atTop`.
- First claim: eventually m > 0 and |m^σ I(m)| ≥ |c|/2, which gives the lower bound.
- Second claim: if ‖I m‖ ≤ C m^{−σ′} eventually, then
  - for C < 0 this is impossible, since m^{−σ′} > 0 and norms are nonnegative;
  - for C ≥ 0, |m^σ I(m)| ≤ C m^{σ−σ′} → 0, which forces c = 0, a contradiction.
- `∃ C : ℝ` includes negative C, which is harmless.
- The ℕ version is the form T6L needs.

### T1 `TorusUnfoldStatement`

**Verdict: FAITHFUL. TRUE.**
- `ContDiff ℝ ∞` with `open scoped ContDiff` elaborates to `((⊤ : ℕ∞) : WithTop ℕ∞)`, i.e. C^∞ and not analytic. `chk.lean` checks this by `Iff.rfl` against the explicit `⊤ : ℕ∞` form (lessons 12). Had it meant analytic, a compactly supported η would be 0 and T1 would be false.
- `closedBall (0 : ℝ×ℝ) 4` is [−4,4]², the max-norm ball (checked).
- Construction: η = φ(k₁)φ(k₂), with φ ∈ C_c^∞((−4,4)) and ∑_n φ(·+2πn) = 1. This exists because 8 > 2π.
- Then ∫η g = Σ_n ∫_{box+2πn} η g = ∫_box g · Σ_n η(·+2πn) = ∫_box g, using continuity, periodicity, and the fact that the box boundary is null.
- `∫ k in torusBox` is the Lebesgue (product) measure on ℝ×ℝ.

### T6 `LatticeLaplacianDecayStatement`

**Verdict: FAITHFUL. TRUE (classical).**
- K(t,x) = (2π)² i^{x₁+x₂} J_{x₁}(t) J_{x₂}(t). By Landau's bound, sup_n |J_n(t)| ≤ c t^{−1/3}.
- Numerically, `num.py` gives sup_{0≤n<2t} t^{1/3}|J_n(t)| = 0.685, 0.677, 0.676 at t = 10, 100, 400.
- The sign of x·k does not matter because the statement is uniform over x ∈ ℤ², and the time scale does not matter either.

**Derivable from T1 + GD:**
- g(k) = exp(i(t(cos k₁ + cos k₂) + x·k)) is continuous and 2π-periodic in each variable because x ∈ ℤ².
- Take A = η, K = B̄(0,4), U = ℝ², D = {(±π/2, ±π/2)}, L = x/t.
- `Classified` holds on [−4,4]²:
  - det H = cos k₁ cos k₂. The values ±3π/2 ≈ ±4.71 lie outside the box, so cos k₁ = 0 means k₁ = ±π/2 there.
  - On a fold line, the kernel is e₁ and the third derivative is sin k₁ = ±1.
  - At the four points, H = 0 and D³ = 6(a x³ + d y³) with a, d = ±1/6. `Cubic.discr` = −1/48 ≠ 0 (checked in Lean for (1/6, 0, 0, 1/6)).

**What a dispersive-estimate user still needs.**
- t ≤ −1 follows by conjugation: K(−t, x) = conj K(t, −x).
- |t| < 1 is the trivial bound (2π)².
- The factors (2π)^{−2}, the time scale 2 and the phase e^{−4it} must be inserted.

None of these is lost, but none is stated either (finding n2).

### T6L `LatticeLaplacianLimitStatement`

**Verdict: FAITHFUL. TRUE.**
- (−1)ⁿ K(n,(n,n)) = (2π)² J_n(n)². With J_n(n) ~ Γ(1/3)/(2^{2/3} 3^{1/6} π n^{1/3}), the limit is Γ(1/3)² 2^{2/3}/3^{1/3} = Γ(1/3)² 48^{1/6}/√3 = `d4ClosedConstant (−1/48)` = 7.898993…
- Numerically, `num.py` gives 7.8887, 7.89743, 7.89875, 7.898956 at n = 10, 40, 160, 640. The direct 2D quadrature agrees with (2π)²J_n(n)² at n = 3, 5, 8, so the (−1)ⁿ normalisation is right.
- The casts (n : ℝ) for t and (n : ℤ) for x are right.

**Derivability.** F2 applies to the globally smooth phase φ(κ) = Ψ(k₀+κ) + (κ₁+κ₂) at k₀ = (π/2, π/2):
- After removing the constant phase π (the docs' (−1)ⁿ), φ(0) = 0.
- Dφ(0) = 0 and D²φ(0) = 0, with disc = −1/48.
- On [−4,4]², the only critical point is k₀, and η(k₀) = 1, since the other translates of k₀ lie outside the box.
- The rest is O(n^{−1}) by FE-S2.1l.

## Derivability summary

| Statement | Follows from |
|---|---|
| GD-C | FE-S4.1′L + FE-S3l + partition of unity, translation, Leibniz |
| GD | GD-C with K′ = B̄(0,R) + FE-S2.1l |
| GD-F | FE-S3l + FE-S2.1l |
| GD-N | FE-S2.2l + FE-S2.1l |
| SH | elementary |
| T1 | elementary (bump construction and periodisation, Mathlib-level work) |
| T6 | T1 + GD |
| T6L | F2 + FE-S2.1l (+ T1) |

Nothing stronger than these routes give has slipped in. Nothing a user needs is lost, apart from the documented choices: the rate is 2/3 even when D = ∅, there is no family version, and there is no A₃ statement.

## Vacuity and usefulness

- **cos k₁ + cos k₂** on K = B̄(0,4) with the four D4 points meets every hypothesis of GD, as above.
- **arccos(a cos x + b cos y)** with |a|+|b| < 1 is smooth on ℝ², with Hessian-zero points at (±π/2, ±π/2). The P1 numerics report NFD4, so the hypotheses are expected to be dischargeable.
- No hypothesis is unsatisfiable. In `IsD4Point`, the factor 6 and the existential coefficients do no harm:
  - D³Ψ(k₀) is symmetric at points of U, so coefficients always exist and are unique.
  - Rescaling the factor rescales discr by λ⁴, so "discr ≠ 0" does not depend on it.
- If K = ∅, then A = 0 and the conclusion is trivial, as it should be. D = ∅ is fine.
- D ⊄ K is allowed, which is harmless.

## Sanity theorems and plants (lessons 33)

The sanity theorems go through the frozen constants on closed data. All 10 plants are rejected and all 10 controls accepted, as the replay file records. What they miss:

1. **The only GD and GD-C datum is the elliptic umbilic x³ − 3xy².** It is nondegenerate in a punctured neighbourhood of its D4 point, so there are no fold points at all.
   - A hypothesis-strengthening plant `FoldOrNondegMatrix Ψ k ↦ (hessianMatrix Ψ k).det ≠ 0` inside `Classified` / `ClassifiedCrit` is **not detected**.
   - The hyperbolic case, with fold lines through the D4 point (the lattice case), is not exercised.
   - Datum that separates these roles (lessons 17): x³ + y³ on B̄(0,1) with D = {0}.
2. **`↑D ⊆ U ↦ ↑D ⊆ K` is not detected.** The datum has D = {0} ⊆ K and U = univ. A D point in U ∖ K would separate the two.
3. **As the file says, weakening plants are not detected.** The ones that matter most here:
   - GD-C with `L ∈ K′` dropped from the conclusion's hypotheses. This makes the statement false: a cusp for some L ∉ K′.
   - Any strengthened rate, e.g. GD with −5/6. This is false, since E at L = 0 attains m^{−2/3}.
   - T6 with a faster rate.
   - T6L with a different nonzero constant. Only the numerics test its value. My independent check agrees to 5·10⁻⁶ at n = 640.
4. **Kernel conventions.** `latticeKernel_zero_one` pins the scale of x·k and the box, but not the sign of x·k or the time scale. Both are harmless.

## Findings

**BLOCKER:** none.

**MAJOR:** none.

**MINOR**
- **m1.** `GlobalSanity.lean` exercises GD and GD-C only on `ellPhase` (x³ − 3xy²), which has no fold points. A plant replacing `FoldOrNondegMatrix Ψ k` by `(hessianMatrix Ψ k).det ≠ 0` in `def Classified … (∀ k ∈ K, k ∉ D → FoldOrNondegMatrix Ψ k)` or in `ClassifiedCrit` would pass. Suggestion: add a hyperbolic datum (x³ + y³ on B̄(0,1), D = {0}), or better, cos k₁ + cos k₂ on B̄(0,4), which is the application.
- **m2.** `docs/statements.md` (GD modelling choices) labels "critical points of Ψ + L near a D4 point are folds or nondegenerate" as CONJECTURED. It holds for every D4 point with discr ≠ 0, by the pointwise argument above: H and D³ do not depend on L, and after GL₂ normalisation the punctured neighbourhood is nondegenerate (elliptic) or fold (hyperbolic). The docs could also say that the GD-C/GD hypothesis can fail only at a cusp away from D, never near a D4 point.
- **m3.** The `↑D ⊆ U` versus `↑D ⊆ K` role is not separated by the sanity data (D = {0} ⊆ K, U = univ).

**NIT**
- **n1.** Docs, "every point of K ∖ D … (at every point, not only at critical points)": over all L this is the same condition as the critical-point form, since every k is critical for L = −DΨ(k). Saying so would stop readers from taking GD's hypothesis as stronger than the classical one.
- **n2.** T6 is for `1 ≤ t` only. A consumer note could record K(−t, x) = conj K(t, −x) and the trivial bound for |t| < 1. These are needed for ‖e^{itΔ}‖_{ℓ¹→ℓ^∞} ≲ ⟨t⟩^{−2/3}.
- **n3.** The T6L docstring says "the D4 constant of the cubic (κ₁³ + κ₂³)/6". That matches `IsD4Point`'s a = d = 1/6 and `Cubic.discr` = −1/48, but it would help to say that the coefficients are those of `cubicCoeffs`/F2, i.e. Taylor coefficients D³/6.
