# Proof route: batch GD (GD-C, GD, GD-F, GD-N, SH, T1, T6, T6L)

Drafted by the lead during the pre-proof review window (disclosed, as in batch 3: a route is mathematics with the
Mathlib names it needs, not Lean proof code; no Lean proof of a GD statement exists while the referees run). Every
Mathlib name below is `#check`ed at the pin before an agent uses it (lessons 1, 19); the check output is
`docs/replay/2026-11-08-GD-names.txt`.

## R1. Local D4 pieces at a point k₀ (used by GD-C)
Given Ψ C⁴ on open U, k₀ ∈ U a D4 point. Let φ(κ) = Ψ(k₀ + κ), U₀ = {κ | k₀ + κ ∈ U} (open, ∋ 0). Then φ is C⁴ on U₀
(`ContDiffOn.comp` with the affine map), and `iteratedFDeriv ℝ n φ 0 = iteratedFDeriv ℝ n Ψ k₀` (translation:
`iteratedFDeriv_comp_add_left` or the `fderiv` translation lemmas; name to check). FE-S4.1′L gives δ > 0 and C₀ with
|∫ e^{i(tφ(κ) + L′(κ))} B(κ) dκ| ≤ C₀ M′ t^{−2/3} for every amplitude (2, B̄(0, δ), M′) and every L′.
For an amplitude A₁ supported in B̄(k₀, δ): B(κ) = A₁(k₀ + κ) is supported in B̄(0, δ) with the same derivative bounds
(`iteratedFDeriv` of a translate), and by translation invariance of Lebesgue measure (`MeasureTheory.integral_add_left_eq_self`
for the Haar measure `volume` on ℝ × ℝ)
∫ e^{im(Ψ(k) + L(k))} A₁(k) dk = e^{imL(k₀)} ∫ e^{i(mφ(κ) + (mL)(κ))} B(κ) dκ,
so the piece is ≤ C₀ M₁ m^{−2/3} with L′ = m·L. Uniform over all L (FE-S4.1′L is).

## R2. Cut-offs (GD-C)
D finite. Choose ρ > 0 with ρ ≤ δ(k₀) for each k₀ ∈ D, B̄(k₀, ρ) ⊆ U, and the balls B̄(k₀, ρ) pairwise disjoint (ρ less
than half the minimal distance). χ_{k₀} = a `ContDiffBump` at k₀ with rIn = ρ/2, rOut = ρ (C^∞, values in [0, 1],
= 1 on B̄(k₀, ρ/2), support B̄(k₀, ρ)). Write A = Σ_{k₀ ∈ D} χ_{k₀} A + (1 − Σ χ_{k₀}) A. Leibniz
(`norm_iteratedFDeriv_mul_le`) with the derivative bounds of the bumps (F1 or `ContDiffBump` bounds) gives
derivative bounds C_χ M for every piece. The remainder is supported in K₁ = K \ ⋃ B(k₀, ρ/2) (compact: closed subset
of K); K₁ ∩ D = ∅.

## R3. GD-C assembly
Pieces at D4 points: R1, ≤ C₀ C_χ M m^{−2/3}. Remainder: FE-S3l (`foldOn`) on K₁ ⊆ U with K′: its hypothesis holds
since K₁ ∩ D = ∅ and `ClassifiedCrit`; ≤ C_F C_χ M m^{−5/6} ≤ C_F C_χ M m^{−2/3} for m ≥ 1 (`Real.rpow_le_rpow_of_exponent_le`).
Sum by `MeasureTheory.integral_finsetSum` / `integral_add` (integrable: continuous with compact support) and the
triangle inequality. M ≥ 0 follows from the j = 0 bound.

## R4. GD, GD-F, GD-N: all linear terms
R := 1 + sup_{k ∈ K} ‖DΨ(k)‖ (finite: `fderiv ℝ Ψ` is continuous on U, `ContDiffOn.continuousOn_fderiv_of_isOpen`,
and K is compact, `IsCompact.exists_bound_of_continuousOn`). For ‖L‖ ≥ R: ‖DΨ(k) + L‖ ≥ 1 on K, so FE-S2.1l
(`nonStationaryOn`, N = 1, c = 1) gives ≤ C₁ M m^{−1} ≤ C₁ M m^{−σ} (σ ∈ {2/3, 5/6, 1}). For ‖L‖ ≤ R: K′ = B̄(0, R) in
the dual (compact: finite-dimensional, `ProperSpace`), and the pointwise hypothesis implies the critical-points one;
GD-C (resp. FE-S3l, FE-S2.2l) gives the bound. C = max of the two constants.

## R5. SH
Real variable: eventually m > 0 and ‖m^σ I(m) − c‖ ≤ ‖c‖/2 (`Metric.tendsto_atTop` or `tendsto_iff_norm_sub_tendsto_zero`),
so ‖I(m)‖ ≥ ‖c‖/(2 m^σ) = (‖c‖/2) m^{−σ} (`Real.rpow_neg`). Faster rate: ‖m^σ I(m)‖ ≤ C m^{σ−σ′} → 0
(`tendsto_rpow_neg_atTop`), so the limit c would be 0. Sequences: compose with `tendsto_natCast_atTop_atTop`.

## R6. T1 (unfolding)
h(s) = `Real.smoothTransition` ((s + 1/2)): 0 for s ≤ −1/2, 1 for s ≥ 1/2, C^∞. η₁(s) = h(s + π) − h(s − π): C^∞,
support ⊆ [−π − 1/2, π + 1/2] ⊆ [−4, 4]. For g continuous and 2π-periodic: with G(s) = g(s) h(s + π),
g(s) η₁(s) = G(s) − G(s − 2π) (periodicity), and for b ≥ π + 1/2, a ≥ π + 1/2:
∫_{−a}^{b} (G(s) − G(s − 2π)) ds = ∫_{b−2π}^{b} G − ∫_{−a−2π}^{−a} G = ∫_{b−2π}^{b} g − 0 = ∫_{−π}^{π} g
(`intervalIntegral.integral_comp_sub_right`, `Function.Periodic.intervalIntegral_add_eq`). η(k) = η₁(k₁) η₁(k₂);
Fubini (`MeasureTheory.integral_prod`, `MeasureTheory.setIntegral_prod`) and the 1D identity in each variable.

## R7. The lattice symbol ω = cos k₁ + cos k₂
DΨ(y)v = −sin y₁ v₁ − sin y₂ v₂; D²Ψ(y)[v, w] = −cos y₁ v₁w₁ − cos y₂ v₂w₂; D³Ψ(y)[u, v, w] = sin y₁ u₁v₁w₁ + sin y₂ u₂v₂w₂
(nested `HasFDerivAt` as in `OscInt/Front/ConvertSanity.lean`, then C1/C2 `iteratedFDeriv_two_eq_dd`,
`iteratedFDeriv_three_diag`). Classification on K = B̄(0, 4) (the square [−4, 4]²), D = {(±π/2, ±π/2)}:
cos y₁ cos y₂ ≠ 0 ⇒ nondegenerate; exactly one cosine zero ⇒ fold (kernel the corresponding axis, third derivative
sin = ±1; the span-form lemma for diagonal matrices of `ConvertSanity`); both zero ⇒ y ∈ D (in [−4, 4], cos y = 0 iff
y = ±π/2, `Real.cos_eq_zero_iff`); at D: Hessian 0, cubic (sin y₁ x³ + sin y₂ y³)/6, discriminant −27/36² ≠ 0.

## R8. T6
latticeKernel t x = ∫ η · e^{i(t ω + x·k)} (T1's construction R6, the integrand is continuous and 2π-periodic as
x ∈ ℤ²: `Complex.exp_int_mul_two_pi_mul_I`) = ∫ e^{it(ω(k) + L(k))} η(k) dk with L = (x₁/t) fst + (x₂/t) snd; GD with
A = η (F1 gives M), K = B̄(0, 4), U = ℝ², D from R7.

## R9. T6L
At x = (n, n), t = n: the only critical points of ω + k₁ + k₂ in [−4, 4]² are where sin k₁ = sin k₂ = 1, i.e.
k₀ = (π/2, π/2). Split η = χη + (1 − χ)η with χ a bump at k₀ of radius < δ (from F2 for φ below) and small enough.
(1 − χ)η: no critical point on its support (compact), so ‖D(ω + k₁ + k₂)‖ ≥ c > 0 there (`IsCompact.exists_isMinOn`),
FE-S2.1l with N = 1: O(n^{−1}), and n^{2/3} O(n^{−1}) → 0. χη: translate by k₀; ω(k₀ + κ) + (k₀ + κ)·(1, 1) = π + φ(κ),
φ(κ) = −sin κ₁ − sin κ₂ + κ₁ + κ₂, globally C^∞, φ(0) = 0, Dφ(0) = 0, D²φ(0) = 0, cubic part (κ₁³ + κ₂³)/6,
disc = −1/48. F2 (`d4LimitClosedForm`): t^{2/3} ∫ e^{itφ} B → d4ClosedConstant(−1/48) · B(0), B(0) = χ(k₀) η(k₀) = 1
(η₁(π/2) = h(3π/2) − h(−π/2) = 1). Along integers by composition with `tendsto_natCast_atTop_atTop`; e^{inπ} = (−1)ⁿ.

## Parts for agents (after the review stamp)
- GD-P1 (R1–R3 helpers): translation lemma for the integral and for `iteratedFDeriv`; bump/Leibniz bound
  `∃ C_χ, ∀ A M, …, ‖iteratedFDeriv ℝ j (χ • A) k‖ ≤ C_χ M`; the local D4 piece lemma.
- GD-P2 (R6): T1, with the explicit η exported for R8/R9 (`η₁ (π/2) = 1`, support, smoothness).
- GD-P3 (R7): the classification of ω and the φ data of R9.
- Lead: SH (R5), R3, R4, R8, R9 assemblies.
