# S4.4 proof route (closed forms of the D4 constant)

Statement: `OscInt.Statements.D4ConstantClosedFormStatement` (frozen, stamp `20261106T081634Z-e2d7771c358e`,
pre-proof FAITHFUL ×2). Blueprint parts E1–E7: `Blueprint/D4ClosedForm.lean`. Assembly:
`OscInt.D4.d4ConstantClosedForm_of` (`OscInt/D4/ClosedForm.lean`), machine-checked against E1, E2, E3, E5, E6c, E7
before any part was proved; E4 (`cubicForm_cubicComp`, `disc_cubicComp`, by `ring`) and E7 (`gammaSixth`) are
proved by the lead. E6a and E6b are inputs to E1 and E6c and are separate parts so that those proofs can start
at once (they take them as hypotheses).

Notation: C = cubicForm q, g(θ) = C(cos θ, sin θ), J(C) = angularMoment q = ∫₀^{2π} |g|^{−2/3},
p(u) = C(1, u) = a + bu + cu² + du³, K(C) = lineMoment q = ∫_ℝ |p|^{−2/3}. Normal forms
N₊ = x(x² + y²) = (1, 0, 1, 0), disc −4, and N₋ = xy(x + y) = (0, 1, 1, 0), disc 1.

## Change from the hand-off route
The hand-off proposed I = Γ(2/3)/2 "by an Abel limit of `Complex.integral_cpow_mul_exp_neg_mul_Ioi`" with rate ε − i. At
Mathlib `56a0058` that lemma requires a **real** rate r > 0 (checked with `#check`, 2026-11-06), so a complex rate
needs analytic continuation in r. E1 below uses only real Gamma integrals and the Beta integral E6a, which the
normal forms need anyway.

## Assembly (lead, checked)
For disc C < 0: E5 gives g with C ∘ g = N₊, det g ≠ 0. E3: J(C) = |det g| J(N₊). E2 and E6c:
J(N₊) = 2√π Γ(1/6)/Γ(2/3). E4: disc N₊ = (det g)⁶ disc C, so |disc C|^{1/6} |det g| = 4^{1/6} = 2^{1/3}. With E1,
c_C = (Γ(2/3)/2) |det g| 2√π Γ(1/6)/(3Γ(2/3)) = |det g| √π Γ(1/6)/3, and E7 (√π Γ(1/6) = √3 Γ(1/3)²/2^{1/3})
turns this into Γ(1/3)²/(√3 |disc C|^{1/6}). For disc C > 0: N₋, J(N₋) = 6Γ(1/3)²/Γ(2/3), disc N₋ = 1, so
c_C = |det g| Γ(1/3)² = Γ(1/3)²/disc(C)^{1/6}.

## E1 (cosine moment): `cosMoment = Γ(2/3)/2`, given E6a
1. For u > 0: u^{−1/3} = Γ(1/3)^{−1} ∫₀^∞ s^{−2/3} e^{−us} ds (`Real.Gamma_eq_integral` and
   `MeasureTheory.integral_comp_mul_left_Ioi`).
2. For R > 0, Fubini on (0, R) × (0, ∞) (the absolute integrand s^{−2/3}e^{−us} has iterated integral
   Γ(1/3)∫₀^R u^{−1/3} du < ∞): cosMomentPartial R = Γ(1/3)^{−1} ∫₀^∞ s^{−2/3} h_R(s) ds,
   h_R(s) = ∫₀^R cos u e^{−su} du = (s − e^{−Rs}(s cos R − sin R))/(1 + s²) (FTC: the derivative of
   e^{−su}(sin u − s cos u)/(1 + s²) is cos u · e^{−su}).
3. R → ∞ by dominated convergence (`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`):
   |s^{−2/3} h_R(s)| ≤ s^{−2/3}(2s + 1)/(1 + s²), integrable on (0, ∞) (≤ 3 s^{−2/3} on (0, 1], ≤ 3 s^{−5/3} on
   [1, ∞)); pointwise limit s^{1/3}/(1 + s²).
4. ∫₀^∞ s^{1/3}/(1 + s²) ds = ½ ∫₀^∞ t^{−1/3}(1 + t)^{−1} dt (t = s², `MeasureTheory.integral_comp_rpow_Ioi_of_pos`)
   = ½ Γ(2/3)Γ(1/3)/Γ(1) (E6a with a = 2/3, b = 1/3).
5. So cosMomentPartial → Γ(2/3)/2, hence `cosMoment = Γ(2/3)/2` (`Filter.Tendsto.limUnder_eq`).
Numerical check: Γ(1/3)^{−1}∫₀^∞ s^{1/3}/(1 + s²) ds = 0.6770589697131 = Γ(2/3)/2.

## E2 (chart u = tan θ): `angularMoment q = 2 * lineMoment q` for disc q ≠ 0
1. C(−z) = −C(z) (`OscInt.D4.PolarAux.cubicForm_neg`) gives |g(θ + π)| = |g(θ)|, so θ ↦ |g θ|^{−2/3} has period π and
   ∫₀^{2π} = 2 ∫_{−π/2}^{π/2} (`Function.Periodic.intervalIntegral_add_eq`, `intervalIntegral.integral_add_adjacent_intervals`;
   interval integrability from S4.3, `OscInt.d4ConstantPos`).
2. On Ioo(−π/2, π/2) = arctan '' univ (`Real.range_arctan`, `Real.arctan_injective`, `Real.hasDerivAt_arctan`):
   `MeasureTheory.integral_image_eq_integral_abs_deriv_smul` gives ∫_{Ioo} F = ∫_ℝ (1 + u²)^{−1} F(arctan u).
3. cos(arctan u) = 1/√(1 + u²), sin(arctan u) = u/√(1 + u²) (`Real.cos_arctan`, `Real.sin_arctan`), so
   g(arctan u) = (1 + u²)^{−3/2} p(u) and |g(arctan u)|^{−2/3} = (1 + u²) |p(u)|^{−2/3} (for p(u) = 0 both sides
   are 0, Lean's `0 ^ (−2/3) = 0`). The factors cancel. Interval integral over [−π/2, π/2] = set integral over Ioo
   (endpoints null).
Numerical check: J(xy(x + y))/2 = 15.89974877 = K(xy(x + y)).

## E3 (GL₂ covariance): `angularMoment (cubicComp q g) = angularMoment q / |det2 g|`
1. G(q) := ∫_{ℝ²} exp(−|C(z)|^{2/3}) dz. Polar coordinates (`integral_comp_polarCoord_symm`; C(rω) = r³C(ω),
   `OscInt.D4.PolarAux.cubicForm_polar`) and ∫₀^∞ r e^{−r² a} dr = 1/(2a) for a > 0 give J(C) = 2 G(C) for disc ≠ 0. The
   set {θ : g θ = 0} is null (its points are simple zeros of g by C3, `OscInt.D4.circleNondeg`, hence isolated,
   hence countable; or: for cos θ ≠ 0, g θ = cos³θ · p(tan θ) with p a nonzero polynomial). Tonelli in `lintegral`
   form avoids integrability side conditions; the angular integrand is integrable by S4.3.
2. Linear change of variables on ℝ² (`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar`, the
   volume on ℝ × ℝ is an add-Haar measure): G(C ∘ g) = G(C)/|det g|; `cubicForm_cubicComp` (E4a) identifies
   C ∘ lin2 g with `cubicForm (cubicComp q g)`; `disc_cubicComp` (E4b) gives disc(C ∘ g) ≠ 0.
Numerical check (breakpoints at the zeros of g): q = (1.3, −0.7, 2.1, 0.4), g = (0.9, 1.7, −0.6, 0.8):
5.2420192044 vs 5.2420192079; q = (1, 0, −3, 0.5), g = (2, 1, 1, 3): 2.9458982677 vs 2.9458982696.

## E5 (normal forms): disc < 0 ⇒ ∃ g, det g ≠ 0 ∧ C ∘ g = N₊; disc > 0 ⇒ ∃ g, det g ≠ 0 ∧ C ∘ g = N₋
1. g(θ + π) = −g(θ), so by the intermediate value theorem g has a zero θ₀ ∈ [0, π]. With
   g₁ = (sin θ₀, cos θ₀, −cos θ₀, sin θ₀) (columns (sin θ₀, −cos θ₀) and v = (cos θ₀, sin θ₀), det 1),
   C ∘ g₁ = (a₁, b₁, c₁, 0) since its y³ coefficient is C(v) = 0.
2. disc(a₁, b₁, c₁, 0) = c₁²(b₁² − 4a₁c₁) ≠ 0, so c₁ ≠ 0. The shear (x, y) ↦ (x, y − (b₁/2c₁)x)
   (g = (1, 0, −b₁/(2c₁), 1), det 1) gives (a₂, 0, c₁, 0), a₂ = a₁ − b₁²/(4c₁), disc = −4a₂c₁³.
3. disc < 0 ⇔ a₂c₁ > 0. Scaling (x, y) ↦ (αx, βy) gives (a₂α³, 0, c₁αβ², 0); take α the real cube root of 1/a₂
   (sign of a₂, |a₂|^{−1/3}) and β = |c₁α|^{−1/2}: the result is (1, 0, sign(a₂c₁), 0). So disc < 0 gives N₊, and
   disc > 0 gives x(x² − y²) = (1, 0, −1, 0).
4. x(x² − y²) ∘ (x + y, x − y) = 4xy(x + y); compose with the scaling 4^{−1/3}. Composition: `cubicComp`
   respects composition of `lin2` maps and `det2` is multiplicative (both by `ring`).

## E6 (Beta integrals and the two normal forms)
E6a. ∫₀^∞ t^{a−1}(1 + t)^{−(a+b)} dt = Γ(a)Γ(b)/Γ(a + b) for a, b > 0: Γ(a + b)(1 + t)^{−(a+b)} =
     ∫₀^∞ y^{a+b−1} e^{−(1+t)y} dy (`Real.Gamma_eq_integral`, `integral_comp_mul_left_Ioi`); Tonelli
     (nonnegative integrands) and ∫₀^∞ t^{a−1} e^{−ty} dt = Γ(a) y^{−a} give Γ(a)Γ(b).
E6b. ∫₀¹ x^{a−1}(1 − x)^{b−1} dx = Γ(a)Γ(b)/Γ(a + b): `Complex.Gamma_mul_Gamma_eq_betaIntegral`,
     `Complex.Gamma_ofReal`, `Complex.ofReal_cpow` on [0, 1].
E6c. p₊(u) = 1 + u²: K = 2∫₀^∞ (1 + u²)^{−2/3} du (even), = ∫₀^∞ t^{−1/2}(1 + t)^{−2/3} dt (t = u²)
     = Γ(1/2)Γ(1/6)/Γ(2/3) = √π Γ(1/6)/Γ(2/3) (E6a with a = 1/2, b = 1/6; `Real.Gamma_one_half_eq`).
     p₋(u) = u + u²: ℝ = (−∞, −1) ∪ [−1, 0] ∪ (0, ∞). On (0, ∞): E6a with a = b = 1/3. On (−∞, −1): u ↦ −1 − u
     preserves |u(1 + u)| and maps it to (0, ∞). On (−1, 0): u ↦ −u and E6b with a = b = 1/3. Total
     3Γ(1/3)²/Γ(2/3). Integrability on each piece: a Bochner integral that is nonzero is of an integrable function
     (`MeasureTheory.Integrable.of_integral_ne_zero`), or bound directly.
Numerical check: K(1 + u²) = 7.28595194 = √π Γ(1/6)/Γ(2/3); K(u + u²) = 15.8997487 = 3Γ(1/3)²/Γ(2/3).

## E7 (lead, proved): √π Γ(1/6) = √3 Γ(1/3)²/2^{1/3}
Duplication at 1/6 (`Real.Gamma_mul_Gamma_add_half`) and reflection at 1/3 (`Real.Gamma_mul_Gamma_one_sub`,
`Real.sin_pi_div_three`). `OscInt.D4.gammaSixth`.

Numerical checks above are tooling, not evidence (mpmath, 25 digits, `scratch`; the committed validation of the
closed forms is `numerics/results-d4const-2026-11-06.txt`).

## Revision after the route referee (`review/2026-11-06-S44-proof-route.md`, 2026-11-06)
E1, E2, E3, E5, E6a, E6b, E6c TRUE as stated; one BLOCKER, no MAJOR. Adopted:
1. BLOCKER: `OscInt.Blueprint.NormalFormFacts` already existed (`Blueprint/StationaryPhase.lean`, the L2 normal
   form); E5 is renamed `CubicNormalFormFacts` everywhere. The lead had elaborated the blueprint against
   `OscInt.Statements.D4Limit` only; from now on a new blueprint and assembly are elaborated against
   `import OscInt` and `import Blueprint` before review (lessons 19).
2. Names: `OscInt.D4.PolarAux.cubicForm_neg`, `OscInt.D4.PolarAux.cubicForm_polar`
   (`cubicForm q (r * cos θ, r * sin θ) = r ^ 3 * circleCubic q θ`), `Complex.integral_cpow_mul_exp_neg_mul_Ioi`
   (corrected in the text above).
3. E1, E6a: `Real.integral_rpow_mul_exp_neg_mul_Ioi` (`∫ t in Ioi 0, t ^ (a - 1) * exp (-(r * t)) =
   (1 / r) ^ a * Gamma a` for `0 < a`, `0 < r`) gives the Gamma representation in one step.
4. E3: polar coordinates integrate over `polarCoord.target = Ioi 0 ×ˢ Ioo (-π) π`; one more periodicity step (period
   2π) reaches `angularMoment`. The null zero set is `OscInt.D4.circleZerosNull` (already proved: `disc q ≠ 0 →
   volume {θ | circleCubic q θ = 0} = 0`). Radial integral: `integral_rpow_mul_exp_neg_mul_rpow` (p = 2, q = 1);
   template `Complex.integral_exp_neg_mul_rpow`. Determinant: `lin2 g` as `Matrix.toLin (Module.Basis.finTwoProd ℝ)
   (Module.Basis.finTwoProd ℝ) !![g₁, g₂; g₃, g₄]` (`Matrix.toLin_finTwoProd_apply`), `LinearMap.det_toLin`,
   `Matrix.det_fin_two_of`; add-Haar instance `Measure.prod.instIsAddHaarMeasure`; then `integral_map`,
   `integral_smul_measure` or their `lintegral` versions; back to Bochner by `ofReal_integral_eq_lintegral_ofReal`.
5. E2: `integral_add_adjacent_intervals` needs interval integrability: `(OscInt.d4ConstantPos.2.2 q hq).1` and
   `IntervalIntegrable.mono_set`.
6. E6c: integrability of each piece by `MeasureTheory.Integrable.of_integral_ne_zero` (set integrals) and
   `intervalIntegral.intervalIntegrable_of_integral_ne_zero` (the piece over (−1, 0)), applied after computing it;
   split ℝ by `intervalIntegral.integral_Iic_add_Ioi` or `setIntegral_union` with `Set.Iic_union_Ioi`;
   `integral_comp_neg_Ioi` is in the root namespace.
7. E5: the zero θ₀ by `intermediate_value_Icc` or `intermediate_value_Icc'` according to the sign of g(0); the cube
   root as `SignType.sign a₂ * |a₂| ^ (-(1:ℝ)/3)`, never `a₂ ^ (-(1:ℝ)/3)` (`Real.rpow` of a negative base).

## Change during the proof (agent K, 2026-11-06)
E6a was proved by the substitution x = t/(1 + t) from E6b (`integral_image_eq_integral_abs_deriv_smul`) instead of
Tonelli; the Prop is unchanged and both are in `OscInt/D4/Beta.lean`.
