# Proof route: front-end batch 2 (C1–C9, C7′, FE-S2.1, FE-S2.2, FE-S3, FE-S4.1′)

Drafted during the statement-review window in the lead's scratch directory (mathematics and Mathlib names only, no
proof code, lessons 23); committed after the blind statement reviews (FAITHFUL ×2, `review/2026-11-07-API2-pre-proof-*.md`).
The C6 certificates were computed with sympy 1.13.3 (scripts kept in the lead's scratch; the identities are re-checked
by `linear_combination` in Lean, which is the evidence).

## Parts (disjoint files under OscInt/API/)

**P-Deriv** (`OscInt/API/ConvertDeriv.lean`): C1, C2, C3, C4.
- C1. `ContDiffAt ℝ 2 Ψ k` ⇒ `fderiv ℝ Ψ` is differentiable at k (`ContDiffAt.fderiv_right`, then
  `.differentiableAt`). `dd Ψ k v w = fderiv (fun y => fderiv Ψ y v) k w = fderiv (fderiv Ψ) k w v`
  (`fderiv_clm_apply` with a constant `v`). `iteratedFDeriv_two_apply`: `D²Ψ(k)[v, w] = fderiv (fderiv Ψ) k v w`.
  Symmetry `IsSymmSndFDerivAt` from `ContDiffAt.isSymmSndFDerivAt` (`minSmoothness ℝ 2 = 2` over ℝ).
- C2. On a neighbourhood U of k, Ψ is C³ (`ContDiffAt.eventually` / `contDiffAt_iff`), so `dd Ψ y u v = D²Ψ(y)[u, v]`
  for y ∈ U by C1; `Filter.EventuallyEq.fderiv_eq` transfers to `ddd`. `fderiv (fun y => D²Ψ(y)[u, v]) k w =
  D³Ψ(k)[w, u, v]` (`iteratedFDeriv_succ_apply_left`, `fderiv_continuousMultilinear_apply_const_apply` or the
  existing `fderiv_iteratedFDeriv_apply` used in `OscInt/StationaryPhase/Implicit.lean`, which needs a local version).
  Full symmetry: `ddd u v w` is symmetric in (u, v) (C1 symmetry at y ∈ U) and in (v, w) (C1 applied to
  `g = fun y => fderiv Ψ y u`, C² near k); the transpositions (12), (23) generate S₃.
- C3. `Matrix.det_fin_two` and C1 with the symmetry of `D²Ψ(k)`.
- C4. With κ = κ₁e₁ + κ₂e₂, expand `D³φ(0)[κ, κ, κ]` by multilinearity (`ContinuousMultilinearMap.map_add`,
  `map_smul` on `Function.update`, or through the curried form `fderiv (fderiv (fderiv φ))`), collect with full
  symmetry, compare with `cubicCoeffs` through C2.

**P-Disc** (`OscInt/API/ConvertDisc.lean`): C5, C6.
- C5. `simp [disc, Cubic.discr]` (definitional up to unfolding).
- C6. `fderiv ℝ (cubicForm q) z = 0` iff `C_x(z) = C_y(z) = 0` (compute the derivative of the polynomial).
  (⇒ of the iff, i.e. disc ≠ 0 ⇒ isolated) Certificate (sympy, checked): with
  A_y = (3abd − 4ac² + b²c)·y + (−2abc + 2b³/3)·x, B_y = (−9a²d + 5abc − 4b³/3)·y + (6a²c − 2ab²)·x,
  A_y C_x + B_y C_y = disc · y³; with
  A_x = (6bd² − 2c²d)·y + (−9ad² + 5bcd − 4c³/3)·x, B_x = (−2bcd + 2c³/3)·y + (3acd − 4b²d + bc²)·x,
  A_x C_x + B_x C_y = disc · x³ (`linear_combination`). A common zero z ≠ 0 forces disc = 0. So for disc ≠ 0 every
  z ≠ 0 has nonzero derivative; `eventually_nhdsWithin_of_forall`.
  (⇐) disc = 0 ⇒ a nonzero critical point z₀, then t z₀ (t → 0⁺) are critical points in every punctured
  neighbourhood (derivative homogeneous of degree 2). Witness z₀, with g = b² − 3ac:
  g ≠ 0: z₀ = ((9ad − bc)/(2g), 1); 4g² C_x(z₀) = −9a·disc, 4g² C_y(z₀) = −3b·disc (checked);
  g = 0, a ≠ 0: z₀ = (−b/(3a), 1); disc = −(27a²d − b³)²/(27a²) when c = b²/(3a), so 27a²d = b³, then C_x = 0 and
  C_y = (27a²d − b³)/(9a²) = 0 (checked);
  a = b = 0: z₀ = (1, 0) (C = y²(cx + dy)).

**P-Fold** (`OscInt/API/ConvertFold.lean`): the linear-algebra core used by C7 and C7′, and C7′ itself. The core,
exactly as the assembly uses it (`OscInt.API.FoldAux.foldCore`):
```lean
theorem foldCore (B : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ) (T : ℝ × ℝ → ℝ) (hB : ∀ v w, B v w = B w v)
    (hT : ∀ (c : ℝ) v, T (c • v) = c ^ 3 * T v) :
    ((B (1, 0) (1, 0) * B (0, 1) (0, 1) - B (1, 0) (0, 1) ^ 2 ≠ 0 ∨
        ((∃ v w, B v w ≠ 0) ∧ ∀ v : ℝ × ℝ, v ≠ 0 → (∀ w, B v w = 0) → T v ≠ 0)) ↔
      FoldCondSpan (Matrix.of fun i j => B (coordVec i) (coordVec j)) (fun e => T (ofFin2 e))) ∧
    ((B (1, 0) (1, 0) * B (0, 1) (0, 1) - B (1, 0) (0, 1) ^ 2 ≠ 0 ∨
        ((∃ v w, B v w ≠ 0) ∧ ∀ v : ℝ × ℝ, v ≠ 0 → (∀ w, B v w = 0) → T v ≠ 0)) ↔
      FoldCondRank (Matrix.of fun i j => B (coordVec i) (coordVec j)) (fun e => T (ofFin2 e)))
```
- Core. For B : E →L E →L ℝ with B v w = B w v (E = ℝ × ℝ) and T3 : E →L E →L E →L ℝ:
  [hessDet-form ≠ 0 ∨ ((∃ v w, B v w ≠ 0) ∧ ∀ v ≠ 0, (∀ w, B v w = 0) → T3 v v v ≠ 0)]
  ↔ FoldCondSpan H T ↔ FoldCondRank H T, with H i j = B (coordVec i) (coordVec j), T e = T3 e' e' e' (e' = ofFin2 e).
  det H = 0 and H ≠ 0 ⇒ ker H is a line (rank–nullity: `Matrix.rank`, `LinearMap.finrank_range_add_finrank_ker`);
  T(c e) = c³ T(e).
- C7 from the core with B = (D²Ψ(k) as a bilinear map), T3 = D³Ψ(k), via C1, C2 (lead's assembly).
- C7′ from the core with B = flip of D₂ k (dd Ψ k v w = D₂ k w v), symmetric by
  `second_derivative_symmetric_of_eventually`; ddd Ψ k v v v = D₃ v v v (`HasFDerivAt.fderiv`, congruence of
  `fun y => dd Ψ y u v` with `fun y => D₂ y v u` everywhere).

**P-Norm** (`OscInt/API/ConvertNorm.lean`): C8, C9.
- C8. For a functional ℓ(h) = a h₀ + b h₁: on `EuclideanSpace ℝ (Fin 2)`, ‖ℓ‖ = √(a² + b²) (upper bound by
  Cauchy–Schwarz and `opNorm_le_bound`, lower bound by the test vector (a, b)); on ℝ × ℝ (max norm), ‖ℓ‖ = |a| + |b|
  (test vector (sign a, sign b)). Chain rule for `Ψ ∘ (x ↦ (x 0, x 1))`.
- C9. (i) `HasCompactSupport.intro`/`of_support_subset_isCompact` with `tsupport ⊆ K`; (ii) F1
  (`OscInt.API.ampBoundOfContDiff`) with K = tsupport A.

**Lead: front ends** (`OscInt/API/Convert.lean`).
- Linear terms: L ↦ p_L = (L e₁, L e₂) is a continuous linear map ((ℝ × ℝ) →L ℝ) → ℝ × ℝ; L k = lin p_L k;
  K′ compact ⇒ image compact. `fderiv Ψ k + L = 0` ⇔ `IsCritical Ψ p_L k`.
- FE-S2.1: S2.1 with Λ = Unit (`sanity_familyCk_const`), c/√2 by C8(iii) (‖fderiv Ψ k + L‖ = ‖fderiv (Ψ + L) k‖).
- FE-S2.2: S2.2 with K′ ↦ image; hessDet = det by C3.
- FE-S3: S3 with Λ = Unit; FoldOrNondeg from FoldOrNondegMatrix by C7.
- FE-S4.1′: dd φ 0 = 0 from D²φ(0) = 0 by C1; cubicCoeffs φ = (a, b, c, d) from C4 and the hypothesis (a binary
  cubic is determined by its values at (1,0), (0,1), (1,1), (1,−1)… solve); disc by C5; S4.1′ with y = p_L.

## After the proofs
- `OscInt/API/ConvertSanity.lean`: derivative-level non-vacuity (fold x³ + y² satisfies FoldOrNondegMatrix on
  closedBall 0 1; x³ − 3xy² + x⁴ satisfies FE-S4.1′'s hypotheses with (1, 0, −3, 0)).
- P2 helpers (`OscInt/API/Poly.lean`, not frozen: they only produce hypotheses): iteratedFDeriv along a line of a
  function whose restriction is a polynomial in t (`iteratedDeriv` of `Polynomial.eval`), polarisation for the
  Hessian, `FoldCondSpan` from an elementary rank-one test.
- `examples/consumer/ConsumerFormula.lean`: FE-S3 and FE-S4.1′ on explicit formulas.
