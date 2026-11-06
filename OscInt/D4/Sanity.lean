import OscInt.Statements.D4

/-!
# S4.1 sanity checks

These answer the S4.1 pre-proof referees' NITs (`review/2026-11-06-S4-pre-proof-answers.md`):
* `sanity_D4_generic` checks the argument order of `ddd` in `cubicCoeffs` (and the factors `1/6`, `1/2`) on the
  cubic `x³ + 2x²y + 3xy² + 5y³`, whose four coefficients are distinct and nonzero;
* `sanity_D4_elliptic_excluded` checks that the elliptic umbilic `x³ − 3xy²` (positive discriminant) is excluded
  by the hypothesis `disc < 0`.

Derivatives are computed through explicit `HasFDerivAt` terms, then `dd`, then `ddd`, for a general binary cubic.
-/

namespace OscInt.D4

open OscInt.Statements

/-- The general binary cubic `a x³ + b x²y + c xy² + d y³`. -/
noncomputable def genCubic (a b c d : ℝ) : ℝ × ℝ → ℝ :=
  fun k => a * k.1 ^ 3 + b * k.1 ^ 2 * k.2 + c * k.1 * k.2 ^ 2 + d * k.2 ^ 3

theorem fd_genCubic (a b c d : ℝ) (y v : ℝ × ℝ) :
    fderiv ℝ (genCubic a b c d) y v =
      (3 * a) * v.1 * y.1 ^ 2 + (2 * b) * v.1 * y.1 * y.2 + c * v.1 * y.2 ^ 2 +
        (b * v.2 * y.1 ^ 2 + (2 * c) * v.2 * y.1 * y.2 + (3 * d) * v.2 * y.2 ^ 2) := by
  have h1 := hasFDerivAt_fst (𝕜 := ℝ) (p := y) (E := ℝ) (F := ℝ)
  have h2 := hasFDerivAt_snd (𝕜 := ℝ) (p := y) (E := ℝ) (F := ℝ)
  have h : HasFDerivAt (genCubic a b c d)
      ((3 * a * y.1 ^ 2 + 2 * b * y.1 * y.2 + c * y.2 ^ 2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (b * y.1 ^ 2 + 2 * c * y.1 * y.2 + 3 * d * y.2 ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    unfold genCubic
    convert ((((h1.pow 3).const_mul a).add (((h1.pow 2).const_mul b).mul h2)).add
      (((h1.const_mul c).mul (h2.pow 2)))).add ((h2.pow 3).const_mul d) using 1
    ext <;> simp <;> ring
  rw [h.fderiv]; simp; ring

/-- The general binary quadratic `p x² + q xy + r y²`. -/
theorem fd_genQuad (p q r : ℝ) (y w : ℝ × ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => p * k.1 ^ 2 + q * k.1 * k.2 + r * k.2 ^ 2) y w =
      (2 * p * w.1 + q * w.2) * y.1 + (q * w.1 + 2 * r * w.2) * y.2 := by
  have h1 := hasFDerivAt_fst (𝕜 := ℝ) (p := y) (E := ℝ) (F := ℝ)
  have h2 := hasFDerivAt_snd (𝕜 := ℝ) (p := y) (E := ℝ) (F := ℝ)
  have h : HasFDerivAt (fun k : ℝ × ℝ => p * k.1 ^ 2 + q * k.1 * k.2 + r * k.2 ^ 2)
      ((2 * p * y.1 + q * y.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (q * y.1 + 2 * r * y.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    convert (((h1.pow 2).const_mul p).add ((h1.const_mul q).mul h2)).add ((h2.pow 2).const_mul r) using 1
    ext <;> simp <;> ring
  rw [h.fderiv]; simp; ring

theorem dd_genCubic (a b c d : ℝ) (y u v : ℝ × ℝ) :
    dd (genCubic a b c d) y u v =
      (2 * (3 * a * u.1 + b * u.2) * v.1 + (2 * b * u.1 + 2 * c * u.2) * v.2) * y.1 +
        ((2 * b * u.1 + 2 * c * u.2) * v.1 + 2 * (c * u.1 + 3 * d * u.2) * v.2) * y.2 := by
  have : (fun y : ℝ × ℝ => fderiv ℝ (genCubic a b c d) y u) = fun y =>
      (3 * a * u.1 + b * u.2) * y.1 ^ 2 + (2 * b * u.1 + 2 * c * u.2) * y.1 * y.2 +
        (c * u.1 + 3 * d * u.2) * y.2 ^ 2 := by
    funext y; rw [fd_genCubic]; ring
  rw [dd, this, fd_genQuad]

theorem ddd_genCubic (a b c d : ℝ) (y u v w : ℝ × ℝ) :
    ddd (genCubic a b c d) y u v w =
      (2 * (3 * a * u.1 + b * u.2) * v.1 + (2 * b * u.1 + 2 * c * u.2) * v.2) * w.1 +
        ((2 * b * u.1 + 2 * c * u.2) * v.1 + 2 * (c * u.1 + 3 * d * u.2) * v.2) * w.2 := by
  have : (fun y : ℝ × ℝ => dd (genCubic a b c d) y u v) = fun y =>
      (2 * (3 * a * u.1 + b * u.2) * v.1 + (2 * b * u.1 + 2 * c * u.2) * v.2) * y.1 +
        ((2 * b * u.1 + 2 * c * u.2) * v.1 + 2 * (c * u.1 + 3 * d * u.2) * v.2) * y.2 := by
    funext y; rw [dd_genCubic]
  rw [ddd, this, sanity_fd_lin]

theorem cubicCoeffs_genCubic (a b c d : ℝ) : cubicCoeffs (genCubic a b c d) = (a, b, c, d) := by
  simp only [cubicCoeffs, ddd_genCubic]; norm_num
  exact ⟨by ring, by ring⟩

theorem genCubic_contDiff (a b c d : ℝ) : ContDiff ℝ 4 (genCubic a b c d) := by
  unfold genCubic; fun_prop

theorem dd_genCubic_zero (a b c d : ℝ) (v w : ℝ × ℝ) : dd (genCubic a b c d) 0 v w = 0 := by
  rw [dd_genCubic]; simp

/-- S4.1 `cubicCoeffs` on `x³ + 2x²y + 3xy² + 5y³` (four distinct nonzero coefficients): `(1, 2, 3, 5)`,
discriminant `36 − 108 − 160 − 675 + 540 = −367`. -/
theorem sanity_D4_generic :
    ContDiff ℝ 4 (fun k : ℝ × ℝ => k.1 ^ 3 + 2 * k.1 ^ 2 * k.2 + 3 * k.1 * k.2 ^ 2 + 5 * k.2 ^ 3) ∧
      (∀ v w, dd (fun k : ℝ × ℝ => k.1 ^ 3 + 2 * k.1 ^ 2 * k.2 + 3 * k.1 * k.2 ^ 2 + 5 * k.2 ^ 3) 0 v w = 0) ∧
      cubicCoeffs (fun k : ℝ × ℝ => k.1 ^ 3 + 2 * k.1 ^ 2 * k.2 + 3 * k.1 * k.2 ^ 2 + 5 * k.2 ^ 3) =
        (1, 2, 3, 5) ∧
      disc (cubicCoeffs (fun k : ℝ × ℝ => k.1 ^ 3 + 2 * k.1 ^ 2 * k.2 + 3 * k.1 * k.2 ^ 2 + 5 * k.2 ^ 3)) =
        -367 := by
  have hφ : (fun k : ℝ × ℝ => k.1 ^ 3 + 2 * k.1 ^ 2 * k.2 + 3 * k.1 * k.2 ^ 2 + 5 * k.2 ^ 3) =
      genCubic 1 2 3 5 := by funext k; simp only [genCubic]; ring
  rw [hφ, cubicCoeffs_genCubic]
  refine ⟨genCubic_contDiff _ _ _ _, dd_genCubic_zero _ _ _ _, rfl, ?_⟩
  simp only [disc]; norm_num

/-- The elliptic umbilic `x³ − 3xy²` has cubic coefficients `(1, 0, −3, 0)` and discriminant `108 > 0`, so it is
excluded by the S4.1 hypothesis `disc < 0`. -/
theorem sanity_D4_elliptic_excluded :
    ContDiff ℝ 4 (fun k : ℝ × ℝ => k.1 ^ 3 - 3 * k.1 * k.2 ^ 2) ∧
      (∀ v w, dd (fun k : ℝ × ℝ => k.1 ^ 3 - 3 * k.1 * k.2 ^ 2) 0 v w = 0) ∧
      cubicCoeffs (fun k : ℝ × ℝ => k.1 ^ 3 - 3 * k.1 * k.2 ^ 2) = (1, 0, -3, 0) ∧
      disc (cubicCoeffs (fun k : ℝ × ℝ => k.1 ^ 3 - 3 * k.1 * k.2 ^ 2)) = 108 ∧
      ¬ disc (cubicCoeffs (fun k : ℝ × ℝ => k.1 ^ 3 - 3 * k.1 * k.2 ^ 2)) < 0 := by
  have hφ : (fun k : ℝ × ℝ => k.1 ^ 3 - 3 * k.1 * k.2 ^ 2) = genCubic 1 0 (-3) 0 := by
    funext k; simp only [genCubic]; ring
  have hd : disc ((1, 0, -3, 0) : ℝ × ℝ × ℝ × ℝ) = 108 := by simp only [disc]; norm_num
  rw [hφ, cubicCoeffs_genCubic, hd]
  exact ⟨genCubic_contDiff _ _ _ _, dd_genCubic_zero _ _ _ _, rfl, rfl, by norm_num⟩

end OscInt.D4
