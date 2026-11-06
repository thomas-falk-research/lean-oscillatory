import OscInt.StationaryPhase.Final

/-!
# S2/S3 bite and exclusion checks

Checks that the proved statements have content and exclude what they should (adversarial review 2026-11-06,
MINOR 8; the probes were written by that referee in `/tmp/adv2/` and are reproduced here, renamed):
* `bite_fold_instance`, `bite_nonStationary_unbounded`: explicit instances derived from the final theorems;
* `cusp_excluded`: the cusp `k₁⁴ + k₂²` (true decay `m^{-3/4}`) fails the fold hypothesis;
* `familyCk_affine_param`: `FamilyCk` is met by a non-constant family over `[0, 1]`, not only by one-point families.
-/

namespace OscInt.StationaryPhase.Sanity

open OscInt.Statements

/-- Bite: S3 instantiated on the fold `k₁³ + k₂²` over `closedBall 0 1`, `K' = {0}`. -/
theorem bite_fold_instance : ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M m : ℝ), AmpBound 2 (Metric.closedBall 0 1) A M → 1 ≤ m →
    ‖oscInt2 (fun k => m * ((k.1 ^ 3 + k.2 ^ 2) + lin 0 k)) A‖ ≤ C * M * m ^ (-(5:ℝ)/6) := by
  obtain ⟨h1, h2, h3, -⟩ := sanity_Fold_hyps
  obtain ⟨C, hC⟩ := OscInt.fold Unit (fun _ => fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 2) _ {0} h1 h2
    isCompact_singleton (fun _ => h3)
  exact ⟨C, fun A M m hA hm => hC A M () 0 m hA rfl hm⟩
/-- Bite: S2.1 with unbounded linear terms (`Ψ = 0`, all `p` with `|p| ≥ 1`, `N = 3`). -/
theorem bite_nonStationary_unbounded : ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (p : ℝ × ℝ) (m : ℝ), AmpBound 3 (Metric.closedBall 0 1) A M →
    1 ≤ p.1 ^ 2 + p.2 ^ 2 → 1 ≤ m →
    ‖oscInt2 (fun k => m * ((fun _ => (0:ℝ)) k + lin p k)) A‖ ≤ C * M / m ^ 3 := by
  obtain ⟨C, hC⟩ := OscInt.nonStationary Unit 3 (fun _ _ => 0) (Metric.closedBall 0 1) 1
    (sanity_familyCk_const _ _ contDiff_const) (isCompact_closedBall _ _) one_pos
  refine ⟨C, fun A M p m hA hp hm => hC A M () p m hA (fun k _ => ?_) hm⟩
  simp [GradLower]; nlinarith

theorem cusp_fd (y v : ℝ × ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => k.1 ^ 4 + k.2 ^ 2) y v = 4 * y.1 ^ 3 * v.1 + 2 * y.2 * v.2 := by
  have h : HasFDerivAt (fun k : ℝ × ℝ => k.1 ^ 4 + k.2 ^ 2)
      ((4 * y.1 ^ 3) • ContinuousLinearMap.fst ℝ ℝ ℝ + (2 * y.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    convert ((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 4).add ((hasFDerivAt_snd (𝕜 := ℝ) (p := y)).pow 2) using 1
    ext <;> simp
  rw [h.fderiv]; simp

theorem cusp_fd_cub_lin (y w : ℝ × ℝ) (a b : ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => a * k.1 ^ 3 + b * k.2) y w = 3 * a * y.1 ^ 2 * w.1 + b * w.2 := by
  have h : HasFDerivAt (fun k : ℝ × ℝ => a * k.1 ^ 3 + b * k.2)
      ((3 * a * y.1 ^ 2) • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    convert (((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 3).const_mul a).add
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := y)).const_mul b) using 1
    ext <;> simp; ring
  rw [h.fderiv]; simp

theorem cusp_dd (y v w : ℝ × ℝ) :
    dd (fun k : ℝ × ℝ => k.1 ^ 4 + k.2 ^ 2) y v w = 12 * y.1 ^ 2 * v.1 * w.1 + 2 * v.2 * w.2 := by
  have : (fun y : ℝ × ℝ => fderiv ℝ (fun k : ℝ × ℝ => k.1 ^ 4 + k.2 ^ 2) y v) =
      fun y => (4 * v.1) * y.1 ^ 3 + (2 * v.2) * y.2 := by funext y; rw [cusp_fd]; ring
  rw [dd, this, cusp_fd_cub_lin]; ring

theorem cusp_fd_sq_lin (y w : ℝ × ℝ) (a b : ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => a * k.1 ^ 2 + b) y w = 2 * a * y.1 * w.1 := by
  have h : HasFDerivAt (fun k : ℝ × ℝ => a * k.1 ^ 2 + b)
      ((2 * a * y.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) y := by
    convert ((((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 2).const_mul a).add_const b) using 1
    ext <;> simp; ring
  rw [h.fderiv]; simp

theorem cusp_ddd (y u v w : ℝ × ℝ) :
    ddd (fun k : ℝ × ℝ => k.1 ^ 4 + k.2 ^ 2) y u v w = 24 * y.1 * u.1 * v.1 * w.1 := by
  have : (fun y : ℝ × ℝ => dd (fun k : ℝ × ℝ => k.1 ^ 4 + k.2 ^ 2) y u v) =
      fun y => (12 * u.1 * v.1) * y.1 ^ 2 + 2 * u.2 * v.2 := by funext y; rw [cusp_dd]; ring
  rw [ddd, this, cusp_fd_sq_lin]; ring

/-- Exclusion: the cusp `k₁⁴ + k₂²` (decay `m^{-3/4}`) fails `FoldOrNondeg` at `0`, so S3 does not claim
`m^{-5/6}` for it. -/
theorem cusp_excluded : ¬ FoldOrNondeg (fun k : ℝ × ℝ => k.1 ^ 4 + k.2 ^ 2) 0 := by
  rintro (h | ⟨-, h⟩)
  · apply h; simp [hessDet, cusp_dd]
  · apply h (1, 0) (by simp) (fun w => by rw [cusp_dd]; simp)
    rw [cusp_ddd]; simp

/-- Satisfiability with a genuinely varying family over the non-discrete compact space `[0, 1]`. -/
theorem familyCk_affine_param (n : ℕ) (f g : ℝ × ℝ → ℝ) (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    FamilyCk n (fun σ : Set.Icc (0:ℝ) 1 => fun k => (σ : ℝ) * f k + g k) := by
  refine ⟨fun σ => contDiff_const.mul hf |>.add hg, fun j hj => ?_⟩
  have hj' : (j : WithTop ℕ∞) ≤ n := by exact_mod_cast hj
  have : (fun q : Set.Icc (0:ℝ) 1 × (ℝ × ℝ) => iteratedFDeriv ℝ j (fun k => (q.1 : ℝ) * f k + g k) q.2) =
      fun q => (q.1 : ℝ) • iteratedFDeriv ℝ j f q.2 + iteratedFDeriv ℝ j g q.2 := by
    funext q
    have h1 : ContDiff ℝ j (fun k => (q.1 : ℝ) * f k) := (contDiff_const.mul hf).of_le hj'
    have e : (fun k => (q.1 : ℝ) * f k + g k) = (q.1 : ℝ) • f + g := by funext k; simp [smul_eq_mul]
    have hs : ContDiff ℝ j ((q.1 : ℝ) • f) := by simpa only [Pi.smul_def] using (hf.of_le hj').const_smul (q.1 : ℝ)
    rw [e, iteratedFDeriv_add_apply hs.contDiffAt ((hg.of_le hj').contDiffAt),
      iteratedFDeriv_const_smul_apply ((hf.of_le hj').contDiffAt)]
  rw [this]
  exact ((continuous_subtype_val.comp continuous_fst).smul
    ((hf.continuous_iteratedFDeriv hj').comp continuous_snd)).add
    ((hg.continuous_iteratedFDeriv hj').comp continuous_snd)

end OscInt.StationaryPhase.Sanity
