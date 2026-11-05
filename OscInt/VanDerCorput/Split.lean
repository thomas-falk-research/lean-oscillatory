import Blueprint.VanDerCorput
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# P0: the splitting point (`OscInt.Blueprint.SplitFacts`)

If `g` has derivative `g'` on `[a, b]` (continuous on `[a, b]`, `HasDerivAt` on `(a, b)`) and `μ ≤ |g'|` on
`(a, b)` with `μ > 0`, then `g` is monotone or antitone on `[a, b]`, and there is `d ∈ [a, b]` with
`μ |x - d| ≤ |g x|` on `[a, b]`.

Proof: Darboux's theorem gives `g' ≥ μ` or `g' ≤ -μ` on `(a, b)`. In the first case the mean value inequality
gives `μ (y - x) ≤ g y - g x` for `x ≤ y`; then `d` is `a`, `b`, or a zero of `g` (intermediate value theorem).
The second case follows by applying the first to `-g`.

Route adapted from `exists_le_abs_of_le_derivWithin` in J. Roos and M. Praveen, `roos-j/lean-oscillatory`,
`LeanOscillatory/VanDerCorput.lean` (Apache-2.0).
-/

namespace OscInt.VanDerCorput

open Set OscInt.Statements

namespace SplitAux

/-- Mean value inequality: `μ ≤ g'` on `(a, b)` gives `μ (y - x) ≤ g y - g x` for `x ≤ y` in `[a, b]`. -/
theorem mul_sub_le_of_le_deriv {g g' : ℝ → ℝ} {a b μ : ℝ} (hg : HasDerivOn g g' a b)
    (hμ : ∀ x ∈ Ioo a b, μ ≤ g' x) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → μ * (y - x) ≤ g y - g x := by
  refine Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc a b) hg.1 ?_ ?_
  · rw [interior_Icc]
    exact fun x hx => (hg.2 x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx
    rw [(hg.2 x hx).deriv]
    exact hμ x hx

/-- If `g` is continuous on `[a, b]` and `μ (y - x) ≤ g y - g x` for `x ≤ y` in `[a, b]`, with `0 ≤ μ`,
then some `d ∈ [a, b]` has `μ |x - d| ≤ |g x|` for all `x ∈ [a, b]`. -/
theorem exists_split_of_mul_sub_le {g : ℝ → ℝ} {a b μ : ℝ} (hab : a ≤ b) (hμ : 0 ≤ μ)
    (hc : ContinuousOn g (Icc a b))
    (hg : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → μ * (y - x) ≤ g y - g x) :
    ∃ d ∈ Icc a b, ∀ x ∈ Icc a b, μ * |x - d| ≤ |g x| := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  -- the key estimate around a point `d` where `g` changes sign
  have key : ∀ d : ℝ, (∀ x ∈ Icc a b, d < x → μ * (x - d) ≤ g x) →
      (∀ x ∈ Icc a b, x < d → g x ≤ -(μ * (d - x))) → ∀ x ∈ Icc a b, μ * |x - d| ≤ |g x| := by
    intro d h1 h2 x hx
    rcases lt_trichotomy x d with hxd | rfl | hdx
    · have := h2 x hx hxd
      have : 0 ≤ μ * (d - x) := mul_nonneg hμ (by linarith)
      rw [abs_of_neg (by linarith : x - d < 0), abs_of_nonpos (by linarith : g x ≤ 0)]
      linarith
    · simp
    · have := h1 x hx hdx
      have : 0 ≤ μ * (x - d) := mul_nonneg hμ (by linarith)
      rw [abs_of_pos (by linarith : 0 < x - d), abs_of_nonneg (by linarith : 0 ≤ g x)]
      linarith
  by_cases hga : 0 ≤ g a
  · refine ⟨a, ha, key a (fun x hx hax => ?_) (fun x hx hxa => absurd hx.1 (not_le.2 hxa))⟩
    linarith [hg a ha x hx hax.le]
  by_cases hgb : g b ≤ 0
  · refine ⟨b, hb, key b (fun x hx hbx => absurd hx.2 (not_le.2 hbx)) (fun x hx hxb => ?_)⟩
    linarith [hg x hx b hb hxb.le]
  obtain ⟨d, hd, hgd⟩ := intermediate_value_Icc hab hc ⟨(not_le.1 hga).le, (not_le.1 hgb).le⟩
  refine ⟨d, hd, key d (fun x hx hdx => ?_) (fun x hx hxd => ?_)⟩
  · linarith [hg d hd x hx hdx.le]
  · linarith [hg x hx d hd hxd.le]

/-- `SplitFacts` when `μ ≤ g'` on `(a, b)`: `g` is monotone on `[a, b]` and a splitting point exists. -/
theorem split_of_le_deriv {g g' : ℝ → ℝ} {a b μ : ℝ} (hab : a ≤ b) (hμ : 0 < μ) (hg : HasDerivOn g g' a b)
    (hle : ∀ x ∈ Ioo a b, μ ≤ g' x) :
    MonotoneOn g (Icc a b) ∧ ∃ d ∈ Icc a b, ∀ x ∈ Icc a b, μ * |x - d| ≤ |g x| := by
  have h := mul_sub_le_of_le_deriv hg hle
  refine ⟨fun x hx y hy hxy => ?_, exists_split_of_mul_sub_le hab hμ.le hg.1 h⟩
  have := h x hx y hy hxy
  nlinarith

end SplitAux

open SplitAux in
/-- **P0** (splitting point): `OscInt.Blueprint.SplitFacts`. -/
theorem splitFacts : OscInt.Blueprint.SplitFacts := by
  intro g g' a b μ hab hμ hg hle
  have hne : ∀ x ∈ Ioo a b, g' x ≠ 0 := fun x hx h0 => by
    have := hle x hx; rw [h0, abs_zero] at this; linarith
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne (convex_Ioo a b)
      (fun x hx => (hg.2 x hx).hasDerivWithinAt) hne with hneg | hpos
  · -- `g' ≤ -μ`: apply the monotone case to `-g`
    have hg' : HasDerivOn (fun x => -g x) (fun x => -g' x) a b :=
      ⟨hg.1.neg, fun x hx => (hg.2 x hx).neg⟩
    have hle' : ∀ x ∈ Ioo a b, μ ≤ -g' x := fun x hx => by
      have := hle x hx; rw [abs_of_neg (hneg x hx)] at this; exact this
    obtain ⟨hmono, d, hd, hdx⟩ := split_of_le_deriv hab hμ hg' hle'
    refine ⟨Or.inr fun x hx y hy hxy => neg_le_neg_iff.1 (hmono hx hy hxy), d, hd, fun x hx => ?_⟩
    simpa only [abs_neg] using hdx x hx
  · have hle' : ∀ x ∈ Ioo a b, μ ≤ g' x := fun x hx => by
      have := hle x hx; rwa [abs_of_pos (hpos x hx)] at this
    obtain ⟨hmono, hd⟩ := split_of_le_deriv hab hμ hg hle'
    exact ⟨Or.inl hmono, hd⟩

end OscInt.VanDerCorput
