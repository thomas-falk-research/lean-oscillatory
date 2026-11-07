import Blueprint.D4ClosedForm

/-!
# S4.4, part E4: the coefficients and the discriminant of `C ∘ g`

* `cubicForm_cubicComp`: `cubicComp q g` are the coefficients of `z ↦ C(lin2 g z)` (in the order of `cubicForm`).
* `disc_cubicComp`: `disc (C ∘ g) = (det g)⁶ disc C` (the discriminant is a `GL₂` covariant of weight 6).
* `abs_disc_rpow_mul`: `|disc C|^{1/6} |det g| = |disc (C ∘ g)|^{1/6}`.

All three by `ring` and `Real.rpow` algebra (route `docs/proof-S44.md`, E4).
-/

namespace OscInt.D4

open OscInt.Statements OscInt.Blueprint

/-- **E4a** `cubicComp q g` are the coefficients of `C ∘ lin2 g`. -/
theorem cubicForm_cubicComp (q g : ℝ × ℝ × ℝ × ℝ) (z : ℝ × ℝ) :
    cubicForm (cubicComp q g) z = cubicForm q (lin2 g z) := by
  obtain ⟨a, b, c, d⟩ := q
  obtain ⟨g₁, g₂, g₃, g₄⟩ := g
  obtain ⟨x, y⟩ := z
  simp only [cubicComp, cubicForm, lin2]
  ring

/-- **E4b** `disc (C ∘ g) = (det g)⁶ · disc C`. -/
theorem disc_cubicComp (q g : ℝ × ℝ × ℝ × ℝ) : disc (cubicComp q g) = det2 g ^ 6 * disc q := by
  obtain ⟨a, b, c, d⟩ := q
  obtain ⟨g₁, g₂, g₃, g₄⟩ := g
  simp only [cubicComp, cubicForm, lin2, disc, det2]
  ring

/-- `|disc C|^{1/6} · |det g| = |disc (C ∘ g)|^{1/6}`. -/
theorem abs_disc_rpow_mul (q g : ℝ × ℝ × ℝ × ℝ) :
    |disc q| ^ ((1 : ℝ) / 6) * |det2 g| = |disc (cubicComp q g)| ^ ((1 : ℝ) / 6) := by
  rw [disc_cubicComp, abs_mul, abs_pow, Real.mul_rpow (by positivity) (abs_nonneg _), mul_comm]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  norm_num

end OscInt.D4
