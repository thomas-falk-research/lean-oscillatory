import Blueprint.D4
import OscInt.StationaryPhase.Implicit

/-!
# S4.1 parts D5 and D6: openness of the gauge condition, large linear terms

* `OscInt.D4.gaugeOpen : GaugeOpenFacts` (D5). Through `dd_eq_iteratedFDeriv`/`ddd_eq_iteratedFDeriv` the gauge
  `foldGauge` and `hessNorm` are polynomials in `D²Ψ_σ(k)`, `D³Ψ_σ(k)` (the kernel vectors enter by joint continuity
  of evaluation), hence jointly continuous in `(σ, k)` for a `C³` family; the set where both are positive is open and
  contains `{σ₀} × K`, so the tube lemma `IsCompact.eventually_forall_of_forall_eventually` concludes.
* `OscInt.D4.gradBound : GradBoundFacts` (D6). The partial derivatives are bounded by `C` on the compact `Λ × K`;
  with the max norm the coordinate `i` with `|p_i| = ‖p‖ ≥ C + 1` gives `(∂_iΨ + p_i)² ≥ 1`.

Route: `docs/proof-S4.md`, Steps 3 and 4.
-/

namespace OscInt.D4.OpenAux

open OscInt.Statements OscInt.Blueprint OscInt.StationaryPhase.ImplicitAux

variable {T : Type} [TopologicalSpace T] {Q : T → ℝ × ℝ → ℝ}

/-- Third directional derivatives along a jointly continuous vector field are jointly continuous. -/
theorem continuous_ddd_diag (hQ : FamilyCk 3 Q) {u : T × (ℝ × ℝ) → ℝ × ℝ} (hu : Continuous u) :
    Continuous fun q : T × (ℝ × ℝ) => ddd (Q q.1) q.2 (u q) (u q) (u q) := by
  simp_rw [ddd_eq_iteratedFDeriv (hQ.1 _) le_rfl]
  refine continuous_eval.comp ((hQ.2 3 le_rfl).prodMk (continuous_pi fun i => ?_))
  fin_cases i <;> exact hu

theorem continuous_hessNorm (hQ : FamilyCk 3 Q) :
    Continuous fun q : T × (ℝ × ℝ) => hessNorm (Q q.1) q.2 := by
  unfold hessNorm
  have h := continuous_dd hQ (by norm_num)
  exact (((h _ _).pow 2).add ((h _ _).pow 2)).add ((h _ _).pow 2)

theorem continuous_foldGauge (hQ : FamilyCk 3 Q) :
    Continuous fun q : T × (ℝ × ℝ) => foldGauge (Q q.1) q.2 := by
  unfold foldGauge hessDet
  have h := continuous_dd hQ (by norm_num)
  have h₁ : Continuous fun q : T × (ℝ × ℝ) => kerVec₁ (Q q.1) q.2 := (h _ _).neg.prodMk (h _ _)
  have h₂ : Continuous fun q : T × (ℝ × ℝ) => kerVec₂ (Q q.1) q.2 := (h _ _).prodMk (h _ _).neg
  exact ((((h _ _).mul (h _ _)).sub ((h _ _).pow 2)).pow 2).add
    ((continuous_ddd_diag hQ h₁).pow 2) |>.add ((continuous_ddd_diag hQ h₂).pow 2)

theorem abs_fderiv_le {Λ : Type} [TopologicalSpace Λ] [CompactSpace Λ] {Ψ : Λ → ℝ × ℝ → ℝ}
    {K : Set (ℝ × ℝ)} (hΨ : FamilyCk 1 Ψ) (hK : IsCompact K) (v : ℝ × ℝ) :
    ∃ C : ℝ, ∀ σ, ∀ k ∈ K, |fderiv ℝ (Ψ σ) k v| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ.prod hK).exists_bound_of_continuousOn
    (continuous_fderiv_apply hΨ le_rfl v).continuousOn
  exact ⟨C, fun σ k hk => hC (σ, k) ⟨Set.mem_univ _, hk⟩⟩

theorem one_le_sq_add {a p B : ℝ} (ha : |a| ≤ B) (hp : B + 1 ≤ |p|) : 1 ≤ (a + p) ^ 2 := by
  have h : 1 ≤ |a + p| := by
    have := abs_sub_abs_le_abs_sub p (-a)
    rw [sub_neg_eq_add, abs_neg, add_comm] at this
    linarith
  have := mul_le_mul h h zero_le_one (by linarith)
  rw [one_mul, ← abs_mul_abs_self, ← pow_two] at this
  simpa [sq_abs] using this

end OscInt.D4.OpenAux

namespace OscInt.D4

open OscInt.Statements OscInt.Blueprint OscInt.D4.OpenAux

/-- **D5**: the gauge condition on a compact set is open in the parameter. -/
theorem gaugeOpen : GaugeOpenFacts := by
  intro Λ _ Ψ σ₀ K hΨ hK h
  refine hK.eventually_forall_of_forall_eventually fun k hk => ?_
  have hU : IsOpen {q : Λ × (ℝ × ℝ) | 0 < foldGauge (Ψ q.1) q.2 ∧ 0 < hessNorm (Ψ q.1) q.2} :=
    (isOpen_lt continuous_const (continuous_foldGauge hΨ)).inter
      (isOpen_lt continuous_const (continuous_hessNorm hΨ))
  exact hU.mem_nhds (h k hk)

/-- **D6**: large linear terms make the phase non-stationary on a compact set. -/
theorem gradBound : GradBoundFacts := by
  intro Λ _ _ Ψ K hΨ hK
  obtain ⟨C₁, hC₁⟩ := abs_fderiv_le hΨ hK (1, 0)
  obtain ⟨C₂, hC₂⟩ := abs_fderiv_le hΨ hK (0, 1)
  refine ⟨max C₁ C₂ + 1, fun σ k hk p hp => ?_⟩
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at hp
  unfold GradLower
  rw [one_pow]
  rcases le_total |p.2| |p.1| with h | h
  · have := one_le_sq_add (p := p.1) (le_trans (hC₁ σ k hk) (le_max_left C₁ C₂))
      (by rw [max_eq_left h] at hp; linarith)
    nlinarith [sq_nonneg (fderiv ℝ (Ψ σ) k (0, 1) + p.2)]
  · have := one_le_sq_add (p := p.2) (le_trans (hC₂ σ k hk) (le_max_right C₁ C₂))
      (by rw [max_eq_right h] at hp; linarith)
    nlinarith [sq_nonneg (fderiv ℝ (Ψ σ) k (1, 0) + p.1)]

end OscInt.D4
