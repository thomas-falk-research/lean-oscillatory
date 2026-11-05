import Mathlib

/-!
# S2, S3: two-dimensional oscillatory integrals (statements only)

Mathematics: `docs/statements.md`, S2 and S3.

Symbols.
* Points of ℝ² are `k : ℝ × ℝ` (product Lebesgue measure; the norm on `ℝ × ℝ` is the max norm).
* `lin p k = p.1 * k.1 + p.2 * k.2` is `p·k`.
* `oscInt2 Q A = ∫ k, exp (Q k * I) * A k` is `I(Q, A)` (Bochner integral over `ℝ × ℝ`).
* `dd Ψ k v w = fderiv ℝ (fun y => fderiv ℝ Ψ y v) k w` is `∂_w ∂_v Ψ(k)`;
  `ddd Ψ k u v w = fderiv ℝ (fun y => dd Ψ y u v) k w` is `∂_w ∂_v ∂_u Ψ(k)`.
* `hessDet Ψ k = dd Ψ k e₁ e₁ * dd Ψ k e₂ e₂ - dd Ψ k e₁ e₂ ^ 2` with `e₁ = (1, 0)`, `e₂ = (0, 1)`.
* `IsCritical Ψ p k`: `∂₁Ψ(k) + p₁ = 0 ∧ ∂₂Ψ(k) + p₂ = 0`.
* `GradLower Ψ p k c`: `c² ≤ (∂₁Ψ(k) + p₁)² + (∂₂Ψ(k) + p₂)²`, i.e. `|∇(Ψ + p·)(k)| ≥ c` for `c ≥ 0`.
* `FoldOrNondeg Ψ k`: `hessDet Ψ k ≠ 0`, or the Hessian bilinear form `dd Ψ k` is nonzero and every nonzero
  `v` with `dd Ψ k v w = 0` for all `w` has `ddd Ψ k v v v ≠ 0`.
* `AmpBound n K A M`: `A` is `Cⁿ`, `tsupport A ⊆ K`, and `‖iteratedFDeriv ℝ j A k‖ ≤ M` for all `k`, `j ≤ n`.
* `FamilyCk n Ψ`: every `Ψ σ` is `Cⁿ` and `(σ, k) ↦ iteratedFDeriv ℝ j (Ψ σ) k` is continuous for `j ≤ n`.

Modelling choices.
* The C^n "norm" of the amplitude enters only through an arbitrary bound `M` on all derivatives of order ≤ n,
  so no `iSup` (whose Lean value is `0` on unbounded sets) is involved.
* `oscInt2` is a Bochner integral; the integrand is continuous with compact support under `AmpBound`, hence
  integrable, so Lean's value `0` for non-integrable integrands is never reached.
* `m ^ (-(5 : ℝ) / 6)` is `Real.rpow` with `m ≥ 1`; `m ^ N` is a natural power; `/ m` with `m ≥ 1`.
* Constants: `∃ C` comes after the family, `K`, `K'`, `c`, `N` and before `A`, `M`, `σ`, `p`, `m`.
* Second and third derivatives are nested `fderiv`s (directional derivatives), equal to
  `iteratedFDeriv` for `C²`/`C³` functions; the hypotheses only use them for `C⁴` phases.
-/

namespace OscInt.Statements

open Set MeasureTheory Complex

/-- `p · k`. -/
def lin (p k : ℝ × ℝ) : ℝ := p.1 * k.1 + p.2 * k.2

/-- `∫_{ℝ²} e^{i Q(k)} A(k) dk`. -/
noncomputable def oscInt2 (Q : ℝ × ℝ → ℝ) (A : ℝ × ℝ → ℂ) : ℂ :=
  ∫ k, Complex.exp (↑(Q k) * Complex.I) * A k

/-- `∂_w ∂_v Ψ(k)`. -/
noncomputable def dd (Ψ : ℝ × ℝ → ℝ) (k v w : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ Ψ y v) k w

/-- `∂_w ∂_v ∂_u Ψ(k)`. -/
noncomputable def ddd (Ψ : ℝ × ℝ → ℝ) (k u v w : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun y => dd Ψ y u v) k w

/-- The Hessian determinant `∂₁₁Ψ ∂₂₂Ψ - (∂₁₂Ψ)²` at `k`. -/
noncomputable def hessDet (Ψ : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : ℝ :=
  dd Ψ k (1, 0) (1, 0) * dd Ψ k (0, 1) (0, 1) - dd Ψ k (1, 0) (0, 1) ^ 2

/-- `k` is a critical point of `Ψ + p·(·)`. -/
def IsCritical (Ψ : ℝ × ℝ → ℝ) (p k : ℝ × ℝ) : Prop :=
  fderiv ℝ Ψ k (1, 0) + p.1 = 0 ∧ fderiv ℝ Ψ k (0, 1) + p.2 = 0

/-- `|∇(Ψ + p·)(k)| ≥ c` (stated with squares). -/
def GradLower (Ψ : ℝ × ℝ → ℝ) (p k : ℝ × ℝ) (c : ℝ) : Prop :=
  c ^ 2 ≤ (fderiv ℝ Ψ k (1, 0) + p.1) ^ 2 + (fderiv ℝ Ψ k (0, 1) + p.2) ^ 2

/-- At `k` the Hessian is nondegenerate, or it has rank one and the third derivative along its kernel is
nonzero. -/
def FoldOrNondeg (Ψ : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : Prop :=
  hessDet Ψ k ≠ 0 ∨
    ((∃ v w, dd Ψ k v w ≠ 0) ∧ ∀ v : ℝ × ℝ, v ≠ 0 → (∀ w, dd Ψ k v w = 0) → ddd Ψ k v v v ≠ 0)

/-- Amplitude bound `(n, K, M)`: `A ∈ Cⁿ`, support closure in `K`, derivatives of order `≤ n` bounded by `M`. -/
def AmpBound (n : ℕ) (K : Set (ℝ × ℝ)) (A : ℝ × ℝ → ℂ) (M : ℝ) : Prop :=
  ContDiff ℝ n A ∧ tsupport A ⊆ K ∧ ∀ j ≤ n, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M

/-- A family of phases of class `Cⁿ`, with derivatives of order `≤ n` jointly continuous in `(σ, k)`. -/
def FamilyCk (n : ℕ) {Λ : Type} [TopologicalSpace Λ] (Ψ : Λ → ℝ × ℝ → ℝ) : Prop :=
  (∀ σ, ContDiff ℝ n (Ψ σ)) ∧
    ∀ j ≤ n, Continuous (fun q : Λ × (ℝ × ℝ) => iteratedFDeriv ℝ j (Ψ q.1) q.2)

/-- **S2.1** Non-stationary phase: decay `m^{-N}`, uniform over a compact family and over every linear term with
`|∇(Ψ_σ + p·)| ≥ c` on `K`. -/
def NonStationaryStatement : Prop :=
  ∀ (Λ : Type) [TopologicalSpace Λ] [CompactSpace Λ] (N : ℕ) (Ψ : Λ → ℝ × ℝ → ℝ) (K : Set (ℝ × ℝ)) (c : ℝ),
    FamilyCk (N + 1) Ψ → IsCompact K → 0 < c →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (σ : Λ) (p : ℝ × ℝ) (m : ℝ),
      AmpBound N K A M → (∀ k ∈ K, GradLower (Ψ σ) p k c) → 1 ≤ m →
      ‖oscInt2 (fun k => m * (Ψ σ k + lin p k)) A‖ ≤ C * M / m ^ N

theorem statement_pin_NonStationary : NonStationaryStatement = NonStationaryStatement := rfl

/-- **S2.2** Nondegenerate stationary phase: decay `m^{-1}`, uniform over `p ∈ K'`. -/
def StationaryPhaseStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (K K' : Set (ℝ × ℝ)),
    ContDiff ℝ 4 Ψ → IsCompact K → IsCompact K' →
    (∀ p ∈ K', ∀ k ∈ K, IsCritical Ψ p k → hessDet Ψ k ≠ 0) →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (p : ℝ × ℝ) (m : ℝ),
      AmpBound 2 K A M → p ∈ K' → 1 ≤ m →
      ‖oscInt2 (fun k => m * (Ψ k + lin p k)) A‖ ≤ C * M / m

theorem statement_pin_StationaryPhase : StationaryPhaseStatement = StationaryPhaseStatement := rfl

/-- **S3** Uniform fold estimate: decay `m^{-5/6}`, uniform over a compact family and over `p ∈ K'`. -/
def FoldStatement : Prop :=
  ∀ (Λ : Type) [TopologicalSpace Λ] [CompactSpace Λ] (Ψ : Λ → ℝ × ℝ → ℝ) (K K' : Set (ℝ × ℝ)),
    FamilyCk 4 Ψ → IsCompact K → IsCompact K' →
    (∀ σ, ∀ k ∈ K, FoldOrNondeg (Ψ σ) k) →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (σ : Λ) (p : ℝ × ℝ) (m : ℝ),
      AmpBound 2 K A M → p ∈ K' → 1 ≤ m →
      ‖oscInt2 (fun k => m * (Ψ σ k + lin p k)) A‖ ≤ C * M * m ^ (-(5 : ℝ) / 6)

theorem statement_pin_Fold : FoldStatement = FoldStatement := rfl

/-! ## Sanity: every hypothesis set is satisfiable by non-degenerate data, stated through the same definitions
as the statements; a nonzero amplitude satisfies `AmpBound`. -/


theorem sanity_fd_sq_sub (y v : ℝ × ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => k.1 ^ 2 - k.2 ^ 2) y v = 2 * y.1 * v.1 - 2 * y.2 * v.2 := by
  have h : HasFDerivAt (fun k : ℝ × ℝ => k.1 ^ 2 - k.2 ^ 2)
      ((2 * y.1) • ContinuousLinearMap.fst ℝ ℝ ℝ - (2 * y.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    convert ((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 2).sub ((hasFDerivAt_snd (𝕜 := ℝ) (p := y)).pow 2) using 1
    ext <;> simp
  rw [h.fderiv]; simp

theorem sanity_fd_lin (y v : ℝ × ℝ) (a b : ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => a * k.1 + b * k.2) y v = a * v.1 + b * v.2 := by
  have h : HasFDerivAt (fun k : ℝ × ℝ => a * k.1 + b * k.2)
      (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    convert ((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).const_mul a).add
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := y)).const_mul b) using 1
  rw [h.fderiv]; simp

theorem sanity_saddle_hessDet (k : ℝ × ℝ) : hessDet (fun k : ℝ × ℝ => k.1 ^ 2 - k.2 ^ 2) k = -4 := by
  have : ∀ v : ℝ × ℝ, (fun y : ℝ × ℝ => fderiv ℝ (fun k : ℝ × ℝ => k.1 ^ 2 - k.2 ^ 2) y v) =
      fun y => (2 * v.1) * y.1 + (-2 * v.2) * y.2 := fun v => by funext y; rw [sanity_fd_sq_sub]; ring
  simp only [hessDet, dd, this, sanity_fd_lin]; norm_num


theorem sanity_fd_cube_sq (y v : ℝ × ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 2) y v = 3 * y.1 ^ 2 * v.1 + 2 * y.2 * v.2 := by
  have h : HasFDerivAt (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 2)
      ((3 * y.1 ^ 2) • ContinuousLinearMap.fst ℝ ℝ ℝ + (2 * y.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    convert ((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 3).add ((hasFDerivAt_snd (𝕜 := ℝ) (p := y)).pow 2) using 1
    ext <;> simp
  rw [h.fderiv]; simp

theorem sanity_fd_sq_lin (y w : ℝ × ℝ) (a b : ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => a * k.1 ^ 2 + b * k.2) y w = 2 * a * y.1 * w.1 + b * w.2 := by
  have h : HasFDerivAt (fun k : ℝ × ℝ => a * k.1 ^ 2 + b * k.2)
      ((2 * a * y.1) • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    convert (((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 2).const_mul a).add
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := y)).const_mul b) using 1
    ext <;> simp; ring
  rw [h.fderiv]; simp

theorem sanity_fd_lin_const (y w : ℝ × ℝ) (a c : ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => a * k.1 + c) y w = a * w.1 := by
  have h : HasFDerivAt (fun k : ℝ × ℝ => a * k.1 + c) (a • ContinuousLinearMap.fst ℝ ℝ ℝ) y := by
    simpa using ((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).const_mul a).add_const c
  rw [h.fderiv]; simp

theorem sanity_dd_fold (y v w : ℝ × ℝ) :
    dd (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 2) y v w = 6 * y.1 * v.1 * w.1 + 2 * v.2 * w.2 := by
  have : (fun y : ℝ × ℝ => fderiv ℝ (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 2) y v) =
      fun y => (3 * v.1) * y.1 ^ 2 + (2 * v.2) * y.2 := by funext y; rw [sanity_fd_cube_sq]; ring
  rw [dd, this, sanity_fd_sq_lin]; ring

theorem sanity_ddd_fold (y u v w : ℝ × ℝ) :
    ddd (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 2) y u v w = 6 * u.1 * v.1 * w.1 := by
  have : (fun y : ℝ × ℝ => dd (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 2) y u v) =
      fun y => (6 * u.1 * v.1) * y.1 + 2 * u.2 * v.2 := by funext y; rw [sanity_dd_fold]; ring
  rw [ddd, this, sanity_fd_lin_const]

theorem sanity_fold_everywhere (k : ℝ × ℝ) : FoldOrNondeg (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 2) k := by
  by_cases hk : k.1 = 0
  · right
    refine ⟨⟨(0, 1), (0, 1), by rw [sanity_dd_fold]; norm_num⟩, fun v hv hker => ?_⟩
    have h2 : v.2 = 0 := by have := hker (0, 1); rw [sanity_dd_fold] at this; simpa [hk] using this
    have h1 : v.1 ≠ 0 := fun h1 => hv (Prod.ext h1 h2)
    rw [sanity_ddd_fold]; simpa using h1
  · left
    simp only [hessDet, sanity_dd_fold]; norm_num; exact hk


theorem sanity_familyCk_const (n : ℕ) (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ n f) :
    FamilyCk n (fun _ : Unit => f) :=
  ⟨fun _ => hf, fun j hj => (hf.continuous_iteratedFDeriv (by exact_mod_cast hj)).comp continuous_snd⟩

/-- A nonzero amplitude satisfying `AmpBound n (closedBall 0 1) A M` for some `M`, for every `n`. -/
theorem sanity_ampBound_exists (n : ℕ) :
    ∃ (A : ℝ × ℝ → ℂ) (M : ℝ), AmpBound n (Metric.closedBall 0 1) A M ∧ A 0 = 1 := by
  let b : ContDiffBump (0 : ℝ × ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let A : ℝ × ℝ → ℂ := fun k => (b k : ℂ)
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hs : Function.support A = Function.support b := by ext k; simp [A]
  have hsupp : tsupport A ⊆ Metric.closedBall 0 1 := by
    rw [tsupport, hs, ← tsupport, b.tsupport_eq]
  have hcs : HasCompactSupport A :=
    HasCompactSupport.intro (isCompact_closedBall 0 1) fun k hk => image_eq_zero_of_notMem_tsupport
      (fun h => hk (hsupp h))
  choose B hB using fun j : ℕ =>
    ((hA.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).norm.bddAbove_range_of_hasCompactSupport
      (hcs.iteratedFDeriv j).norm)
  refine ⟨A, ∑ j ∈ Finset.range (n + 1), max (B j) 0,
    ⟨hA.of_le (by exact_mod_cast le_top), hsupp, fun j hj k => ?_⟩, ?_⟩
  · calc ‖iteratedFDeriv ℝ j A k‖ ≤ max (B j) 0 := (hB j ⟨k, rfl⟩).trans (le_max_left _ _)
      _ ≤ ∑ i ∈ Finset.range (n + 1), max (B i) 0 :=
        Finset.single_le_sum (f := fun i => max (B i) 0) (fun i _ => le_max_right _ _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  · simp only [A]
    rw [b.one_of_mem_closedBall (by simp [b])]
    simp

/-- S2.1 hypotheses: `Ψ(k) = k₁` (a one-point family), `K = closedBall 0 1`, `c = 1`, `p = 0`. -/
theorem sanity_NonStationary_hyps (N : ℕ) :
    FamilyCk (N + 1) (fun _ : Unit => fun k : ℝ × ℝ => 1 * k.1 + 0 * k.2) ∧
      IsCompact (Metric.closedBall (0 : ℝ × ℝ) 1) ∧
      ∀ k, GradLower (fun k : ℝ × ℝ => 1 * k.1 + 0 * k.2) 0 k 1 := by
  refine ⟨sanity_familyCk_const _ _ (by fun_prop), isCompact_closedBall _ _, fun k => ?_⟩
  simp only [GradLower, sanity_fd_lin]; norm_num

/-- S2.2 hypotheses: the saddle `k₁² - k₂²` on `K = K' = closedBall 0 1`; a critical point exists. -/
theorem sanity_StationaryPhase_hyps :
    ContDiff ℝ 4 (fun k : ℝ × ℝ => k.1 ^ 2 - k.2 ^ 2) ∧
      IsCompact (Metric.closedBall (0 : ℝ × ℝ) 1) ∧
      (∀ p ∈ Metric.closedBall (0 : ℝ × ℝ) 1, ∀ k ∈ Metric.closedBall (0 : ℝ × ℝ) 1,
        IsCritical (fun k : ℝ × ℝ => k.1 ^ 2 - k.2 ^ 2) p k →
          hessDet (fun k : ℝ × ℝ => k.1 ^ 2 - k.2 ^ 2) k ≠ 0) ∧
      ∃ p ∈ Metric.closedBall (0 : ℝ × ℝ) 1, ∃ k ∈ Metric.closedBall (0 : ℝ × ℝ) 1,
        IsCritical (fun k : ℝ × ℝ => k.1 ^ 2 - k.2 ^ 2) p k := by
  refine ⟨by fun_prop, isCompact_closedBall _ _, fun p _ k _ _ => by rw [sanity_saddle_hessDet]; norm_num,
    0, Metric.mem_closedBall_self zero_le_one, 0, Metric.mem_closedBall_self zero_le_one, ?_⟩
  simp [IsCritical, sanity_fd_sq_sub]

/-- S3 hypotheses: the fold `k₁³ + k₂²` (a one-point family) on `K = closedBall 0 1`; the Hessian degenerates
at `0 ∈ K`, so the rank-one branch is used. -/
theorem sanity_Fold_hyps :
    FamilyCk 4 (fun _ : Unit => fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 2) ∧
      IsCompact (Metric.closedBall (0 : ℝ × ℝ) 1) ∧
      (∀ k ∈ Metric.closedBall (0 : ℝ × ℝ) 1, FoldOrNondeg (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 2) k) ∧
      hessDet (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 2) 0 = 0 := by
  refine ⟨sanity_familyCk_const _ _ (by fun_prop), isCompact_closedBall _ _,
    fun k _ => sanity_fold_everywhere k, ?_⟩
  simp [hessDet, sanity_dd_fold]

end OscInt.Statements
