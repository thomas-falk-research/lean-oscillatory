import OscInt.Statements.Convert

/-!
# Front-end batch 3: compact families, the classical fold hypothesis and local smoothness (statements only)

Mathematics: `docs/statements.md`, "Front end, batch 3". Written, stamped and blind-reviewed before any proof of these
statements exists (`CONTRIBUTING.md`, lessons 23 and 29).

* S2.2F `StationaryPhaseFamilyStatement`: S2.2 uniform over a compact family of phases (`FamilyCk 4`) and `p ∈ K'`.
* S3c `FoldCritStatement`: S3 with the fold-or-nondegenerate condition required only at critical points of
  `Ψ_σ + p·` (`k ∈ K`, `p ∈ K'`), as in the classical statement; uniform over a compact family.
* C10 `FamilyCkOfUncurryStatement`: a phase family that is `Cⁿ` jointly in the parameter and the point
  (`ContDiff ℝ n (Function.uncurry Ψ)`, parameter in a real normed space) is `FamilyCk n` on every parameter set.
* FE-S2.1L, FE-S2.2L, FE-S3L: S2.1, S2.2, S3c in Mathlib's idiom for a family `Ψ : E → ℝ × ℝ → ℝ` indexed by a
  compact set `S` of a real normed space, with smoothness only on an open set: `ContDiffOn` of the uncurried map on
  `V ×ˢ U`, `V ⊇ S` open, `U ⊇ K` open, `K` compact containing the amplitude's support.
* FE-S4.1′L: S4.1′ in Mathlib's idiom for a phase smooth only on an open neighbourhood `U` of `0`.
* FE-S2.1l, FE-S2.2l, FE-S3l: the single-phase forms of FE-S2.1L, FE-S2.2L, FE-S3L (`ContDiffOn ℝ n Ψ U`).

Modelling choices.
* Amplitude bounds and linear terms are as in front-end batch 2 (`ContDiff ℝ n A`, `tsupport A ⊆ K`,
  `‖iteratedFDeriv ℝ j A k‖ ≤ M` for `j ≤ n`; `L : (ℝ × ℝ) →L[ℝ] ℝ`; the max norm on `ℝ × ℝ`); the integral is
  written out.
* Derivatives of a phase that is smooth only on `U` are Mathlib's `fderiv`, `hessianMatrix` (via `iteratedFDeriv`)
  and `iteratedFDeriv` of the function on all of `ℝ²`, evaluated only at points of the open set `U` (or of `K ⊆ U`),
  where they depend only on the germ of the function; values of the phase outside `U` are arbitrary.
* For S3c and FE-S3L the fold condition is `FoldOrNondeg` (resp. `FoldOrNondegMatrix`) of the phase alone; adding a
  linear term changes neither the Hessian nor the third derivative.
* The parameter of a front-end family lives in a real normed space `E` (any, not necessarily finite-dimensional);
  `S` compact, so the family is compact as in S2.1 and S3.
-/

namespace OscInt.Statements

open Filter Topology

/-- **S2.2F** Nondegenerate stationary phase, uniform over a compact family: decay `m^{-1}`, uniform over `σ` and
`p ∈ K'`, when the Hessian of `Ψ_σ` is nondegenerate at every critical point of `Ψ_σ + p·` in `K`. -/
def StationaryPhaseFamilyStatement : Prop :=
  ∀ (Λ : Type) [TopologicalSpace Λ] [CompactSpace Λ] (Ψ : Λ → ℝ × ℝ → ℝ) (K K' : Set (ℝ × ℝ)),
    FamilyCk 4 Ψ → IsCompact K → IsCompact K' →
    (∀ σ, ∀ p ∈ K', ∀ k ∈ K, IsCritical (Ψ σ) p k → hessDet (Ψ σ) k ≠ 0) →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (σ : Λ) (p : ℝ × ℝ) (m : ℝ),
      AmpBound 2 K A M → p ∈ K' → 1 ≤ m →
      ‖oscInt2 (fun k => m * (Ψ σ k + lin p k)) A‖ ≤ C * M / m

theorem statement_pin_StationaryPhaseFamily :
    StationaryPhaseFamilyStatement = StationaryPhaseFamilyStatement := rfl

/-- **S3c** Uniform fold estimate with the classical hypothesis: decay `m^{-5/6}`, uniform over a compact family and
`p ∈ K'`, when `Ψ_σ` is fold-or-nondegenerate at every critical point of `Ψ_σ + p·` in `K`. -/
def FoldCritStatement : Prop :=
  ∀ (Λ : Type) [TopologicalSpace Λ] [CompactSpace Λ] (Ψ : Λ → ℝ × ℝ → ℝ) (K K' : Set (ℝ × ℝ)),
    FamilyCk 4 Ψ → IsCompact K → IsCompact K' →
    (∀ σ, ∀ p ∈ K', ∀ k ∈ K, IsCritical (Ψ σ) p k → FoldOrNondeg (Ψ σ) k) →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (σ : Λ) (p : ℝ × ℝ) (m : ℝ),
      AmpBound 2 K A M → p ∈ K' → 1 ≤ m →
      ‖oscInt2 (fun k => m * (Ψ σ k + lin p k)) A‖ ≤ C * M * m ^ (-(5 : ℝ) / 6)

theorem statement_pin_FoldCrit : FoldCritStatement = FoldCritStatement := rfl

/-- **C10** A family that is `Cⁿ` jointly in a real normed parameter and the point is `FamilyCk n` on every
parameter set `S` (subspace topology). -/
def FamilyCkOfUncurryStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (Ψ : E → ℝ × ℝ → ℝ),
    ContDiff ℝ n (Function.uncurry Ψ) → ∀ S : Set E, FamilyCk n (fun σ : S => Ψ σ)

theorem statement_pin_FamilyCkOfUncurry : FamilyCkOfUncurryStatement = FamilyCkOfUncurryStatement := rfl

/-- **FE-S2.1L** Non-stationary phase, Mathlib idiom, compact family, local smoothness: decay `m^{-N}`, uniform over
`σ ∈ S`, amplitudes with derivative bound `M` supported in `K`, and linear terms `L` with `‖DΨ_σ(k) + L‖ ≥ c` on
`K`, for a family `C^{N+1}` on `V ×ˢ U` (`S ⊆ V`, `K ⊆ U`, both open). -/
def NonStationaryLocalStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (N : ℕ) (Ψ : E → ℝ × ℝ → ℝ) (S V : Set E)
    (K U : Set (ℝ × ℝ)) (c : ℝ),
    IsCompact S → IsOpen V → S ⊆ V → IsCompact K → IsOpen U → K ⊆ U →
    ContDiffOn ℝ (N + 1) (Function.uncurry Ψ) (V ×ˢ U) → 0 < c →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (σ : E) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      σ ∈ S → ContDiff ℝ N A → tsupport A ⊆ K → (∀ j ≤ N, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      (∀ k ∈ K, c ≤ ‖fderiv ℝ (Ψ σ) k + L‖) → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ σ k + L k)) * Complex.I) * A k‖ ≤ C * M / m ^ N

theorem statement_pin_NonStationaryLocal : NonStationaryLocalStatement = NonStationaryLocalStatement := rfl

/-- **FE-S2.2L** Nondegenerate stationary phase, Mathlib idiom, compact family, local smoothness: decay `m^{-1}`,
uniform over `σ ∈ S` and `L ∈ K'`, when the Hessian matrix of `Ψ_σ` is invertible at every critical point of
`Ψ_σ + L` in `K`. -/
def StationaryPhaseLocalStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Ψ : E → ℝ × ℝ → ℝ) (S V : Set E)
    (K U : Set (ℝ × ℝ)) (K' : Set ((ℝ × ℝ) →L[ℝ] ℝ)),
    IsCompact S → IsOpen V → S ⊆ V → IsCompact K → IsOpen U → K ⊆ U → IsCompact K' →
    ContDiffOn ℝ 4 (Function.uncurry Ψ) (V ×ˢ U) →
    (∀ σ ∈ S, ∀ L ∈ K', ∀ k ∈ K, fderiv ℝ (Ψ σ) k + L = 0 → (hessianMatrix (Ψ σ) k).det ≠ 0) →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (σ : E) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      σ ∈ S → ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → L ∈ K' →
      1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ σ k + L k)) * Complex.I) * A k‖ ≤ C * M / m

theorem statement_pin_StationaryPhaseLocal : StationaryPhaseLocalStatement = StationaryPhaseLocalStatement := rfl

/-- **FE-S3L** Uniform fold estimate, Mathlib idiom, compact family, local smoothness, classical hypothesis: decay
`m^{-5/6}`, uniform over `σ ∈ S` and `L ∈ K'`, when `Ψ_σ` satisfies the matrix fold-or-nondegenerate condition at
every critical point of `Ψ_σ + L` in `K`. -/
def FoldLocalStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Ψ : E → ℝ × ℝ → ℝ) (S V : Set E)
    (K U : Set (ℝ × ℝ)) (K' : Set ((ℝ × ℝ) →L[ℝ] ℝ)),
    IsCompact S → IsOpen V → S ⊆ V → IsCompact K → IsOpen U → K ⊆ U → IsCompact K' →
    ContDiffOn ℝ 4 (Function.uncurry Ψ) (V ×ˢ U) →
    (∀ σ ∈ S, ∀ L ∈ K', ∀ k ∈ K, fderiv ℝ (Ψ σ) k + L = 0 → FoldOrNondegMatrix (Ψ σ) k) →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (σ : E) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      σ ∈ S → ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → L ∈ K' →
      1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ σ k + L k)) * Complex.I) * A k‖ ≤ C * M * m ^ (-(5 : ℝ) / 6)

theorem statement_pin_FoldLocal : FoldLocalStatement = FoldLocalStatement := rfl

/-- **FE-S4.1′L** Uniform D4 bound, Mathlib idiom, phase smooth only on an open neighbourhood `U` of `0`:
`D²φ(0) = 0`, cubic part `a x³ + b x²y + c xy² + d y³` with nonzero discriminant; decay `t^{-2/3}` uniformly over
all linear terms, for amplitudes supported in a small ball. -/
def D4BoundLocalStatement : Prop :=
  ∀ (φ : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) (a b c d : ℝ), IsOpen U → (0 : ℝ × ℝ) ∈ U → ContDiffOn ℝ 4 φ U →
    iteratedFDeriv ℝ 2 φ 0 = 0 →
    (∀ x y : ℝ, iteratedFDeriv ℝ 3 φ 0 ![(x, y), (x, y), (x, y)] =
      6 * (a * x ^ 3 + b * x ^ 2 * y + c * x * y ^ 2 + d * y ^ 3)) →
    (Cubic.mk a b c d).discr ≠ 0 →
    ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (t : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 δ → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      1 ≤ t →
      ‖∫ κ : ℝ × ℝ, Complex.exp (↑(t * φ κ + L κ) * Complex.I) * A κ‖ ≤ C * M * t ^ (-(2 : ℝ) / 3)

theorem statement_pin_D4BoundLocal : D4BoundLocalStatement = D4BoundLocalStatement := rfl

/-- **FE-S2.1l** Non-stationary phase, Mathlib idiom, one phase smooth on an open `U ⊇ K`. -/
def NonStationaryOnStatement : Prop :=
  ∀ (N : ℕ) (Ψ : ℝ × ℝ → ℝ) (K U : Set (ℝ × ℝ)) (c : ℝ),
    IsCompact K → IsOpen U → K ⊆ U → ContDiffOn ℝ (N + 1) Ψ U → 0 < c →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ N A → tsupport A ⊆ K → (∀ j ≤ N, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      (∀ k ∈ K, c ≤ ‖fderiv ℝ Ψ k + L‖) → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k‖ ≤ C * M / m ^ N

theorem statement_pin_NonStationaryOn : NonStationaryOnStatement = NonStationaryOnStatement := rfl

/-- **FE-S2.2l** Nondegenerate stationary phase, Mathlib idiom, one phase smooth on an open `U ⊇ K`. -/
def StationaryPhaseOnStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (K U : Set (ℝ × ℝ)) (K' : Set ((ℝ × ℝ) →L[ℝ] ℝ)),
    IsCompact K → IsOpen U → K ⊆ U → IsCompact K' → ContDiffOn ℝ 4 Ψ U →
    (∀ L ∈ K', ∀ k ∈ K, fderiv ℝ Ψ k + L = 0 → (hessianMatrix Ψ k).det ≠ 0) →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → L ∈ K' → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k‖ ≤ C * M / m

theorem statement_pin_StationaryPhaseOn : StationaryPhaseOnStatement = StationaryPhaseOnStatement := rfl

/-- **FE-S3l** Uniform fold estimate, Mathlib idiom, one phase smooth on an open `U ⊇ K`, classical hypothesis. -/
def FoldOnStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (K U : Set (ℝ × ℝ)) (K' : Set ((ℝ × ℝ) →L[ℝ] ℝ)),
    IsCompact K → IsOpen U → K ⊆ U → IsCompact K' → ContDiffOn ℝ 4 Ψ U →
    (∀ L ∈ K', ∀ k ∈ K, fderiv ℝ Ψ k + L = 0 → FoldOrNondegMatrix Ψ k) →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → L ∈ K' → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k‖ ≤ C * M * m ^ (-(5 : ℝ) / 6)

theorem statement_pin_FoldOn : FoldOnStatement = FoldOnStatement := rfl

/-! ## Sanity: generic witnesses, and bites separating these statements from their predecessors -/

/-- `∂_v (a x² + b y²)(y) = 2a y₁ v₁ + 2b y₂ v₂`. -/
theorem sanity_fd_quad (a b : ℝ) (y v : ℝ × ℝ) :
    fderiv ℝ (fun k : ℝ × ℝ => a * k.1 ^ 2 + b * k.2 ^ 2) y v = 2 * a * y.1 * v.1 + 2 * b * y.2 * v.2 := by
  have h : HasFDerivAt (fun k : ℝ × ℝ => a * k.1 ^ 2 + b * k.2 ^ 2)
      ((2 * a * y.1) • ContinuousLinearMap.fst ℝ ℝ ℝ + (2 * b * y.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
    convert (((hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 2).const_mul a).add
      (((hasFDerivAt_snd (𝕜 := ℝ) (p := y)).pow 2).const_mul b) using 1
    ext <;> simp <;> ring
  rw [h.fderiv]; simp

/-- The Hessian form of `a x² + b y²` is `2a v₁w₁ + 2b v₂w₂` at every point. -/
theorem sanity_dd_quad (a b : ℝ) (y v w : ℝ × ℝ) :
    dd (fun k : ℝ × ℝ => a * k.1 ^ 2 + b * k.2 ^ 2) y v w = 2 * a * v.1 * w.1 + 2 * b * v.2 * w.2 := by
  have : (fun y : ℝ × ℝ => fderiv ℝ (fun k : ℝ × ℝ => a * k.1 ^ 2 + b * k.2 ^ 2) y v) =
      fun y => (2 * a * v.1) * y.1 + (2 * b * v.2) * y.2 := by funext y; rw [sanity_fd_quad]; ring
  rw [dd, this, sanity_fd_lin]

theorem sanity_hessDet_quad (a b : ℝ) (y : ℝ × ℝ) :
    hessDet (fun k : ℝ × ℝ => a * k.1 ^ 2 + b * k.2 ^ 2) y = 4 * a * b := by
  simp only [hessDet, sanity_dd_quad]; ring

/-- A two-member family indexed by `Bool` (discrete, compact): `x² − y²` and `2x² + 3y²`. -/
def sanityQuadFamily (a b : Bool → ℝ) : Bool → ℝ × ℝ → ℝ := fun σ k => a σ * k.1 ^ 2 + b σ * k.2 ^ 2

theorem sanityQuadFamily_apply (a b : Bool → ℝ) (σ : Bool) :
    sanityQuadFamily a b σ = fun k : ℝ × ℝ => a σ * k.1 ^ 2 + b σ * k.2 ^ 2 := rfl

theorem sanity_familyCk_bool (n : ℕ) (a b : Bool → ℝ) : FamilyCk n (sanityQuadFamily a b) :=
  ⟨fun σ => by rw [sanityQuadFamily_apply]; fun_prop, fun j _ =>
    continuous_prod_of_discrete_left.mpr fun σ =>
      (ContDiff.continuous_iteratedFDeriv (m := j) le_rfl
        (by rw [sanityQuadFamily_apply]; fun_prop : ContDiff ℝ j (sanityQuadFamily a b σ)))⟩

/-- S2.2F hypotheses on a genuine family (two different nondegenerate quadratic phases, `K ≠ K'`), with a critical
point present; bite: a member with a degenerate Hessian at a critical point (`3y²`) violates the hypothesis. -/
theorem sanity_StationaryPhaseFamily_hyps :
    FamilyCk 4 (sanityQuadFamily (fun σ => if σ then 1 else 2) (fun σ => if σ then -1 else 3)) ∧
      (∀ σ, ∀ p ∈ Metric.closedBall (0 : ℝ × ℝ) 2, ∀ k ∈ Metric.closedBall (0 : ℝ × ℝ) 1,
        IsCritical (sanityQuadFamily (fun σ => if σ then 1 else 2) (fun σ => if σ then -1 else 3) σ) p k →
          hessDet (sanityQuadFamily (fun σ => if σ then 1 else 2) (fun σ => if σ then -1 else 3) σ) k ≠ 0) ∧
      IsCritical (sanityQuadFamily (fun σ => if σ then 1 else 2) (fun σ => if σ then -1 else 3) false) 0 0 ∧
      ¬ (∀ σ, ∀ p ∈ Metric.closedBall (0 : ℝ × ℝ) 2, ∀ k ∈ Metric.closedBall (0 : ℝ × ℝ) 1,
        IsCritical (sanityQuadFamily (fun σ => if σ then 1 else 0) (fun σ => if σ then -1 else 3) σ) p k →
          hessDet (sanityQuadFamily (fun σ => if σ then 1 else 0) (fun σ => if σ then -1 else 3) σ) k ≠ 0) := by
  refine ⟨sanity_familyCk_bool 4 _ _, fun σ p _ k _ _ => ?_, ?_, fun h => ?_⟩
  · rw [sanityQuadFamily_apply, sanity_hessDet_quad]; cases σ <;> norm_num
  · simp only [IsCritical, sanityQuadFamily_apply, sanity_fd_quad]; norm_num
  · have := h false 0 (Metric.mem_closedBall_self (by norm_num)) 0 (Metric.mem_closedBall_self (by norm_num))
      (by simp only [IsCritical, sanityQuadFamily_apply, sanity_fd_quad]; norm_num)
    rw [sanityQuadFamily_apply, sanity_hessDet_quad] at this
    norm_num at this

/-- Bite separating S3c from S3: for `x³ + y³` on `K = closedBall 0 2` and `K' = {(−3, −3)}` the classical
hypothesis holds (the critical points are `(±1, ±1)`, where the Hessian `diag(6x, 6y)` is invertible) and is not
vacuous (`(1, 1)` is critical), but `FoldOrNondeg` fails at `0 ∈ K` (the Hessian vanishes), so S3 does not apply. -/
theorem sanity_FoldCrit_bite :
    FamilyCk 4 (fun _ : Unit => fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) ∧
      (∀ p ∈ ({(-3, -3)} : Set (ℝ × ℝ)), ∀ k ∈ Metric.closedBall (0 : ℝ × ℝ) 2,
        IsCritical (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) p k → FoldOrNondeg (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) k) ∧
      IsCritical (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) (-3, -3) (1, 1) ∧
      (1, 1) ∈ Metric.closedBall (0 : ℝ × ℝ) 2 ∧
      ¬ FoldOrNondeg (fun k : ℝ × ℝ => k.1 ^ 3 + k.2 ^ 3) 0 := by
  refine ⟨sanity_familyCk_const _ _ (by fun_prop), fun p hp k _ hk => ?_, ?_, ?_, ?_⟩
  · rw [Set.mem_singleton_iff] at hp; subst hp
    simp only [IsCritical, sanity_fd_cubes] at hk
    obtain ⟨h1, h2⟩ := hk
    have hx : k.1 ≠ 0 := by rintro h; rw [h] at h1; norm_num at h1
    have hy : k.2 ≠ 0 := by rintro h; rw [h] at h2; norm_num at h2
    left
    simp only [hessDet, sanity_dd_cubes]; norm_num
    exact ⟨hx, hy⟩
  · simp only [IsCritical, sanity_fd_cubes]; norm_num
  · simp [Metric.mem_closedBall, Prod.norm_def]
  · rintro (h | ⟨⟨v, w, h⟩, -⟩)
    · simp [hessDet, sanity_dd_cubes] at h
    · simp [sanity_dd_cubes] at h

/-- C10 hypotheses on a genuinely parameter-dependent family `Ψ σ k = σ k₁ + k₂²` (`E = ℝ`). -/
theorem sanity_FamilyCkOfUncurry_hyps (n : ℕ) :
    ContDiff ℝ n (Function.uncurry fun (σ : ℝ) (k : ℝ × ℝ) => σ * k.1 + k.2 ^ 2) := by
  change ContDiff ℝ n (fun q : ℝ × (ℝ × ℝ) => q.1 * q.2.1 + q.2.2 ^ 2)
  fun_prop

/-- Bite for local smoothness: `|k₁|` is `C⁴` (indeed `C^∞`) on the open half-plane `{k₁ > 0}` but not `C¹` on
`ℝ²`, so the local statements apply to phases that front-end batch 2 (`ContDiff` on `ℝ²`) does not. The family
`σ |k₁| + k₂²` is `C⁴` on `ℝ × {k₁ > 0}` in the parameter and the point jointly. -/
theorem sanity_local_bite :
    IsOpen {k : ℝ × ℝ | 0 < k.1} ∧ ContDiffOn ℝ 4 (fun k : ℝ × ℝ => |k.1|) {k | 0 < k.1} ∧
      ¬ ContDiff ℝ 1 (fun k : ℝ × ℝ => |k.1|) ∧
      ContDiffOn ℝ 4 (Function.uncurry fun (σ : ℝ) (k : ℝ × ℝ) => σ * |k.1| + k.2 ^ 2)
        (Set.univ ×ˢ {k | 0 < k.1}) := by
  refine ⟨isOpen_lt continuous_const continuous_fst, contDiffOn_fst.congr fun k hk => abs_of_pos hk, fun h => ?_, ?_⟩
  · have hd : DifferentiableAt ℝ (fun k : ℝ × ℝ => |k.1|) ((0 : ℝ), (0 : ℝ)) :=
      (h.differentiable (by norm_num)) _
    have hl : DifferentiableAt ℝ (fun x : ℝ => ((x, (0 : ℝ)) : ℝ × ℝ)) 0 :=
      differentiableAt_id.prodMk (differentiableAt_const _)
    have : DifferentiableAt ℝ ((fun k : ℝ × ℝ => |k.1|) ∘ fun x : ℝ => ((x, (0 : ℝ)) : ℝ × ℝ)) 0 :=
      hd.comp (f := fun x : ℝ => ((x, (0 : ℝ)) : ℝ × ℝ)) (0 : ℝ) hl
    exact not_differentiableAt_abs_zero (by simpa [Function.comp_def] using this)
  · have : ContDiffOn ℝ 4 (fun q : ℝ × (ℝ × ℝ) => q.1 * q.2.1 + q.2.2 ^ 2) (Set.univ ×ˢ {k | 0 < k.1}) := by
      fun_prop
    exact this.congr fun q hq => by
      simp only [Function.uncurry, abs_of_pos (show 0 < q.2.1 from hq.2)]

end OscInt.Statements
