import OscInt.Statements.FrontEnd

/-!
# Front-end batch 2: conversions and Mathlib-idiom front ends (statements only)

Mathematics: `docs/statements.md`, "Front end, batch 2". Written, stamped and reviewed before any proof of these
statements exists (the statement-first order, restored after batch 1). Bridges: `OscInt/API/Convert.lean`.

Symbols (in addition to `OscInt/Statements/StationaryPhase.lean`, `D4.lean`, `D4Limit.lean`).
* `coordVec i` is the standard basis vector `eᵢ` of `ℝ × ℝ` (`e₀ = (1, 0)`, `e₁ = (0, 1)`); `ofFin2 e = (e 0, e 1)`.
* `hessianMatrix Ψ k` is the matrix `(D²Ψ(k)[eᵢ, eⱼ])ᵢⱼ`, with Mathlib's `iteratedFDeriv ℝ 2`.
* `FoldCondSpan H T`: `det H ≠ 0`, or `ker H = span {e}` for some `e ≠ 0` with `T e ≠ 0`.
* `FoldCondRank H T`: `det H ≠ 0`, or `rank H = 1` and `T e ≠ 0` for every nonzero `e ∈ ker H`.
  (`ker H` is `LinearMap.ker (Matrix.toLin' H)`: the `e : Fin 2 → ℝ` with `H *ᵥ e = 0`.)
* `FoldOrNondegMatrix Ψ k`: the span form for `hessianMatrix Ψ k` and `T e = D³Ψ(k)[ofFin2 e, ofFin2 e, ofFin2 e]`.
* `toEuclid k` is `k` as a point of `EuclideanSpace ℝ (Fin 2)`.

Modelling choices.
* Front ends take a linear term as a functional `L : (ℝ × ℝ) →L[ℝ] ℝ` and an amplitude bound as Mathlib terms
  (`ContDiff ℝ n A`, `tsupport A ⊆ K`, `‖iteratedFDeriv ℝ j A k‖ ≤ M` for `j ≤ n`), which is `AmpBound n K A M`
  written out; the integral is written out (the same term as `oscInt2`).
* Front ends are for one phase (no compact family); norms on `ℝ × ℝ` are the max norm (`‖L‖ = |L e₀| + |L e₁|`).
* In FE-S4.1′ the cubic part is given by coefficients `a b c d` and the identity
  `D³φ(0)[(x, y), (x, y), (x, y)] = 6 (a x³ + b x² y + c x y² + d y³)`; its discriminant is Mathlib's `Cubic.discr`.
-/

namespace OscInt.Statements

open Filter Topology

/-- The standard basis of `ℝ × ℝ`: `coordVec 0 = (1, 0)`, `coordVec 1 = (0, 1)`. -/
def coordVec : Fin 2 → ℝ × ℝ := ![(1, 0), (0, 1)]

/-- A vector `e : Fin 2 → ℝ` as the point `(e 0, e 1)` of `ℝ × ℝ`. -/
def ofFin2 (e : Fin 2 → ℝ) : ℝ × ℝ := (e 0, e 1)

/-- The Hessian matrix `(D²Ψ(k)[eᵢ, eⱼ])ᵢⱼ`. -/
noncomputable def hessianMatrix (Ψ : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => iteratedFDeriv ℝ 2 Ψ k ![coordVec i, coordVec j]

/-- Fold condition, span form: `H` is invertible, or its kernel is the line through some `e ≠ 0` with `T e ≠ 0`. -/
def FoldCondSpan (H : Matrix (Fin 2) (Fin 2) ℝ) (T : (Fin 2 → ℝ) → ℝ) : Prop :=
  H.det ≠ 0 ∨ ∃ e : Fin 2 → ℝ, e ≠ 0 ∧ LinearMap.ker (Matrix.toLin' H) = Submodule.span ℝ {e} ∧ T e ≠ 0

/-- Fold condition, rank form: `H` is invertible, or it has rank one and `T` is nonzero on its nonzero kernel. -/
def FoldCondRank (H : Matrix (Fin 2) (Fin 2) ℝ) (T : (Fin 2 → ℝ) → ℝ) : Prop :=
  H.det ≠ 0 ∨ (H.rank = 1 ∧ ∀ e ∈ LinearMap.ker (Matrix.toLin' H), e ≠ 0 → T e ≠ 0)

/-- The fold-or-nondegenerate condition at `k` in Mathlib's idiom (Hessian matrix, kernel, third derivative). -/
noncomputable def FoldOrNondegMatrix (Ψ : ℝ × ℝ → ℝ) (k : ℝ × ℝ) : Prop :=
  FoldCondSpan (hessianMatrix Ψ k) (fun e => iteratedFDeriv ℝ 3 Ψ k ![ofFin2 e, ofFin2 e, ofFin2 e])

/-- `k` as a point of the Euclidean plane. -/
noncomputable def toEuclid (k : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![k.1, k.2]

/-- **C1** Second derivatives: `dd Ψ k v w = D²Ψ(k)[v, w]` for `Ψ` of class `C²` near `k`. -/
def DdEqIteratedStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (k : ℝ × ℝ), ContDiffAt ℝ 2 Ψ k → ∀ v w, dd Ψ k v w = iteratedFDeriv ℝ 2 Ψ k ![v, w]

theorem statement_pin_DdEqIterated : DdEqIteratedStatement = DdEqIteratedStatement := rfl

/-- **C2** Third derivatives: `ddd Ψ k u v w = D³Ψ(k)[u, v, w]` for `Ψ` of class `C³` near `k`. -/
def DddEqIteratedStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (k : ℝ × ℝ), ContDiffAt ℝ 3 Ψ k →
    ∀ u v w, ddd Ψ k u v w = iteratedFDeriv ℝ 3 Ψ k ![u, v, w]

theorem statement_pin_DddEqIterated : DddEqIteratedStatement = DddEqIteratedStatement := rfl

/-- **C3** `hessDet Ψ k = det (hessianMatrix Ψ k)` for `Ψ` of class `C²` near `k`. -/
def HessDetEqDetStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (k : ℝ × ℝ), ContDiffAt ℝ 2 Ψ k → hessDet Ψ k = (hessianMatrix Ψ k).det

theorem statement_pin_HessDetEqDet : HessDetEqDetStatement = HessDetEqDetStatement := rfl

/-- **C4** The cubic part: `cubicForm (cubicCoeffs φ) κ = D³φ(0)[κ, κ, κ] / 6` for `φ` of class `C³` near `0`. -/
def CubicCoeffsEqStatement : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, ContDiffAt ℝ 3 φ 0 →
    ∀ κ : ℝ × ℝ, cubicForm (cubicCoeffs φ) κ = iteratedFDeriv ℝ 3 φ 0 ![κ, κ, κ] / 6

theorem statement_pin_CubicCoeffsEq : CubicCoeffsEqStatement = CubicCoeffsEqStatement := rfl

/-- **C5** `disc` is Mathlib's discriminant of the cubic polynomial `a X³ + b X² + c X + d`. -/
def DiscEqCubicDiscrStatement : Prop :=
  ∀ a b c d : ℝ, disc (a, b, c, d) = (Cubic.mk a b c d).discr

theorem statement_pin_DiscEqCubicDiscr : DiscEqCubicDiscrStatement = DiscEqCubicDiscrStatement := rfl

/-- **C6** `disc q ≠ 0` iff `0` is an isolated critical point of the binary cubic `cubicForm q`. -/
def DiscNeZeroIffIsolatedStatement : Prop :=
  ∀ q : ℝ × ℝ × ℝ × ℝ, disc q ≠ 0 ↔ ∀ᶠ z in 𝓝[≠] (0 : ℝ × ℝ), fderiv ℝ (cubicForm q) z ≠ 0

theorem statement_pin_DiscNeZeroIffIsolated :
    DiscNeZeroIffIsolatedStatement = DiscNeZeroIffIsolatedStatement := rfl

/-- **C7** `FoldOrNondeg` in matrix form (span form and rank form) for `Ψ` of class `C³` near `k`. -/
def FoldOrNondegIffStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (k : ℝ × ℝ), ContDiffAt ℝ 3 Ψ k →
    (FoldOrNondeg Ψ k ↔ FoldOrNondegMatrix Ψ k) ∧
      (FoldOrNondeg Ψ k ↔
        FoldCondRank (hessianMatrix Ψ k) (fun e => iteratedFDeriv ℝ 3 Ψ k ![ofFin2 e, ofFin2 e, ofFin2 e]))

theorem statement_pin_FoldOrNondegIff : FoldOrNondegIffStatement = FoldOrNondegIffStatement := rfl

/-- **C7′** `FoldOrNondeg` from derivative data: `Ψ' = D₁`, `D₁' = D₂` everywhere and `D₂'(k) = D₃`. -/
def FoldOrNondegOfHasFDerivStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (D₁ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ) (D₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ)
    (D₃ : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ) (k : ℝ × ℝ),
    (∀ y, HasFDerivAt Ψ (D₁ y) y) → (∀ y, HasFDerivAt D₁ (D₂ y) y) → HasFDerivAt D₂ D₃ k →
    (FoldOrNondeg Ψ k ↔
      FoldCondSpan (Matrix.of fun i j => D₂ k (coordVec i) (coordVec j))
        (fun e => D₃ (ofFin2 e) (ofFin2 e) (ofFin2 e)))

theorem statement_pin_FoldOrNondegOfHasFDeriv :
    FoldOrNondegOfHasFDerivStatement = FoldOrNondegOfHasFDerivStatement := rfl

/-- **C8** `GradLower` as a norm bound: Euclidean (an equivalence) and max norm (both directions, losing `√2`). -/
def GradLowerIffStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (p k : ℝ × ℝ) (c : ℝ), DifferentiableAt ℝ Ψ k → 0 ≤ c →
    (GradLower Ψ p k c ↔
        c ≤ ‖fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 2) => Ψ (x 0, x 1) + lin p (x 0, x 1)) (toEuclid k)‖) ∧
      (GradLower Ψ p k c → c ≤ ‖fderiv ℝ (fun x => Ψ x + lin p x) k‖) ∧
      (c ≤ ‖fderiv ℝ (fun x => Ψ x + lin p x) k‖ → GradLower Ψ p k (c / Real.sqrt 2))

theorem statement_pin_GradLowerIff : GradLowerIffStatement = GradLowerIffStatement := rfl

/-- **C9** `AmpBound` and Mathlib's idiom: (i) on a compact `K` it gives `Cⁿ` with compact support; (ii) `Cⁿ` with
compact support gives `AmpBound n (tsupport A) A M` for some `M`. -/
def AmpBoundConvStatement : Prop :=
  (∀ (n : ℕ) (K : Set (ℝ × ℝ)) (A : ℝ × ℝ → ℂ) (M : ℝ), IsCompact K → AmpBound n K A M →
      ContDiff ℝ n A ∧ HasCompactSupport A) ∧
    ∀ (n : ℕ) (A : ℝ × ℝ → ℂ), ContDiff ℝ n A → HasCompactSupport A → ∃ M : ℝ, AmpBound n (tsupport A) A M

theorem statement_pin_AmpBoundConv : AmpBoundConvStatement = AmpBoundConvStatement := rfl

/-- **FE-S2.1** Non-stationary phase in Mathlib's idiom (one phase): decay `m^{-N}`, uniform over amplitudes with
derivative bound `M` and over linear terms `L` with `‖DΨ(k) + L‖ ≥ c` on `K`. -/
def NonStationaryFEStatement : Prop :=
  ∀ (N : ℕ) (Ψ : ℝ × ℝ → ℝ) (K : Set (ℝ × ℝ)) (c : ℝ), ContDiff ℝ (N + 1) Ψ → IsCompact K → 0 < c →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ N A → tsupport A ⊆ K → (∀ j ≤ N, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      (∀ k ∈ K, c ≤ ‖fderiv ℝ Ψ k + L‖) → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k‖ ≤ C * M / m ^ N

theorem statement_pin_NonStationaryFE : NonStationaryFEStatement = NonStationaryFEStatement := rfl

/-- **FE-S2.2** Nondegenerate stationary phase in Mathlib's idiom: decay `m^{-1}`, uniform over `L ∈ K'`. -/
def StationaryPhaseFEStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (K : Set (ℝ × ℝ)) (K' : Set ((ℝ × ℝ) →L[ℝ] ℝ)),
    ContDiff ℝ 4 Ψ → IsCompact K → IsCompact K' →
    (∀ L ∈ K', ∀ k ∈ K, fderiv ℝ Ψ k + L = 0 → (hessianMatrix Ψ k).det ≠ 0) →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → L ∈ K' → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k‖ ≤ C * M / m

theorem statement_pin_StationaryPhaseFE : StationaryPhaseFEStatement = StationaryPhaseFEStatement := rfl

/-- **FE-S3** Uniform fold estimate in Mathlib's idiom (one phase): decay `m^{-5/6}`, uniform over `L ∈ K'`. -/
def FoldFEStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (K : Set (ℝ × ℝ)) (K' : Set ((ℝ × ℝ) →L[ℝ] ℝ)),
    ContDiff ℝ 4 Ψ → IsCompact K → IsCompact K' → (∀ k ∈ K, FoldOrNondegMatrix Ψ k) →
    ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → L ∈ K' → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) * A k‖ ≤ C * M * m ^ (-(5 : ℝ) / 6)

theorem statement_pin_FoldFE : FoldFEStatement = FoldFEStatement := rfl

/-- **FE-S4.1′** Uniform D4 bound in Mathlib's idiom: `D²φ(0) = 0`, cubic part `a x³ + b x²y + c xy² + d y³` with
nonzero discriminant; decay `t^{-2/3}` uniformly over all linear terms. -/
def D4BoundFEStatement : Prop :=
  ∀ (φ : ℝ × ℝ → ℝ) (a b c d : ℝ), ContDiff ℝ 4 φ → iteratedFDeriv ℝ 2 φ 0 = 0 →
    (∀ x y : ℝ, iteratedFDeriv ℝ 3 φ 0 ![(x, y), (x, y), (x, y)] =
      6 * (a * x ^ 3 + b * x ^ 2 * y + c * x * y ^ 2 + d * y ^ 3)) →
    (Cubic.mk a b c d).discr ≠ 0 →
    ∃ δ > 0, ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (t : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 δ → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) →
      1 ≤ t →
      ‖∫ κ : ℝ × ℝ, Complex.exp (↑(t * φ κ + L κ) * Complex.I) * A κ‖ ≤ C * M * t ^ (-(2 : ℝ) / 3)

theorem statement_pin_D4BoundFE : D4BoundFEStatement = D4BoundFEStatement := rfl

/-! ## Sanity (on data; derivative hypotheses of explicit phases are checked after the proofs, through the bridges) -/

/-- `coordVec` and `ofFin2` are the standard basis and coordinates, in this order. -/
theorem sanity_coordVec : coordVec 0 = (1, 0) ∧ coordVec 1 = (0, 1) ∧ ofFin2 ![2, 3] = (2, 3) :=
  ⟨rfl, rfl, rfl⟩

/-- `toEuclid` keeps the coordinates in order. -/
theorem sanity_toEuclid (k : ℝ × ℝ) : toEuclid k 0 = k.1 ∧ toEuclid k 1 = k.2 := by
  simp [toEuclid]

/-- `disc` and `Cubic.discr` on generic coefficients `(1, 2, 3, 5)`: both are `−367`; on `x³ − 3xy²`: `108`. -/
theorem sanity_discr_values :
    (Cubic.mk (1 : ℝ) 2 3 5).discr = -367 ∧ disc (1, 2, 3, 5) = -367 ∧ (Cubic.mk (1 : ℝ) 0 (-3) 0).discr = 108 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [Cubic.discr, disc]

/-- Bite for C6: `x²y` (coefficients `(0, 1, 0, 0)`) has a repeated factor and `disc = 0`; `x³ + y³` has `−27`. -/
theorem sanity_disc_bite : disc (0, 1, 0, 0) = 0 ∧ disc (1, 0, 0, 1) = -27 := by
  constructor <;> norm_num [disc]

/-- The fold matrix `diag(0, 2)` of `x³ + y²` at `0`: its kernel is the line through `(1, 0)`. -/
theorem sanity_ker_fold :
    LinearMap.ker (Matrix.toLin' !![(0 : ℝ), 0; 0, 2]) = Submodule.span ℝ {![1, 0]} := by
  ext e
  simp only [LinearMap.mem_ker, Matrix.toLin'_apply, Submodule.mem_span_singleton]
  constructor
  · intro h
    have h1 : e 1 = 0 := by
      have := congrFun h 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      exact this
    refine ⟨e 0, ?_⟩
    ext i; fin_cases i <;> simp [h1]
  · rintro ⟨a, rfl⟩
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The span form holds for the fold data (`H = diag(0, 2)`, `T e = 6 e₀³`: the Hessian and third derivative of
`x³ + y²` at `0`) and for a generic invertible matrix. Bite: it fails when `T` vanishes on the kernel line
(`T e = 6 e₁³`), and for the zero matrix, whose kernel is the whole plane and so is no line. -/
theorem sanity_FoldCondSpan :
    FoldCondSpan !![(0 : ℝ), 0; 0, 2] (fun e => 6 * e 0 ^ 3) ∧
      FoldCondSpan !![(1 : ℝ), 2; 2, 5] (fun _ => 0) ∧
      ¬ FoldCondSpan !![(0 : ℝ), 0; 0, 2] (fun e => 6 * e 1 ^ 3) ∧
      ¬ FoldCondSpan (0 : Matrix (Fin 2) (Fin 2) ℝ) (fun _ => 1) := by
  refine ⟨Or.inr ⟨![1, 0], by simp, sanity_ker_fold, by norm_num⟩, Or.inl (by simp [Matrix.det_fin_two]; norm_num),
    ?_, ?_⟩
  · rintro (h | ⟨e, he, hker, hT⟩)
    · simp [Matrix.det_fin_two] at h
    · have : e ∈ Submodule.span ℝ {(![1, 0] : Fin 2 → ℝ)} := by
        rw [← sanity_ker_fold, hker]; exact Submodule.mem_span_singleton_self e
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp this
      simp at hT
  · rintro (h | ⟨e, he, hker, -⟩)
    · simp at h
    · have h1 : (![0, 1] : Fin 2 → ℝ) ∈ Submodule.span ℝ {e} := by
        rw [← hker]; simp
      have h0 : (![1, 0] : Fin 2 → ℝ) ∈ Submodule.span ℝ {e} := by
        rw [← hker]; simp
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h0
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp h1
      have e1 := congrFun ha 1; have e0 := congrFun ha 0
      have f1 := congrFun hb 1; have f0 := congrFun hb 0
      simp at e1 e0 f1 f0
      -- a e₀ = 1, a e₁ = 0, b e₀ = 0, b e₁ = 1: then e₁ = 0 and b e₁ = 1, a contradiction
      have ha0 : a ≠ 0 := by rintro rfl; simp at e0
      have : e 1 = 0 := by
        rcases e1 with h | h
        · exact absurd h ha0
        · exact h
      rw [this, mul_zero] at f1
      exact zero_ne_one f1

/-- The rank form on the same fold data: `diag(0, 2)` has rank one. -/
theorem sanity_rank_fold : (!![(0 : ℝ), 0; 0, 2]).rank = 1 := by
  have h : LinearMap.range (!![(0 : ℝ), 0; 0, 2]).mulVecLin = Submodule.span ℝ {(![0, 2] : Fin 2 → ℝ)} := by
    ext v
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨e, rfl⟩
      refine ⟨e 1, ?_⟩
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
    · rintro ⟨a, rfl⟩
      refine ⟨![0, a], ?_⟩
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  rw [Matrix.rank, h, finrank_span_singleton (by simp)]

/-- The rank form on the same fold data, and its bite when `T` vanishes on the kernel. -/
theorem sanity_FoldCondRank :
    FoldCondRank !![(0 : ℝ), 0; 0, 2] (fun e => 6 * e 0 ^ 3) ∧
      ¬ FoldCondRank !![(0 : ℝ), 0; 0, 2] (fun e => 6 * e 1 ^ 3) := by
  refine ⟨Or.inr ⟨sanity_rank_fold, fun e he hne => ?_⟩, ?_⟩
  · rw [sanity_ker_fold] at he
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp he
    have ha : a ≠ 0 := by rintro rfl; simp at hne
    simpa using ha
  · rintro (h | ⟨-, h⟩)
    · simp [Matrix.det_fin_two] at h
    · exact h ![1, 0] (by rw [sanity_ker_fold]; exact Submodule.mem_span_singleton_self _) (by simp) (by simp)

/-- The amplitude hypothesis of the front ends is satisfiable by a nonzero amplitude: the bump of
`sanity_ampBound_exists`, written out in Mathlib's idiom. -/
theorem sanity_FE_amplitude :
    ∃ (A : ℝ × ℝ → ℂ) (M : ℝ), ContDiff ℝ 2 A ∧ tsupport A ⊆ Metric.closedBall 0 1 ∧
      (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) ∧ A 0 = 1 := by
  obtain ⟨A, M, ⟨h1, h2, h3⟩, h4⟩ := sanity_ampBound_exists 2
  exact ⟨A, M, h1, h2, h3, h4⟩

end OscInt.Statements
