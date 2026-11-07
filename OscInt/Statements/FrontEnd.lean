import OscInt.Statements.D4Limit

/-!
# Front-end statements, batch 1 (statements only)

Mathematics: `docs/statements.md`, "Front end". These are user-facing forms of frozen statements, proved from them by
bridge lemmas (`OscInt/API.lean`); they are frozen, stamped and reviewed like every statement.

* F1 `AmpBoundOfContDiffStatement`: a `Cⁿ` amplitude whose support closure lies in a compact set `K` satisfies the
  amplitude bound `(n, K, M)` for some `M`. It converts Mathlib's idiom (`ContDiff ℝ n A`, `tsupport A ⊆ K`) into the
  hypothesis `AmpBound` of S2–S4.
* F2 `D4LimitClosedFormStatement`: the brief's S4 limit with its closed-form constant, for a fixed amplitude in
  Mathlib's idiom: at a D4 point with `Disc < 0`, `t^{2/3} ∫ e^{itφ} A → Γ(1/3)²/(√3 |Disc|^{1/6}) · A(0)`; with
  `Disc > 0`, the constant is `Γ(1/3)²/Disc^{1/6}` (`d4ClosedConstant`). (S4.2 ∧ S4.4 ∧ F1.)

Modelling choices.
* The integral is written out (`∫ k, exp(i t φ(k)) A(k) dk` over `ℝ × ℝ` with Lebesgue measure), not through
  `oscInt2`; it is the same term.
* Phase hypotheses are those of S4.2 (`ContDiff ℝ 4 φ`, `φ 0 = 0`, `fderiv ℝ φ 0 = 0`, `dd φ 0 = 0`) and the cubic
  part is `cubicCoeffs φ` (third derivatives at `0` as nested `fderiv`s); conversions from `iteratedFDeriv` are later
  batches (ROADMAP §2).
-/

namespace OscInt.Statements

open Filter Topology

/-- **F1** Amplitude bounds from Mathlib's idiom: a `Cⁿ` amplitude with `tsupport A ⊆ K`, `K` compact, satisfies
`AmpBound n K A M` for some `M`. -/
def AmpBoundOfContDiffStatement : Prop :=
  ∀ (n : ℕ) (K : Set (ℝ × ℝ)) (A : ℝ × ℝ → ℂ), IsCompact K → ContDiff ℝ n A → tsupport A ⊆ K →
    ∃ M : ℝ, AmpBound n K A M

theorem statement_pin_AmpBoundOfContDiff : AmpBoundOfContDiffStatement = AmpBoundOfContDiffStatement := rfl

/-- The closed-form D4 constant as a function of the discriminant: `Γ(1/3)²/(√3 |D|^{1/6})` for `D < 0` (the brief's
constant), `Γ(1/3)²/D^{1/6}` otherwise (used for `D > 0`; S4.4 gives `c_C = d4ClosedConstant (disc C)` for `D ≠ 0`). -/
noncomputable def d4ClosedConstant (D : ℝ) : ℝ :=
  if D < 0 then Real.Gamma (1 / 3) ^ 2 / (Real.sqrt 3 * |D| ^ ((1 : ℝ) / 6))
  else Real.Gamma (1 / 3) ^ 2 / D ^ ((1 : ℝ) / 6)

/-- **F2** The D4 limit with its closed-form constant (the brief's S4), for a `C²` amplitude supported near `0`:
`t^{2/3} ∫ e^{itφ} A → Γ(1/3)²/(√3 |Disc|^{1/6}) A(0)` if `Disc < 0`, and `→ Γ(1/3)²/Disc^{1/6} A(0)` if `Disc > 0`. -/
def D4LimitClosedFormStatement : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ 4 φ → φ 0 = 0 → fderiv ℝ φ 0 = 0 → (∀ v w, dd φ 0 v w = 0) →
    disc (cubicCoeffs φ) ≠ 0 →
    ∃ δ > 0, ∀ A : ℝ × ℝ → ℂ, ContDiff ℝ 2 A → tsupport A ⊆ Metric.closedBall 0 δ →
      Tendsto (fun t : ℝ => ((t ^ ((2 : ℝ) / 3) : ℝ) : ℂ) *
          ∫ k : ℝ × ℝ, Complex.exp (↑(t * φ k) * Complex.I) * A k) atTop
        (𝓝 ((d4ClosedConstant (disc (cubicCoeffs φ)) : ℂ) * A 0))

theorem statement_pin_D4LimitClosedForm : D4LimitClosedFormStatement = D4LimitClosedFormStatement := rfl

/-! ## Sanity -/

/-- F1's hypotheses are satisfiable by a nonzero amplitude: a smooth bump (`ContDiffBump`) with radii `1 < 2`,
supported in `closedBall 0 2`, which is compact. -/
theorem sanity_AmpBoundOfContDiff_hyps :
    ∃ A : ℝ × ℝ → ℂ, ContDiff ℝ 2 A ∧ tsupport A ⊆ Metric.closedBall 0 2 ∧ A 0 = 1 ∧
      IsCompact (Metric.closedBall (0 : ℝ × ℝ) 2) := by
  let b : ContDiffBump (0 : ℝ × ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun k => (b k : ℂ), ?_, ?_, ?_, isCompact_closedBall 0 2⟩
  · exact Complex.ofRealCLM.contDiff.comp b.contDiff
  · have : Function.support (fun k => (b k : ℂ)) = Function.support b := by
      ext k; simp [Function.mem_support]
    rw [tsupport, this, ← tsupport, b.tsupport_eq]
  · simp [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]

/-- The constant on `x³ + y³` (`disc = −27`): `Γ(1/3)²/(√3 · 27^{1/6}) = Γ(1/3)²/3`, the textbook value. -/
theorem sanity_d4ClosedConstant_cubes : d4ClosedConstant (-27) = Real.Gamma (1 / 3) ^ 2 / 3 := by
  have h : Real.sqrt 3 * |(-27 : ℝ)| ^ ((1 : ℝ) / 6) = 3 := by
    rw [show |(-27 : ℝ)| = 3 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num), Real.sqrt_eq_rpow,
      ← Real.rpow_add (by norm_num)]
    norm_num
  simp only [d4ClosedConstant, show (-27 : ℝ) < 0 by norm_num, ↓reduceIte, h]

/-- Bite: the constant is positive for every nonzero discriminant (no junk `0`), so F2 forces
`t^{2/3} |∫ e^{itφ} A| → c > 0` whenever `A(0) ≠ 0`. -/
theorem sanity_d4ClosedConstant_pos (D : ℝ) (hD : D ≠ 0) : 0 < d4ClosedConstant D := by
  have hG : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  unfold d4ClosedConstant
  split_ifs with h
  · have : 0 < |D| := abs_pos.mpr hD
    positivity
  · have : 0 < D := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hD)
    positivity

/-- The two branches of the constant on generic discriminants (`−367` from `x³ + 2x²y + 3xy² + 5y³`, `1` from
`xy(x + y)`), so a swap of the branches or of `|D|` and `D` would show here. -/
theorem sanity_d4ClosedConstant_branches :
    d4ClosedConstant (-367) = Real.Gamma (1 / 3) ^ 2 / (Real.sqrt 3 * (367 : ℝ) ^ ((1 : ℝ) / 6)) ∧
      d4ClosedConstant 1 = Real.Gamma (1 / 3) ^ 2 := by
  refine ⟨?_, ?_⟩
  · simp only [d4ClosedConstant, show (-367 : ℝ) < 0 by norm_num, ↓reduceIte]; norm_num
  · simp only [d4ClosedConstant, show ¬ (1 : ℝ) < 0 by norm_num, ↓reduceIte]; norm_num

end OscInt.Statements
