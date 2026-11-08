import OscInt.Statements.Global

/-!
# Batch VT: the global decay estimates for vector-valued amplitudes (statements only)

Mathematics: `docs/statements.md`, "Batch VT". Written, stamped and blind-reviewed before any proof of these statements
exists (`CONTRIBUTING.md`, lessons 23 and 29).

* GD-C-V, GD-V, GD-F-V, GD-N-V: the four global decay statements of batch GD (`OscInt/Statements/Global.lean`) with the
  amplitude `A : ℝ² → E` for an arbitrary complex Banach space `E`, the product `e^{imΦ} · A` replaced by the scalar
  action `e^{imΦ} • A`, and the constant `C` chosen before `E` (one constant for every `E`).

Modelling choices.
* `E : Type` (universe 0): matrices, `Fin n → ℂ`, `ℓ²`-type spaces and spaces of bounded operators on them all live
  there. A universe-polymorphic statement is not attempted (the commitment tooling hashes closed constants).
* `ContDiff ℝ 2 A` and `iteratedFDeriv ℝ j A` use the real structure of `E` (`NormedSpace.complexToReal`); the integral
  is Bochner's integral in `E`.
* Hypotheses on `Ψ`, `K`, `U`, `D`, `K′` and the rates are exactly those of the scalar statements; with `E = ℂ` each
  statement gives its scalar counterpart (`•` is `*` on `ℂ`).
-/

namespace OscInt.Statements

open scoped ContDiff

/-- **GD-C-V** GD-C for amplitudes with values in any complex Banach space `E` (`E : Type`), with a constant independent of `E`. -/
def GlobalDecayCritVecStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (K U : Set (ℝ × ℝ)) (K' : Set ((ℝ × ℝ) →L[ℝ] ℝ)) (D : Finset (ℝ × ℝ)),
    IsCompact K → IsOpen U → K ⊆ U → (↑D : Set (ℝ × ℝ)) ⊆ U → IsCompact K' → ContDiffOn ℝ 4 Ψ U →
    ClassifiedCrit Ψ K K' D →
    ∃ C : ℝ, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      (A : ℝ × ℝ → E) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → L ∈ K' → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) • A k‖ ≤ C * M * m ^ (-(2 : ℝ) / 3)

theorem statement_pin_GlobalDecayCritVec : GlobalDecayCritVecStatement = GlobalDecayCritVecStatement := rfl

/-- **GD-V** GD for amplitudes with values in any complex Banach space `E` (`E : Type`), with a constant independent of `E`. -/
def GlobalDecayVecStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (K U : Set (ℝ × ℝ)) (D : Finset (ℝ × ℝ)),
    IsCompact K → IsOpen U → K ⊆ U → (↑D : Set (ℝ × ℝ)) ⊆ U → ContDiffOn ℝ 4 Ψ U → Classified Ψ K D →
    ∃ C : ℝ, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      (A : ℝ × ℝ → E) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) • A k‖ ≤ C * M * m ^ (-(2 : ℝ) / 3)

theorem statement_pin_GlobalDecayVec : GlobalDecayVecStatement = GlobalDecayVecStatement := rfl

/-- **GD-F-V** GD-F for amplitudes with values in any complex Banach space `E` (`E : Type`), with a constant independent of `E`. -/
def GlobalFoldVecStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (K U : Set (ℝ × ℝ)),
    IsCompact K → IsOpen U → K ⊆ U → ContDiffOn ℝ 4 Ψ U → (∀ k ∈ K, FoldOrNondegMatrix Ψ k) →
    ∃ C : ℝ, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      (A : ℝ × ℝ → E) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) • A k‖ ≤ C * M * m ^ (-(5 : ℝ) / 6)

theorem statement_pin_GlobalFoldVec : GlobalFoldVecStatement = GlobalFoldVecStatement := rfl

/-- **GD-N-V** GD-N for amplitudes with values in any complex Banach space `E` (`E : Type`), with a constant independent of `E`. -/
def GlobalNondegVecStatement : Prop :=
  ∀ (Ψ : ℝ × ℝ → ℝ) (K U : Set (ℝ × ℝ)),
    IsCompact K → IsOpen U → K ⊆ U → ContDiffOn ℝ 4 Ψ U → (∀ k ∈ K, (hessianMatrix Ψ k).det ≠ 0) →
    ∃ C : ℝ, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      (A : ℝ × ℝ → E) (M : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℝ),
      ContDiff ℝ 2 A → tsupport A ⊆ K → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → 1 ≤ m →
      ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (Ψ k + L k)) * Complex.I) • A k‖ ≤ C * M / m

theorem statement_pin_GlobalNondegVec : GlobalNondegVecStatement = GlobalNondegVecStatement := rfl

end OscInt.Statements
