import OscInt.VanDerCorput.Final
import OscInt.StationaryPhase.Final
import OscInt.D4.Final
import OscInt.D4.ConstantPosFinal
import OscInt.D4.LimitFinal
import OscInt.D4.ClosedFormFinal
import OscInt.Statements.FrontEnd

/-!
# OscInt public API

Import this file: it imports every final theorem of OscInt. Every theorem in the table below has, as its type, a
statement constant that was frozen, stamped and blind-reviewed (`stamps/statements.json`, `docs/statements.md`); the
S1–S4 theorems keep their names in `OscInt`, and the front-end theorems F1 and F2 are proved here from them by short
bridge lemmas (`d4Constant_eq_closed` is such a helper; its type is not a frozen statement). For S1–S4 the statement
was reviewed before any proof existed; for F1 and F2 the bridge proofs were drafted before the statements were
stamped and reviewed, so that claim is not made for them (process note in `docs/statements.md`, "Front end, batch 1").

| Name | Statement | Textbook form |
|---|---|---|
| `OscInt.vanDerCorput_one/two/three` | S1.1–S1.3 | van der Corput's lemma with amplitude, constants c₁ = 3, c₂ = 8, c₃ = 18, i.e. Stein's c_k = 5·2^{k−1} − 2 (E. M. Stein, *Harmonic Analysis*, 1993, Ch. VIII §1) |
| `OscInt.nonStationary` | S2.1 | non-stationary phase, O(m^{−N}) (Stein, Ch. VIII §2), uniform over compact families and linear terms |
| `OscInt.stationaryPhase` | S2.2 | the stationary-phase bound O(m^{−n/2}) for n = 2 (Hörmander, *ALPDO I*, §7.7; Stein, Ch. VIII §2), uniform in the linear term |
| `OscInt.fold` | S3 | the uniform fold (A₂) estimate O(m^{−5/6}) (Arnold–Gusein-Zade–Varchenko, *Singularities of Differentiable Maps II*; Duistermaat 1974) |
| `OscInt.d4Bound`, `OscInt.d4BoundNe` | S4.1, S4.1′ | the uniform D4 (umbilic) estimate O(t^{−2/3}) (oscillation index −2/3 of D4, AGV II) |
| `OscInt.d4Limit`, `OscInt.d4ConstantPos`, `OscInt.d4ConstantClosedForm` | S4.2–S4.4 | the D4 leading term t^{2/3}∫e^{itφ}A → c_C A(0), c_C > 0, and c_C = Γ(1/3)²/(√3 \|Disc\|^{1/6}) for Disc < 0, Γ(1/3)²/Disc^{1/6} for Disc > 0 |
| `OscInt.API.ampBoundOfContDiff` | F1 | a Cⁿ function with compact support has bounded derivatives |
| `OscInt.API.d4LimitClosedForm` | F2 | the D4 leading term with the closed-form constant, for one C² amplitude (S4.2 ∧ S4.4 ∧ F1) |

The textbook references say which classical statement each formalises; they are given at chapter level from the
author's knowledge of the literature and were not re-checked against the books when this file was written (a human
expert review of the statements is an open owner item, ROADMAP §6); the precise Lean hypotheses (derivatives
continuous up to the endpoints, amplitude bounds `AmpBound`, the fold condition on all of K, …) are in
`docs/statements.md`, and what they add or omit relative to the textbooks is recorded there and in `docs/STATUS.md`.
-/

namespace OscInt.API

open Filter Topology OscInt.Statements

/-- **F1** A `Cⁿ` amplitude whose support closure lies in a compact set `K` satisfies the amplitude bound
`AmpBound n K A M` for some `M` (each `iteratedFDeriv ℝ j A`, `j ≤ n`, is continuous with support in `K`, hence
bounded). Use it to apply S2–S4 to an amplitude given in Mathlib's idiom. -/
theorem ampBoundOfContDiff : AmpBoundOfContDiffStatement := by
  intro n K A hK hA hsupp
  have hb : ∀ j ≤ n, ∃ M : ℝ, 0 ≤ M ∧ ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M := by
    intro j hj
    have hc : Continuous (iteratedFDeriv ℝ j A) := hA.continuous_iteratedFDeriv (by exact_mod_cast hj)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun k => ?_⟩
    by_cases hk : k ∈ K
    · exact (hC k hk).trans (le_max_left _ _)
    · have : k ∉ tsupport (iteratedFDeriv ℝ j A) := fun h => hk (hsupp (tsupport_iteratedFDeriv_subset j h))
      rw [image_eq_zero_of_notMem_tsupport this, norm_zero]; exact le_max_right _ _
  choose! Mj hMj0 hMj using hb
  refine ⟨∑ j ∈ Finset.range (n + 1), Mj j, hA, hsupp, fun j hj k => ?_⟩
  refine (hMj j hj k).trans ?_
  exact Finset.single_le_sum (f := Mj) (fun i hi => hMj0 i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

/-- S4.4 in terms of the discriminant: `c_C = d4ClosedConstant (disc C)` whenever `disc C ≠ 0`. -/
theorem d4Constant_eq_closed (q : ℝ × ℝ × ℝ × ℝ) (hq : disc q ≠ 0) :
    d4Constant q = d4ClosedConstant (disc q) := by
  rcases lt_or_gt_of_ne hq with h | h
  · rw [OscInt.d4ConstantClosedForm.2.1 q h, d4ClosedConstant]; simp only [h, ↓reduceIte]
  · rw [OscInt.d4ConstantClosedForm.2.2 q h, d4ClosedConstant]; simp only [not_lt.mpr h.le, ↓reduceIte]

/-- **F2** The D4 leading term with its closed-form constant: at a point where `φ`, `∇φ` and `∇²φ` vanish and the
cubic part `C` has `Disc C ≠ 0`, for every `C²` amplitude supported in a small ball,
`t^{2/3} ∫ e^{itφ} A → Γ(1/3)²/(√3 |Disc C|^{1/6}) · A(0)` (`Disc C < 0`) or `Γ(1/3)²/(Disc C)^{1/6} · A(0)`
(`Disc C > 0`). From S4.2 (`OscInt.d4Limit`), S4.4 (`OscInt.d4ConstantClosedForm`) and F1. -/
theorem d4LimitClosedForm : D4LimitClosedFormStatement := by
  intro φ hφ h0 h1 h2 hd
  obtain ⟨δ, hδ, hlim⟩ := OscInt.d4Limit φ hφ h0 h1 h2 hd
  refine ⟨δ, hδ, fun A hA hsupp => ?_⟩
  obtain ⟨M, hM⟩ := ampBoundOfContDiff 2 _ A (isCompact_closedBall 0 δ) hA hsupp
  have := hlim A M hM
  rw [d4Constant_eq_closed _ hd] at this
  exact this

end OscInt.API
