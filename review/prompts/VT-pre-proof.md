# Blind statement review: batch VT (GD-C-V, GD-V, GD-F-V, GD-N-V)

You are a fresh referee. Judge whether the Lean statements say what the mathematics says, whether each is TRUE, and
whether each is non-vacuous and useful. Two referees review independently; do not look for the other's report.
No Lean proof of these four statements exists in the repository or in the lead's scratch. **Do not prove the
statements under review, not even in your own scratch: Lean checks of small facts (elaboration, instances, how a
definition unfolds on data, whether a Mathlib lemma exists with a given signature) and numerical checks only**
(lessons 24).

Read: `docs/statements.md` (section "Batch VT" in full; "Batch GD" for the scalar statements this batch generalises),
`OscInt/Statements/Vector.lean` (the batch), `OscInt/Statements/Global.lean` (the frozen scalar statements and shared
definitions), `OscInt/Front/VectorSanity.lean` (sanity theorems through the constants) with
`docs/replay/2026-11-08-VT-sanity-plants.txt`, `docs/design/vector-amplitudes.md` (§1 the duality route; §5 why the
two-band model is deferred), `docs/lessons.md` (entries 11, 12, 17, 24, 33), and Mathlib sources under
`.lake/packages/mathlib`. You may compile scratch files under `/tmp/<your name>/` with
`nice -n 10 lake env lean -DautoImplicit=false FILE` from the repository root (`. ~/.leanenv`; one Lean process at a
time). Write nothing in the repository.

For each statement constant:
1. Verdict against `docs/statements.md`: FAITHFUL / FAITHFUL-WEAKER / FAITHFUL-STRONGER / UNFAITHFUL. Is it TRUE? Pay
   attention to: the binder `∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]` inside a `Prop`
   and after `∃ C` (one constant for every E: is that true? is it what the docs say?); which `NormedSpace ℝ E` instance
   `ContDiff ℝ 2 A` and `iteratedFDeriv ℝ j A` use (`NormedSpace.complexToReal`?) and whether the norm of the real
   `iteratedFDeriv` is the natural one; the scalar action `Complex.exp (…) • A k` and the Bochner integral in E; the
   universe restriction `E : Type`; whether the hypotheses on Ψ, K, U, D, K′ and the rates are character for character
   those of GD-C, GD, GD-F, GD-N.
2. Derivability: is each implied by its proved scalar statement by the duality route in the docs (Hahn–Banach
   `exists_dual_vector''`, `ContinuousLinearMap.integral_comp_comm` and its integrability hypothesis, the derivative
   bound for ℓ ∘ A with ℓ restricted to ℝ-scalars, ‖ℓ‖ ≤ 1)? Name any step that fails, e.g. measurability or
   integrability of `k ↦ e^{imΨ(k)} • A(k)` when Ψ is smooth only on U, or E = 0.
3. Vacuity and usefulness: does the E = ℂ case give the scalar statement exactly (the sanity file says so: check)? Can
   a user apply GD-N-V to matrix-valued amplitudes (`Fin 2 → Fin 2 → ℂ` with the sup norm; `Matrix` itself has no
   global norm instance in Mathlib: is that a usability problem worth noting)?
4. The sanity theorems and planted controls: what would they miss? The record says the 'C after E' plant is rejected
   only by brittleness: is that right, and does it matter?
5. Findings as BLOCKER / MAJOR / MINOR / NIT with the exact Lean text. First line of your report: `git rev-parse
   HEAD`. Return the report as your final message.
