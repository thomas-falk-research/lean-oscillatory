# Brief: sanity theorems through the statement constants (API3, answer to pre-proof MAJOR M1 of both referees)

Repository `/home/user/lean-oscillatory` (built; `export PATH=$HOME/.elan/bin:$PATH`). Write ONE file
`/tmp/sanity-agent/FamilySanity.lean` (scratch; do not write in the repository). Compile with
`nice -n 10 lake env lean -DautoImplicit=false /tmp/sanity-agent/FamilySanity.lean` from the repository root, one Lean
process at a time. First lines:

```lean
import OscInt
namespace OscInt.API.FamilySanity
open OscInt.Statements OscInt.API.ConvertAux
```

## Absolute rule
The ten statements of `OscInt/Statements/Family.lean` are frozen and NOT proved. You must not prove any of them, in
whole or in part, anywhere. Every theorem you write about them takes the statement constant(s) as HYPOTHESES (e.g.
`(h : FoldCritStatement)`) and only *applies* them to concrete data, discharging the hypotheses of the statement on
that data. The point: if someone planted an error in a statement body (named below), the discharge for these data
would become impossible, so the file would stop compiling. You may use every already-proved theorem of the library
(e.g. `OscInt.API.dd_iteratedFDeriv`, `OscInt.API.hessDet_eq_det`, `OscInt.API.foldOrNondeg_iff`,
`ConvertAux.functional_eq_zero_iff`, the `sanity_*` lemmas of `OscInt/Statements/*.lean`, e.g. `sanity_fd_cubes`,
`sanity_dd_cubes`, `sanity_ddd_cubes`, `sanity_fd_lin`, `sanity_familyCk_const`).

## Library rules (the guard rejects violations)
No `sorry`, `admit`, `axiom`, `native_decide`, `private`, `set_option` (except `set_option maxHeartbeats N in`),
`open Lean`, `Lean.`, macros/elab/notation/attribute, `#eval`. Write `ContDiff ℝ n` with numerals, never `⊤`. Each
declaration ≤ ~60 lines; helpers are `theorem`s with docstrings. Check every Mathlib name with `#check` before relying
on it (remove `#check` lines at the end).

## Theorems to deliver (names fixed)
1. `foldCrit_fold_bite (h : FoldCritStatement) : ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M m : ℝ),
   AmpBound 2 (Metric.closedBall 0 2) A M → 1 ≤ m →
   ‖oscInt2 (fun k => m * ((k.1 ^ 3 + k.2 ^ 3) + lin (0, -3) k)) A‖ ≤ C * M * m ^ (-(5 : ℝ) / 6)`.
   Data: one-point family `Unit`, Ψ = x³ + y³, K = closedBall 0 2, K' = {(0, −3)}. Critical points: (0, ±1), folds
   (Hessian diag(0, 6k₂), kernel e₁, ddd e₁e₁e₁ = 6). Fails under the plants `p ↦ 0` (critical point 0, Hessian 0)
   and "fold condition at every k ∈ K" (0 ∈ K). Add a docstring saying so and that neither S2.2 nor S3 applies here.
2. A phase `Ψσ(k) = σ (k₁⁴ + 4k₁) + k₂²` (`def signFamily (σ : ℝ) (k : ℝ × ℝ) : ℝ`), its derivative lemmas
   (`fderiv … y v = σ (4y₁³ + 4) v₁ + 2y₂ v₂`, `dd … y v w = 12σ y₁² v₁w₁ + 2 v₂w₂`, `hessDet = 24 σ y₁²`).
3. `stationaryPhaseFamily_sign_bite (hC10 : FamilyCkOfUncurryStatement) (h : StationaryPhaseFamilyStatement) :
   ∃ C : ℝ, ∀ (A : ℝ × ℝ → ℂ) (M : ℝ) (σ : Set.Icc (1 : ℝ) 2) (m : ℝ), AmpBound 2 (Metric.closedBall 0 2) A M →
   1 ≤ m → ‖oscInt2 (fun k => m * (signFamily σ k + lin (4, 0) k)) A‖ ≤ C * M / m`.
   Family over the infinite compact `Icc 1 2` (FamilyCk from `hC10 ℝ 4 signFamily _ (Set.Icc 1 2)`), K = closedBall 0 2,
   K' = {(4, 0)}. Critical: σ(4x³ + 4) + 4 = 0 ⇒ x ≠ 0 ⇒ hessDet = 24σx² ≠ 0. Docstring: fails under `p ↦ -p` (σ = 1,
   critical point at 0, Hessian degenerate), `p ↦ 0` (x³ = −1 still nondegenerate — say honestly this plant is NOT
   caught here; theorem 1 catches it for S3c) and "everywhere" (0 ∈ K).
4. `foldCrit_sign_bite (hC10 : FamilyCkOfUncurryStatement) (h : FoldCritStatement)` with the same data and rate
   m^{−5/6} (nondegenerate ⇒ `FoldOrNondeg` by its left branch). Docstring: fails under `p ↦ -p` (σ = 1: critical
   point (0, 0), Hessian diag(0, 2), kernel e₁, ddd e₁e₁e₁ = 24σ·0 = 0, so not a fold).
5. Mathlib-idiom forms through `StationaryPhaseOnStatement` and `FoldOnStatement`: phase singular outside U,
   `def kinkPhase (k : ℝ × ℝ) : ℝ := k.1 ^ 4 + 4 * |k.1 + 3| - 12 + k.2 ^ 2`, `U = {k | -3 < k.1}`,
   `K = closedBall 0 2` (⊆ U in the max norm), `K' = {L₀}` with `L₀ = (4 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ`.
   On U the phase equals the polynomial `k.1 ^ 4 + 4 * k.1 + k.2 ^ 2` (germ equality: `Filter.EventuallyEq`), so
   `fderiv` and `iteratedFDeriv ℝ 2/3` at k ∈ U are those of the polynomial (`Filter.EventuallyEq.fderiv_eq`,
   `Filter.EventuallyEq.iteratedFDeriv`). Deliver
   `stationaryPhaseOn_kink (h : StationaryPhaseOnStatement) : ∃ C, ∀ A M m, ContDiff ℝ 2 A → tsupport A ⊆
   Metric.closedBall 0 2 → (∀ j ≤ 2, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M) → 1 ≤ m →
   ‖∫ k : ℝ × ℝ, Complex.exp (↑(m * (kinkPhase k + L₀ k)) * Complex.I) * A k‖ ≤ C * M / m`,
   and `foldOn_kink (h : FoldOnStatement)` with rate m^{−5/6}, plus `kinkPhase_not_contDiff : ¬ ContDiff ℝ 1 kinkPhase`
   (non-differentiable at (−3, 0)) and `kinkPhase_contDiffOn : ContDiffOn ℝ 4 kinkPhase {k | -3 < k.1}`.
   Use `hessianMatrix` via `OscInt.API.hessDet_eq_det` (C3, proved) or directly via `iteratedFDeriv_two_apply`;
   `FoldOrNondegMatrix` via `OscInt.API.foldOrNondeg_iff` (C7, proved). Critical: 4x³ + 4 + 4 = 0 ⇒ x ≠ 0 ⇒ det 24x² ≠ 0.
   Docstring: the sign `+ L` and the e₀/e₁ order are pinned (L₀ e₀ = 4 ≠ 0 = L₀ e₁; with `- L` the critical point is
   x = 0, degenerate); the phase is not C¹ on ℝ², so batch 2 does not apply without a hand-made cut-off.
6. Optional if time permits (report if skipped): `familyCkOfUncurry_nonconst (hC10 : FamilyCkOfUncurryStatement) :
   FamilyCk 4 (fun σ : Set.Icc (1 : ℝ) 2 => signFamily σ)` stated separately (it is used in 3 and 4).

## Report
Return: the final file contents verbatim, the compile command and its output (must be empty: no errors, no warnings
except unused-variable linters if unavoidable), and a list of each plant each theorem catches or does not catch.
Time box: if a theorem resists after a serious attempt, deliver the others and say exactly where it stopped.
