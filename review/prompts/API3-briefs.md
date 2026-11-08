# Proof-agent briefs, front-end batch 3 (API3)

Common rules (all agents). Repository `/home/user/lean-oscillatory` (built; `export PATH=$HOME/.elan/bin:$PATH`).
Work only in `/tmp/<agent>/` and return the file verbatim; the lead integrates. Compile with
`nice -n 10 lake env lean -DautoImplicit=false FILE` from the repository root, one Lean process at a time. First line
`import OscInt`. Library rules (the guard rejects violations): no `sorry`, `admit`, `axiom`, `native_decide`,
`private`, `set_option` (except `set_option maxHeartbeats N in`), `open Lean`, `Lean.`, macros/elab/notation/attribute,
`#eval`; write numerals, never `⊤`, for smoothness indices (lessons 12); declarations ≤ ~60 lines, helpers in the
agent's `…Aux` namespace with docstrings. `#check` every Mathlib name with its signature before relying on it (lessons
1, 19). Do not weaken a target; if a target is false, report a counterexample. Route: `docs/proof-API3.md`.

## Agent P1 — C10 (namespace `OscInt.API.FamilyAux`)
Target (exact):
```lean
theorem OscInt.API.familyCk_of_uncurry : OscInt.Statements.FamilyCkOfUncurryStatement
```
Route P1 in `docs/proof-API3.md`. Helper to export (used by P2): 
```lean
theorem OscInt.API.FamilyAux.iteratedFDeriv_slice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {f : E × (ℝ × ℝ) → ℝ} (hf : ContDiff ℝ n f) (σ : E) (k : ℝ × ℝ) {j : ℕ} (hj : j ≤ n) :
    iteratedFDeriv ℝ j (fun k' => f (σ, k')) k =
      (iteratedFDeriv ℝ j f (σ, k)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ E (ℝ × ℝ))
```
Names checked at the pin: `iteratedFDeriv_comp_add_left`, `ContinuousLinearMap.iteratedFDeriv_comp_right`,
`ContDiff.continuous_iteratedFDeriv`, `ContinuousMultilinearMap.compContinuousLinearMapL`,
`ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear`.

## Agent P2 — cut-off (namespace `OscInt.API.CutoffAux`)
Targets (exact):
```lean
theorem OscInt.API.CutoffAux.exists_cutoff {K U : Set (ℝ × ℝ)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : ℝ × ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n χ) ∧ tsupport χ ⊆ U ∧ ∃ W : Set (ℝ × ℝ), IsOpen W ∧ K ⊆ W ∧ ∀ k ∈ W, χ k = 1

theorem OscInt.API.CutoffAux.familyCk_cutoff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {Ψ : E → ℝ × ℝ → ℝ} {S V : Set E} {U : Set (ℝ × ℝ)} {χ : ℝ × ℝ → ℝ}
    (hV : IsOpen V) (hU : IsOpen U) (hSV : S ⊆ V) (hΨ : ContDiffOn ℝ n (Function.uncurry Ψ) (V ×ˢ U))
    (hχ : ContDiff ℝ n χ) (hχU : tsupport χ ⊆ U) :
    OscInt.Statements.FamilyCk n (fun σ : S => fun k => χ k * Ψ σ k)

theorem OscInt.API.CutoffAux.cutoff_eventuallyEq {Ψ : ℝ × ℝ → ℝ} {χ : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hχ : ∀ k ∈ W, χ k = 1) {k : ℝ × ℝ} (hk : k ∈ W) :
    (fun k => χ k * Ψ k) =ᶠ[nhds k] Ψ
```
Route P2 in `docs/proof-API3.md`. Names checked at the pin: `IsCompact.exists_cthickening_subset_open`,
`exists_contDiff_support_eq_eq_one_iff` (in `Mathlib/Geometry/Manifold/PartitionOfUnity.lean`; it needs
`FiniteDimensional ℝ (ℝ × ℝ)`), `Filter.EventuallyEq.iteratedFDeriv`, `ContDiffAt.iteratedFDeriv_right`. The closure
lemma for thickenings is NOT `closure_thickening_subset_cthickening` at the pin: find the namespaced name. For
`familyCk_cutoff`: at `(σ, k)` with `k ∈ U`, use that `(σ', k') ↦ χ k' * Ψ σ' k'` is `ContDiffAt` at `(σ, k)` (open
product); to get the slice identity of P1 locally, do NOT use a cut-off in `σ'`: `E` is an arbitrary real normed
space and may be infinite-dimensional, where smooth bumps need not exist. Use instead that `iteratedFDeriv` depends
only on germs, together with a local (within / on an open set) version of the composition identity, e.g. via
`iteratedFDerivWithin` on the open set `V ×ˢ U` (`iteratedFDerivWithin_of_isOpen`) and the `…Within` composition
lemmas, or an induction on `j` using `fderiv` of the slice; `#check` what exists. At
`k ∉ U`, the function vanishes on `univ ×ˢ (tsupport χ)ᶜ`. Report any step whose cost exceeds the time box.
