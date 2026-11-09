76cdff1d5f5127df2671af0c0f5d38d825a662eb

# Referee B: blind pre-proof review of batch VT (GD-C-V, GD-V, GD-F-V, GD-N-V)

I wrote nothing in the repository; `git status` is clean. My scratch files are in /tmp/vtrefB/. I did not prove any statement under review. My Lean checks covered only: how the statements elaborate (`#print` with `pp.explicit`), the signatures of the Mathlib lemmas the route needs, whether the needed instances exist and agree, whether a user can apply the frozen hypothesis to new kinds of E, and one extra planted control. I did not open `.claude/worktrees/`.

## Summary

| Statement | Verdict vs docs | True? | Derivable from the proved scalar statement by duality |
|---|---|---|---|
| GD-C-V `GlobalDecayCritVecStatement` | FAITHFUL | TRUE | yes |
| GD-V `GlobalDecayVecStatement` | FAITHFUL | TRUE | yes |
| GD-F-V `GlobalFoldVecStatement` | FAITHFUL | TRUE | yes |
| GD-N-V `GlobalNondegVecStatement` | FAITHFUL | TRUE | yes |

There are no BLOCKER or MAJOR findings. Two MINOR findings concern what the sanity file covers, not the statements themselves.

## 1. Fidelity and truth

**Same text as the scalar statements.** I compared each vector body with its scalar body (`OscInt/Statements/Global.lean`) after two replacements:
- `∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (A : ℝ × ℝ → E)` becomes `∀ (A : ℝ × ℝ → ℂ)`;
- `) • A k` becomes `) * A k`.

All four bodies are then character-for-character identical to GD-C, GD, GD-F and GD-N. So the hypotheses on Ψ, K, U, D and K′, the rates m^{-2/3}, m^{-2/3}, m^{-5/6} and m^{-1}, and the placement of `L ∈ K'` are unchanged.

**Order of quantifiers.** In `∃ C : ℝ, ∀ (E : Type) [..] ...`, C is chosen after the phase data and before E. This is exactly what `docs/statements.md` says ("one constant C, chosen after the phase data and before E, valid for every E"). The whole expression is still a `Prop`, because Prop is impredicative.

**It is true, with one C for every E.** The duality route gives every E the scalar constant C, and nothing in it depends on E. The Hahn–Banach functional has ‖ℓ‖ ≤ 1 in every dimension, including infinite dimension.

**Instances, checked with `pp.explicit`:**
- `ContDiff ℝ 2 A`, `iteratedFDeriv ℝ j A` and the Bochner integral `MeasureTheory.integral` all use `@NormedSpace.complexToReal E _ inst_1`.
- `•` is the ℂ-action obtained from `NormedSpace.toModule Complex E`.
- `complexToReal` keeps E's norm. So `‖iteratedFDeriv ℝ j A k‖` is the natural operator norm of a `ContinuousMultilinearMap ℝ (Fin j) (ℝ × ℝ) E`, with the max norm on ℝ × ℝ as in the scalar case.
- At `with_reducible_and_instances rfl`, the default instances `NormedSpace ℝ ℂ` and `NormedSpace ℝ (Fin 2 → Fin 2 → ℂ)` are equal to `NormedSpace.complexToReal`. So a user's own `ContDiff ℝ 2 A` hypothesis unifies with the one in the statement.

**`E : Type` (universe 0).** This matches modelling choice 1 in the docs. `ULift.normedSpace` exists, and `CompleteSpace (ULift.{0} E)` is found for `E : Type 1`. So users in higher universes have an escape route, although it is not free (see N2).

## 2. Derivability by duality

Every step of the route in the docs exists at the pinned Mathlib, with the signatures it needs:

- **Hahn–Banach.** `exists_dual_vector'' (𝕜) [RCLike 𝕜] [NormedSpace 𝕜 E] (x) : ∃ g, ‖g‖ ≤ 1 ∧ g x = ↑‖x‖`. Use 𝕜 = ℂ.
- **Moving ℓ inside the integral.** `ContinuousLinearMap.integral_comp_comm` takes separate `[NormedSpace 𝕜 E]` and `[NormedSpace ℝ E]` with no compatibility assumption. That is correct mathematically: a continuous additive map is automatically ℝ-linear. So the `complexToReal` structure creates no diamond.
- **Its integrability hypothesis.** It holds even though Ψ is arbitrary, possibly non-measurable, off U. Let f(k) = e^{im(Ψ+L)(k)} • A(k).
  - At k ∈ U, Ψ is continuous at k because U is open and Ψ is `ContDiffOn` U, so f is continuous at k.
  - At k ∉ U, k lies outside the closed set `tsupport A ⊆ K ⊆ U`, so f vanishes on a neighbourhood of k.
  - So f is continuous with compact support, and `Continuous.integrable_of_hasCompactSupport` applies. Measurability never fails, and the junk value 0 of the Bochner integral cannot occur.
- **ℓ ∘ A is a scalar amplitude.**
  - `ContinuousLinearMap.restrictScalars ℝ ℓ : E →L[ℝ] ℂ` elaborates over `complexToReal`, and `ContinuousLinearMap.norm_restrictScalars ℓ` typechecks, giving ‖ℓ_ℝ‖ = ‖ℓ‖ ≤ 1.
  - `ContinuousLinearMap.norm_iteratedFDeriv_comp_left` gives ‖D^j(ℓ ∘ A)‖ ≤ ‖ℓ‖ ‖D^j A‖ ≤ M.
  - `tsupport_comp_subset` (using ℓ 0 = 0) gives tsupport(ℓ ∘ A) ⊆ K.
  - `map_smul` and `smul_eq_mul` turn the integrand into e^{…} · ℓ(A k).
  - Finally ‖v‖ = ‖ℓ v‖ ≤ C M r(m).
- **E = 0.** Nothing fails. The functional g = 0 works. The hypotheses force M ≥ 0 (take the j = 0 bound at any point). The scalar C is forced to be ≥ 0 (scalar statement at A = 0, M = 1). So 0 ≤ C M r(m). `NormedSpace ℂ PUnit` and `CompleteSpace PUnit` both synthesise.
- **The scalar statements are proved:** `OscInt/Front/GlobalFinal.lean` lines 28–40 (`globalDecayCrit`, `globalDecay`, `globalFold`, `globalNondeg`).

A consequence: the vector statements are mathematically equivalent to their scalar counterparts. Vector implies scalar by taking E = ℂ (the sanity file); scalar implies vector by duality.

## 3. Vacuity and usefulness

- **E = ℂ gives the scalar statement exactly.** `globalDecayCrit_of_vec` and the three similar theorems derive each frozen scalar statement from its vector one using only `simpa [smul_eq_mul]`. Together with the textual comparison and the instance check in §1, the E = ℂ instance is the scalar statement, with nothing weakened. The statements are not vacuous.
- **Matrix-valued amplitudes are usable.** Three cases elaborate in my scratch, each applying a hypothesis `h : GlobalNondegVecStatement` to arbitrary Ψ, K, U:
  1. `Fin 2 → Fin 2 → ℂ` with the sup norm (also in the sanity file);
  2. `Matrix (Fin 2) (Fin 2) ℂ` under `attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace`, via `exact ⟨C, fun A => hC (Matrix (Fin 2) (Fin 2) ℂ) A⟩`;
  3. operator-valued `(Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)`, which has global instances and the operator norm.

  The missing global norm instance on `Matrix` is therefore a convenience issue only (N1).
- **The uniform form is the more useful one.** Uniformity of C in E matters to a consumer who needs a single constant across a family of spaces, for example ℂⁿ for every n, or ℓ²-valued symbols. The `∀ E, ∃ C` form would not give that without the duality lemma.

## 4. Sanity theorems and planted controls

**The record on the 'C after E' plant is right.** `plant-GDN-V-C-after-E-BLINDSPOT` is rejected only because `obtain ⟨C, hC⟩ := h Ψ … hcl` appears before E is supplied. Reordering the proof to `obtain ⟨C, hC⟩ := h … (Fin 2 → Fin 2 → ℂ)` would make it compile. Every sanity datum is a single fixed E, and for a single E the plant gives the conclusion cheaply. So the detection is brittleness, as the record says.

**It does not matter much for truth.** As shown in §2, the `∀ E ∃ C` variant implies the scalar statement (take E = ℂ), which implies the uniform version by duality. So it is not a mathematical weakening of the true statement. For weakenings of true statements, plants can only separate "cheaply derivable" from "not cheaply derivable"; semantic detection is impossible in principle. The uniform form remains the right choice for usefulness (§3).

**A blind spot the record does not list: every sanity datum is finite-dimensional** (ℂ, `Fin 2 → Fin 2 → ℂ`, ℂ × ℂ). I compiled a planted copy of GD-N-V with `[CompleteSpace E] [FiniteDimensional ℂ E]` against both `P_globalNondeg_matrix` and `P_globalNondeg_of_vec`. It is **accepted** (exit 0, no errors; /tmp/vtrefB/plantFD.lean). `[ProperSpace E]`, or any other class satisfied by finite-dimensional spaces, would pass in the same way. The plant registered as "findim" actually adds `[Subsingleton E]` (see `plants_vt.py.txt` line 39), which is a much easier plant to catch.

## 5. Findings

**MINOR-1 (sanity coverage).** No sanity datum is infinite-dimensional, so a plant adding `[FiniteDimensional ℂ E]` after `[CompleteSpace E]` in
`∃ C : ℝ, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]`
is accepted by `OscInt/Front/VectorSanity.lean` (verified). Infinite-dimensional Banach-valued amplitudes are the stated purpose of the batch ("ℓ²-type spaces and spaces of bounded operators on them"). Suggested fix: add a datum `E := ℕ →ᵇ ℂ` (`open scoped BoundedContinuousFunction`; I checked that `NormedAddCommGroup`, `NormedSpace ℂ` and `CompleteSpace` all synthesise) or an `lp` space, and add the FiniteDimensional plant to the record. This needs no re-freeze.

**MINOR-2 (sanity coverage of uniformity).** Every sanity theorem fixes one E, so the 'C after E' plant is separated only by tactic order. A sanity conclusion that quantifies C over a family, for example
`∃ C, ∀ n (A : ℝ × ℝ → EuclideanSpace ℂ (Fin n)) …`,
would not follow cheaply from the plant under any tactic order. That would make the control principled rather than brittle. Low priority, given the equivalence argued in §4.

**NIT-1 (usability).** `Matrix` has no global norm instance. A user needs `attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace` (or the Frobenius instances), or the defeq type `Fin 2 → Fin 2 → ℂ` with the entrywise sup norm, or `(Fin n → ℂ) →L[ℂ] (Fin n → ℂ)` for the operator norm. All three elaborate against the frozen statement. A one-line consumer note in the docs would help. Norm changes on finite-dimensional spaces only change the constant.

**NIT-2.** `E : Type` excludes higher universes. `ULift` has the instances, but moving `ContDiff`, `iteratedFDeriv` and the integral across `ULift.up` is user work. This is documented as modelling choice 1, so I mention it only.

**NIT-3.** Real Banach spaces are not covered (documented as modelling choice 3, "complexify"). Mathlib has no convenient complexification, so for a user this is a real limitation, though not a fidelity defect.

**NIT-4 (record).** The plant name `GDN-V-findim` does not match its mutation, `'[CompleteSpace E] [Subsingleton E]'`. The name suggests a finite-dimensionality plant was run when it was not. Rename it, or add the real FiniteDimensional plant (MINOR-1).

**Scratch files** (in /tmp/vtrefB/): c1.lean (explicit elaboration and lemma signatures), c2.lean (Matrix and operator usability, instance agreement, E = 0 instances), c3.lean (restrictScalars and route lemma signatures), c4.lean (`ℕ →ᵇ ℂ` instances), plantFD.lean (the FiniteDimensional plant, accepted).
