76cdff1 (output of `git rev-parse HEAD`; HEAD is "VT pre-proof referee prompt")

# Referee A: blind pre-proof statement review, batch VT (GD-C-V, GD-V, GD-F-V, GD-N-V)

**Summary.** All four statements are FAITHFUL to `docs/statements.md` "Batch VT" and TRUE. Each follows from its proved scalar statement by the duality route, with the same constant. I found no BLOCKER and no MAJOR issue: 3 MINOR findings and 3 NITs.

I did not prove any statement under review, in the repository or in scratch. All my Lean checks were elaboration, instance, signature or `#print axioms` checks, in `/tmp/vtrefA/check{1,2,3,4}.lean`. Nothing was written in the repository.

## What I checked

- **Textual identity with the scalar statements (scripted).** In each Vec statement I replaced `∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]\n      (A : ℝ × ℝ → E)` with `∀ (A : ℝ × ℝ → ℂ)` and `) • A k` with `) * A k`. The resulting `def` body is character for character the body of GlobalDecayCrit/GlobalDecay/GlobalFold/GlobalNondegStatement in `OscInt/Statements/Global.lean` (all 4 True). So the hypotheses on Ψ, K, U, D and K′, the rates and the position of `∃ C` (after the phase data) are exactly the scalar ones. The only additions are the E binder and `•`.
- **Real structure of E.** With `pp.explicit`, `#print GlobalNondegVecStatement` shows that `ContDiff ℝ 2 A`, `iteratedFDeriv ℝ j A` and its norm use `@NormedSpace.complexToReal E _ inst_1`. That is the only real structure available, so there is no free real structure.
  - The norm of `iteratedFDeriv` is the ordinary operator norm of a `ContinuousMultilinearMap ℝ (fun _ => ℝ × ℝ) E`, with the max norm on ℝ² and E's own norm. That is the natural choice.
  - For `E = Fin n → ℂ` with the sup norm, this norm equals the maximum over components, so M is the entrywise bound.
  - `complexToReal` agrees with the instance found directly on `ℂ`, `ℂ × ℂ` and `Fin 2 → Fin 2 → ℂ`, by `with_reducible_and_instances rfl` (check2). So hypotheses a user writes for those spaces unify with the statement.
- **Constant before E.** `∀ E : Type, …` inside a `Prop` after `∃ C` is well formed (Prop is impredicative). It says what the docs say: "one constant C, chosen after the phase data and before E, valid for every E". It is true, because the duality argument returns the scalar constant itself, independent of E.
- **E = ℂ gives the scalar statement exactly.** This is confirmed both by the textual identity above and by the compiled `globalX_of_vec` theorems (`simpa [smul_eq_mul]`). The scalar theorems are proved: `#print axioms OscInt.API.globalNondeg` gives only `[propext, Classical.choice, Quot.sound]`.

## 1. Verdicts

| Constant | Verdict | True? |
|---|---|---|
| `GlobalDecayCritVecStatement` (GD-C-V) | FAITHFUL | TRUE, given GD-C (proved) |
| `GlobalDecayVecStatement` (GD-V) | FAITHFUL | TRUE, given GD |
| `GlobalFoldVecStatement` (GD-F-V) | FAITHFUL | TRUE, given GD-F |
| `GlobalNondegVecStatement` (GD-N-V) | FAITHFUL | TRUE, given GD-N |

- The universe restriction `E : Type` is stated in the docs (modelling choice 1), so it does not make the statements weaker than documented.
- `•` is the ℂ-action and `∫` is Bochner's integral in E, as documented.

## 2. Derivability by the duality route

Every step exists at the pin with the signature the route needs (checked by `#check` / `#synth`):

1. **Norming functional.** `exists_dual_vector'' ℂ v : ∃ g, ‖g‖ ≤ 1 ∧ g v = ↑‖v‖` works for any seminormed E, including E = 0.
   - E = 0 needs no case split: ‖v‖ = ‖g v‖ ≤ (scalar bound applied to g ∘ A).
   - C ≥ 0 is therefore not needed either.
2. **Integrability.** `ContinuousLinearMap.integral_comp_comm (L : E →L[𝕜] Fₗ) : Integrable φ μ → ∫ L (φ x) = L (∫ φ)`, with 𝕜 = ℂ and `[NormedSpace ℝ E]` supplied by `complexToReal`. This needs `k ↦ e^{im(Ψ+L)(k)} • A(k)` to be integrable, which holds even though Ψ is smooth only on U:
   - At a point outside `tsupport A`, A vanishes on a neighbourhood, so the integrand is 0 there.
   - At a point of `tsupport A ⊆ K ⊆ U`, Ψ is continuous (U is open and `ContDiffOn` gives `ContinuousAt`), and A is continuous.
   - So the integrand is continuous everywhere, with compact support (it lies inside K), whatever Ψ does off U, measurable or not.
   - `Continuous.integrable_of_hasCompactSupport` then applies. Its instances (`Prod.opensMeasurableSpace`, `instIsFiniteMeasureOnCompactsProdVolume`) are found.
   - So the Bochner junk value 0 never occurs.
3. **Commuting ℓ with the phase.** `ℓ (c • A k) = c * ℓ (A k)` holds by ℂ-linearity (`map_smul`).
4. **ℓ ∘ A is a scalar amplitude (2, K, M).**
   - Support: `tsupport_comp_subset (g 0 = 0)`.
   - Smoothness: `ℓ.restrictScalars ℝ` composed with a `ContDiff` map.
   - Derivative bound: `ContinuousLinearMap.norm_iteratedFDeriv_comp_left`, applied to `ℓ.restrictScalars ℝ`, gives `‖iteratedFDeriv ℝ j (ℓ ∘ A) k‖ ≤ ‖ℓ.restrictScalars ℝ‖ · M`.
   - `ContinuousLinearMap.norm_restrictScalars` gives `‖ℓ.restrictScalars ℝ‖ = ‖ℓ‖ ≤ 1`. Its `IsScalarTower ℝ ℂ E` instance is `IsScalarTower.complexToReal`, found by search. I checked the elaboration on a generic E.

No step fails. The scalar constant works for every E, so each Vec statement is equivalent to its scalar statement: Vec ⇒ scalar at E = ℂ, and scalar ⇒ Vec by duality.

## 3. Vacuity and usefulness

- **E = ℂ.** It gives the scalar statement exactly (above). It is non-vacuous because the scalar statements are, and the sanity file gives nonzero data on ℂ², matrices, a fold and an umbilic.
- **Matrices.** GD-N-V applies to `Fin 2 → Fin 2 → ℂ` with the entrywise sup norm, as in the sanity file. For the type `Matrix (Fin 2) (Fin 2) ℂ`:
  - `#synth NormedAddCommGroup` fails with no extra setup, as the brief expected.
  - With `attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace`, or with `open scoped Matrix.Norms.L2Operator`, all three instances are found (`CompleteSpace` is `Matrix.instCompleteSpace`).
  - In both settings, a hypothesis of the frozen shape applies to a user's `A : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ` whose `ContDiff` and `iteratedFDeriv` hypotheses were written at the user's site, with no instance mismatch (check3).
  - So this is only a usability note: one line of setup, plus a free choice of operator norm, which the E-uniform constant allows.
- **Higher universes.** A space `E : Type 1` is rejected, as expected (check2). See MINOR-1.

## 4. Sanity theorems and planted controls

- **What the sanity file can detect.** It only proves "Vec ⇒ scalar" (at E = ℂ) and three single-E instances. So it detects:
  - a strengthened hypothesis, including on the E binder (`[Subsingleton E]` is caught at E = ℂ and by the matrix datum; an `InnerProductSpace` plant would be caught by the matrix and ℂ² data);
  - a textual change in the conclusion, through `simpa` matching.
- **What it misses.**
  - A weakened hypothesis on Ψ or A, e.g. dropping `tsupport A ⊆ K`, which would make the statement false. This structural limit is acknowledged in the file.
  - Dropping `[CompleteSpace E]`. This is harmless: for incomplete E the Bochner integral is 0 and the statement stays true.
  - Any statement on uniformity in E.
- **The 'C after E' plant.** The record is right that it was rejected by brittleness:
  - `obtain ⟨C, hC⟩ := h …` cannot destructure `∀ E, ∃ C, …`.
  - The planted form still implies every sanity conclusion, since each uses only one E. Rewritten proofs would accept it.
- **Does it matter? No.** The planted form `∀ E, ∃ C` implies the scalar statement (take E = ℂ), and the scalar statement implies `∃ C, ∀ E` by §2. So the two placements are logically equivalent, through a short elementary argument, and not just because both are theorems. Calling it a "weakening" is formally right but semantically empty. No user loses anything if the reviews miss the C placement.

## 5. Findings

**MINOR-1. Universe restriction.** The binder `∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]` cannot be applied to a Banach space in `Type u` for u > 0 (check2). It is documented (modelling choice 1) and does not affect faithfulness. Suggestion: also expose the generic duality transfer as an ordinary universe-polymorphic theorem (not a frozen statement), e.g. "scalar bound for all amplitudes (2, K, M) ⇒ the same bound for E-valued ones, E : Type u". Users in higher universes would then not need to redo the argument.

**MINOR-2. The plant record overstates the blind spot.** `docs/replay/2026-11-08-VT-sanity-plants.txt` says "the uniformity of C in E rests on the blind reviews". Given §4, the uniformity is equivalent to the E = ℂ case plus duality. Suggestion: record the plant as formally weaker but provably equivalent, so the brittleness-only rejection has no consequence. If a semantic test is still wanted, a sanity corollary that uses one C for two different spaces at once (ℂ and ℂ × ℂ) would reject the plant by type and not by script shape.

**MINOR-3. Matrices need a local instance.** The module docstring says matrices "live there", but `Matrix (Fin n) (Fin n) ℂ` has no global norm instance. The sanity theorem uses `Fin 2 → Fin 2 → ℂ` instead. Suggestion: add a snippet to `examples/api/Snippets.lean` showing `attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace` (or `open scoped Matrix.Norms.L2Operator`) with GD-N-V; I checked that this elaborates. Also say that the E-uniform constant lets the user pick any norm.

**NIT-1. One-line reason for integrability.** The VT route paragraph in `docs/statements.md` says "the integrand is continuous with compact support". It would help to add the reason, since Ψ is only `ContDiffOn ℝ 4 Ψ U`: continuity at points outside `tsupport A` comes from A vanishing nearby, and inside it from `tsupport A ⊆ K ⊆ U` with U open.

**NIT-2. GD-C-V has only the E = ℂ sanity theorem.** It has no instance with E ≠ ℂ, unlike GD-V, GD-F-V and GD-N-V. Given the textual identity this is low risk, but an instance with E = ℂ × ℂ and a `K′` distinct from `K` (lessons 17) would complete the pattern.

**NIT-3. Docs wording.** "with one constant C, chosen after the phase data and before E" matches the Lean text exactly. It could add "(equivalently, by duality, the scalar constant)" to signal that the E-uniformity costs nothing.

## Files

- Reviewed: `/home/user/lean-oscillatory/OscInt/Statements/Vector.lean`, `/home/user/lean-oscillatory/OscInt/Statements/Global.lean`, `/home/user/lean-oscillatory/OscInt/Front/VectorSanity.lean`, `/home/user/lean-oscillatory/docs/replay/2026-11-08-VT-sanity-plants.txt` and `/home/user/lean-oscillatory/docs/replay/plants/2026-11-08-VT/`, `/home/user/lean-oscillatory/docs/statements.md` (GD and VT sections), `/home/user/lean-oscillatory/docs/design/vector-amplitudes.md`, `/home/user/lean-oscillatory/docs/lessons.md` (11, 12, 17, 24, 33).
- My scratch checks: `/tmp/vtrefA/check1.lean`, `/tmp/vtrefA/check2.lean`, `/tmp/vtrefA/check3.lean`, `/tmp/vtrefA/check4.lean`.
