52188e41d659f6f281483efca2ff2589ca85dcfd

# Route referee report: batch VT (docs/proof-VT.md, Blueprint/Vector.lean, OscInt/Front/VectorAssembly.lean)

**Verdict:** no BLOCKER and no MAJOR. `VecTransferFacts` is true as stated, and the route derives it. Every Mathlib name in the route exists at the pin, and its signature fits the blueprint's instances. The assembly proves exactly the four frozen statements from the part and the proved scalar theorems, with no extra hypotheses. I wrote nothing in the repository (`git status --porcelain` is empty) and did not prove the part.

## What I checked
I ran three scratch files in /tmp/vtroute/, one Lean process at a time:
- **`names.lean`**: `#check @` on every route name, plus the helper lemmas the route uses without naming them.
- **`fit.lean`**: interface checks for each route step in the blueprint's own instance context: `E : Type`, `[NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]`, and the ℝ-structure from `complexToReal`. All of these elaborate with no errors:
  - the dual vector from `exists_dual_vector'' ℂ v` used as `E →L[ℂ] ℂ`;
  - `ℓ.integral_comp_comm hf` rewriting the blueprint's Bochner integral;
  - `rw [map_smul, smul_eq_mul]` turning `ℓ (exp(..) • A k)` into the scalar integrand `exp(..) * ℓ (A k)`;
  - `(ℓ.restrictScalars ℝ).contDiff.comp hA : ContDiff ℝ 2 (fun k => ℓ (A k))`, landing in the scalar statement's instances;
  - `(ℓ.restrictScalars ℝ).norm_iteratedFDeriv_comp_left` followed by `ContinuousLinearMap.norm_restrictScalars`, giving `‖D^j(ℓ∘A)‖ ≤ ‖ℓ‖ ‖D^j A‖`;
  - `tsupport_comp_subset (map_zero ℓ) A`.
- **`asm.lean`**: the body of the assembly under `import OscInt`, `import Blueprint`, `import Blueprint.Vector`, as lessons 20 asks. It compiles with no name clash.

I also ran `lake env lean OscInt/Front/VectorAssembly.lean`: exit 0, no output.

## (1) Is `VecTransferFacts` true, and does the route derive it?
It is true. The edge cases:
- **M negative:** the vector hypothesis `‖iteratedFDeriv ℝ 0 A k‖ = ‖A k‖ ≤ M` at any point of ℝ² forces `M ≥ 0`, so the case is vacuous.
- **E = 0:** v = 0. `exists_dual_vector''` holds for every x, including 0. Step 5 gives `0 ≤ B M` from the scalar hypothesis applied to ℓ∘A = 0, which is admissible because M ≥ 0. No special case is needed.
- **K empty:** A = 0, and the same reasoning applies.
- **θ discontinuous off U:** continuity of `f = e^{iθ} • A` is only needed at k ∈ tsupport A ⊆ K ⊆ U (`ContinuousOn.continuousAt` + `IsOpen.mem_nhds`). Elsewhere f is eventually 0 (`notMem_tsupport_iff_eventuallyEq`, then `ContinuousAt.congr`). So f is continuous everywhere, compactly supported and integrable, and the integral never takes its junk value.
- **B arbitrary:** B is used only through the scalar hypothesis applied to the one function ℓ∘A with the same M. No property of B is needed.

Signatures at the pin, with the hypothesis each step uses:
- `exists_dual_vector'' (𝕜) [RCLike 𝕜] (x : E) : ∃ g, ‖g‖ ≤ 1 ∧ g x = ↑‖x‖`. Used with 𝕜 = ℂ.
- `ContinuousLinearMap.integral_comp_comm (L : E →L[𝕜] Fₗ) : Integrable φ μ → ∫ L (φ x) = L (∫ φ)`. Needs `CompleteSpace E` and `CompleteSpace Fₗ`, both available. Its integrability hypothesis comes from step 1.
- `ContinuousLinearMap.norm_iteratedFDeriv_comp_left (L) : ContDiffAt 𝕜 N f x → ↑n ≤ N → ‖iteratedFDeriv 𝕜 n (L ∘ f) x‖ ≤ ‖L‖ * ‖…‖`.
- `ContinuousLinearMap.norm_restrictScalars`: the instances `NormedAlgebra ℝ ℂ` and `IsScalarTower ℝ ℂ E` resolve.
- `tsupport_comp_subset : g 0 = 0 → tsupport (g ∘ f) ⊆ tsupport f`.
- `notMem_tsupport_iff_eventuallyEq : x ∉ tsupport f ↔ f =ᶠ[𝓝 x] 0`.
- `Continuous.integrable_of_hasCompactSupport : Continuous f → HasCompactSupport f → Integrable f μ`.

## (2) Does the assembly prove exactly the frozen statements?
Yes.
- `gdcv_of`, `gdv_of`, `gdfv_of` and `gdnv_of` are declared with result types `GlobalDecayCritVecStatement`, `GlobalDecayVecStatement`, `GlobalFoldVecStatement` and `GlobalNondegVecStatement`. Their only hypothesis is `hT : VecTransferFacts` (confirmed by `#check`).
- They use the proved theorems `OscInt.API.globalDecayCrit`, `globalDecay`, `globalFold` and `globalNondeg` (`OscInt/Front/GlobalFinal.lean`, lines 28–40), not hypotheses.
- Each takes the constant from its scalar theorem before E is chosen, sets `θ = m(Ψ + L)` (continuity from `theta_cont`, which uses only `ContDiffOn ℝ 4 Ψ U`), and sets B = the scalar rate times C.
- `#print axioms` on all four gives only `[propext, Classical.choice, Quot.sound]`.
- The binder order matches the frozen statements: E comes after ∃ C, with one constant for every E.

## (3) Findings

### MINOR
- **M1. The route's claim about `MathlibNames.lean` is not true at HEAD.** docs/proof-VT.md says "those used are in `MathlibNames.lean`". The file has `exists_dual_vector''`, `integral_comp_comm` and `norm_restrictScalars`, but none of the following, which the route uses:
  - `ContinuousLinearMap.norm_iteratedFDeriv_comp_left`;
  - `tsupport_comp_subset`;
  - `notMem_tsupport_iff_eventuallyEq`;
  - `Continuous.integrable_of_hasCompactSupport`.

  The file lists `iteratedFDeriv_comp_left` and `norm_compContinuousMultilinearMap_le` instead (an alternative route through step 4). All the missing names exist, so this is a lessons 1/19 record gap, not a route error. Add the four, or correct the sentence.
- **M2. The assembly is not built by `make quick` or CI.** `OscInt/Front/VectorAssembly.lean` is imported by nothing (not `OscInt.API`, not `OscInt.lean`), and the Makefile does not mention it. "Compiles" is therefore the lead's manual check; I re-ran it and it holds. Batch LE had the same pattern at its route commit (240455c). Either state in the route that it becomes CI-checked only once a `VectorFinal` imports it, or import it now.
- **M3. Step 6 of CONTRIBUTING ("check every interface numerically") is not addressed.** For a pure duality transfer, a numerical check of the interface has nothing to measure. The route should say so in one line rather than stay silent.

### NIT
- **N1. Step 1 does not name its compact-support lemma.** Suggested: `HasCompactSupport.smul_left` with `HasCompactSupport A`, which comes from `IsCompact.of_isClosed_subset hK (isClosed_tsupport A) hs`; or `HasCompactSupport.intro`, which needs `R1Space` and holds for ℝ×ℝ. It also omits the assembly from pointwise continuity (`continuous_iff_continuousAt`, `ContinuousAt.congr`, `ContinuousOn.continuousAt` + `IsOpen.mem_nhds`).
- **N2. Step 4's "M ≥ 0 from the j = 0 bound" is unnecessary.** `‖ℓ‖ * ‖D^j A‖ ≤ ‖D^j A‖ ≤ M` follows from `mul_le_of_le_one_left (norm_nonneg _) h1` with no sign condition on M. Harmless either way.
- **N3. Step 5 does not name its lemma for `‖(‖v‖ : ℂ)‖ = ‖v‖`.** Use `Complex.norm_real` + `norm_norm`, or `Complex.norm_of_nonneg (norm_nonneg v)`.
- **N4. Universes.** The route says the part is "proved as a universe-polymorphic theorem", while the blueprint fixes `E : Type`. That is consistent (the polymorphic theorem specialises), but the part's brief should say that the delivered constant must be `VecTransferFacts` itself, or a theorem from which it follows by one application.

### Missing from the route
Nothing of substance beyond M1–M3 and N1–N4. Steps 1–5 form a complete proof outline, and all instance interfaces were confirmed by elaboration.
