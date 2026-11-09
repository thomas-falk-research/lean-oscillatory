09e4bc72c1a931cb5563e70b22f403373cb00d92

# Post-proof referee B: batch VT (GD-C-V, GD-V, GD-F-V, GD-N-V)

**Verdict: FAITHFUL on all four theorems, at full scope.** No BLOCKER and no MAJOR. One MINOR: a false claim in the sanity documentation, refuted by a compiled counter-proof. Three NITs.

I wrote nothing in the repository (`git status --porcelain` is empty). I did not run `make` or `lake build`, and ran one Lean process at a time under `nice -n 10`. My scratch files are in /tmp/vtpostB/: check.lean, deps.lean, nonvac.lean, plant.lean, lp.lean.

## (1) Is each theorem's type exactly the frozen constant?
Yes, for all four.

- **Frozen files unchanged.** These files have the same SHA-256 at HEAD as in `stamps/20261108T235416Z-961cebc296ef/manifest.txt` (manifest commit 961cebc):
  - `OscInt/Statements/Vector.lean`: 784ca9a5…c2ba
  - `Challenge/Vector.lean`: 5b0ec1be…f823
  - `comparator-VT.json`: 4e312bec…60b1
  - `OscInt/Statements/Global.lean`
- **Stamp tokens.** All three RFC 3161 tokens in each stamp carry the SHA-256 of their manifest:
  - first stamp: imprint 207c72bc…, 23:54:21Z;
  - second stamp: imprint a7087ff2…, 00:24:23Z.

  I checked only that the hashes match (`openssl ts -reply -text`). I did not check the signature chains; the replay's stamp-verify step covers those.
- **Commitments.** The manifest has a commitment line for each of the four `*VecStatement` constants. They match `stamps/statements.json` and the replay's "commit: … matches its stamp" lines (replay lines 296, 333–348).
- **StatementTypes.lean.** It has four new `#assert_type_is` lines. The replay record, made on d261c19, shows TYPE-OK for all four (lines 126–129). The only difference between d261c19 and HEAD is the replay record and two prompt files.
- **My own check.** In `check.lean`, `example : XVecStatement := OscInt.API.x` elaborates for all four. `#print axioms` gives only `[propext, Classical.choice, Quot.sound]`.
- **Recompiled from source** (`lake env lean`), each with exit 0 and no output: VectorParts, VectorAssembly, VectorFinal, VectorSanity, Statements/Vector, Blueprint/Vector and examples/consumer/ConsumerVector.lean.
- **Replay record.** The comparator accepted `comparator-VT.json` against the VT stamp under six kernels (replay lines 615–638). The challenge export hash matches the stamped one.

## (2) Fidelity to `docs/statements.md` "Batch VT" (with clarifications 4–7)
- **Same hypotheses as the scalar statements.** I compared each statement with its counterpart in `OscInt/Statements/Global.lean` (lines 61–98). They are the same text apart from three changes:
  - the `∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]` binder;
  - `A : ℝ × ℝ → E`;
  - `*` replaced by `•`.

  The hypotheses on Ψ, K, U, D and K′ and the rates (m^{-2/3}, m^{-2/3}, m^{-5/6}, `C * M / m`) are identical.
- **One constant for every E.** `∃ C` comes after the phase data and before `∀ E`, as the docs require.
- **Modelling choices.**
  - Choice 1 (`E : Type`) and choice 3 (no real Banach spaces) are stated limitations, not defects.
  - Clarification 7 promised a universe-polymorphic transfer theorem. It exists as `OscInt.VectorAux.transfer` (`E : Type u`), and `VectorFinal.lean` points users to it.
  - Choice 2 (the scalar statements are the case E = ℂ) holds. `globalNondeg_of_vec` and its siblings compile. I also compiled `GlobalNondegVecStatement ↔ GlobalNondegStatement`, using `globalNondeg_of_vec` in one direction and `globalNondegVec` in the other.
- **Verdicts.**
  - GD-C-V: FAITHFUL, full scope.
  - GD-V: FAITHFUL, full scope.
  - GD-F-V: FAITHFUL, full scope.
  - GD-N-V: FAITHFUL, full scope.

## (3) Non-vacuity on compiled data
- **Phase hypotheses.** The sanity theorems discharge them on concrete data, and `ConsumerVector.lean` applies the proved theorems, using only `import OscInt.API`. The data:
  - matrix-valued amplitudes, `Fin 2 → Fin 2 → ℂ`, on x²+3xy+5y² (GD-N-V);
  - `ℂ × ℂ` with the fold (GD-F-V);
  - `ℂ × ℂ` with the elliptic umbilic (GD-V);
  - `ℂ × ℂ` with K′ = {0, L₁} (GD-C-V);
  - the infinite-dimensional space `ℕ →ᵇ ℂ` (GD-N-V);
  - one constant for all `EuclideanSpace ℂ (Fin n)` (GD-N-V).
- **The amplitude quantifier is not empty either.** In `nonvac.lean` (axioms clean) I proved that, for any E and any v ≠ 0, a `ContDiffBump`-based amplitude A with A 0 = v satisfies every amplitude hypothesis on `closedBall 0 1`. Combined with `globalNondeg_matrix globalNondegVec`, this gives a concrete nonzero matrix-valued amplitude with a finite bound of order C·M/m.

## (4) Does the proof rest only on batch GD and Mathlib?
Yes.

- **Dependency trace** (`deps.lean`). I walked the OscInt constants reachable from the four theorems, stopping at the scalar theorems. The only proof dependencies are:
  - `OscInt.API.globalDecayCrit`, `globalDecay`, `globalFold`, `globalNondeg` (the batch-GD scalar theorems, whose axioms are clean);
  - `OscInt.VectorAux.{transfer, vecTransfer, integrand_continuous, theta_cont, gd*v_of}`;
  - `OscInt.Blueprint.VecTransferFacts`.

  Everything else reached is a statement definition (`Classified`, `ClassifiedCrit`, `IsD4Point`, `hessianMatrix`, `FoldOrNondegMatrix`, …).
- **The proof itself** (`VectorParts.lean`) is the documented duality argument:
  - Hahn–Banach (`exists_dual_vector''`) gives a norming functional;
  - `integral_comp_comm` applies to the continuous, compactly supported integrand;
  - `norm_iteratedFDeriv_comp_left` applies to the functional restricted to ℝ-scalars.
- **Integrability (clarification 4).** It is proved (`integrand_continuous`, `HasCompactSupport.intro`). The junk value of the Bochner integral never enters.

## (5) Claims in the docs against the evidence (order)
- **Statements and challenge before the reviews.** They were committed at 961cebc (23:44) and stamped at 23:54:21Z. The pre-proof prompt was committed at 76cdff1, before the referees ran, and both reports carry 76cdff1 as their first line.
- **Reviews before any proof.** The reports and answers were committed at 4550529 and stamped at 00:24:23Z. That manifest contains no VectorParts, VectorAssembly or VectorFinal, and no transfer proof existed in the tree at 961cebc or 4550529 (only `#check` lines in MathlibNames.lean).
- **Sanity theorems added after the first stamp.** VectorSanity.lean changed after the first stamp: three theorems were added in 4550529 in answer to the reviews. That version is covered by the second stamp; its hash matches.
- **Route review before the part's proof entered the repository.** This holds by git ancestry: route at 52188e4, then route referee report and revision at c24d0ea, then part at d261c19. The docs word this claim correctly: they say "entered the repository", not "was proved".

## Findings

### MINOR
**MINOR-1. The sanity docstring makes a false claim, and the plant record repeats it.**

- **Where.**
  - `OscInt/Front/VectorSanity.lean` lines 91–93, the docstring of `globalNondeg_uniform_dim`: "A planted statement with `C` chosen after `E` gives a constant for each `n` separately, and no maximum over infinitely many; it implies this conclusion only through the duality argument, not by instantiation".
  - `docs/replay/2026-11-08-VT-sanity-plants.txt` lines 14–16 say the same: "a reordered proof cannot succeed either … without the duality argument".
- **Why it is false.** One instantiation of the plant at `E = lp (fun n : ℕ => EuclideanSpace ℂ (Fin n)) ∞` gives a single constant. Each ℂⁿ embeds into that space by a linear isometry (`lp.single`). The isometry preserves the derivative bounds (`LinearIsometry.norm_iteratedFDeriv_comp_left`), the support and the norm of the integral (`LinearIsometry.integral_comp_comm`).
- **Compiled counter-proof.** `/tmp/vtpostB/plant.lean`, theorem `uniform_of_plant`, axioms `[propext, Classical.choice, Quot.sound]`. It derives the exact conclusion of `globalNondeg_uniform_dim` from the 'C after E' plant restricted to the quadratic datum. The full run-2 plant `P_GlobalNondegVecStatement` implies that restricted form trivially.
- **Effect.** The run-2 rejection of the 'C after E' plant is still only by tactic shape (the `rcases` failure). It is not semantic detection.
- **No effect on the theorems.** 'C after E' and 'C before E' are equivalent anyway (clarification 5), and the frozen statement has the stronger placement.
- **Fix.** Correct the docstring and the plant record. A semantic test of the binder order is not possible here, because the two placements are provably equivalent.

### NIT
- **NIT-1. The order evidence after the second stamp is git order and self-reported times only.**
  - The assembly (52188e4) is Lean proof code that reduces VT to the part. It entered 33 s after the stamp commit.
  - The route referee report and the route revision (c24d0ea) were committed 3 min 24 s after the route commit.
  - The lead's draft of the part existed in the scratchpad during the route review. Lessons 42 permits this, and the docs disclose it.
  - So the step-6 wording in `VectorAssembly.lean` ("Compiled before the part was proved") is supported only in the sense "committed before the part's proof was committed". No RFC 3161 stamp covers the route, the route review or the part's order. Git ancestry is the only evidence, and it supports exactly the claim the docs make.
- **NIT-2. The module header of VectorSanity.lean is stale.** Lines 12–21 list only the first-run theorems. They omit `globalNondeg_bounded`, `globalNondeg_uniform_dim` and `globalDecayCrit_pair`.
- **NIT-3. No part brief under `review/prompts/` for VT.** CONTRIBUTING step 7 says parts are proved "under the briefs in `review/prompts/`". Here the lead proved the single part directly, so there was no brief. Route referee N4 had addressed its suggestion to "the part's brief". This is harmless, but it is a deviation from step 7.

Not a finding: the step-11 records (STATUS, CHANGELOG, README, HANDOFF) are not yet updated for VT. That is consistent with step 11 coming after the post-proof reviews.
