<!-- Post-proof fidelity review of S2.1, S2.2, S3, referee B (fresh-context agent). Prompt: review/prompts/S2S3-post-proof.md. Read commit c355ee7. Verbatim final report from the agent's hand-back call. -->

# Referee B: post-proof fidelity review of S2.1, S2.2 and S3

**Overall:** all three theorems are FAITHFUL to the docs, with scope `full`. There are no BLOCKER and no MAJOR findings, and I edited no repository files.

## Commands (repository root, `nice -n 10`, one Lean process at a time)

**1. `git rev-parse HEAD`**
```
c355ee7a720e36e729f4fc484eca0740d2a9e782
```

**2. `lake env lean StatementTypes.lean`**
```
TYPE-OK OscInt.vanDerCorput_one : OscInt.Statements.VdC1Statement
TYPE-OK OscInt.vanDerCorput_two : OscInt.Statements.VdC2Statement
TYPE-OK OscInt.vanDerCorput_three : OscInt.Statements.VdC3Statement
TYPE-OK OscInt.nonStationary : OscInt.Statements.NonStationaryStatement
TYPE-OK OscInt.stationaryPhase : OscInt.Statements.StationaryPhaseStatement
TYPE-OK OscInt.fold : OscInt.Statements.FoldStatement
```

**3. `cat build/commit/commitments.txt`** (the file is present, mtime Nov 6 01:37)
```
2650f1484b3252166e9442f383ad734075f60f180d595c7d6729d9737edba5ad  OscInt.Statements.FoldStatement
a837c8bd8352929aa4ba6456ff19603cd34f7ae09b2896de0af2565fd0f803b4  OscInt.Statements.VdC1Statement
66cc331de7d7bf5fb38076895ff7014f280b41cced6492f70cd87134a78a39f5  OscInt.Statements.VdC2Statement
30b3f96ca215778d4034c6ca660818b04a842bb4b574f27f4a648a64bf9ab4f4  OscInt.Statements.VdC3Statement
238318a74792495f2009807e724673e80c4d3f66b91580c564105d84396fe8f8  OscInt.Statements.NonStationaryStatement
283a23fe63ba052ba6600edd08ee3def6d728a75dbbaa6d7f39fc031fc9eccff  OscInt.Statements.StationaryPhaseStatement
```
I compared these with the `commitment` lines of `stamps/20261105T234456Z-533ae0272521/manifest.txt`. The three S2/S3 lines are identical: NonStationary `238318a7…f8`, StationaryPhase `283a23fe…cff`, Fold `2650f148…5ad`. The three VdC lines also match.

**4. `lake env lean Axioms.lean | grep -E 'OscInt\.(nonStationary|stationaryPhase|fold) |AUDIT-TOTAL'`** (6m28s)
```
AUDIT OscInt.fold propext,Classical.choice,Quot.sound
AUDIT OscInt.nonStationary propext,Classical.choice,Quot.sound
AUDIT OscInt.stationaryPhase propext,Classical.choice,Quot.sound
AUDIT-TOTAL 267 267
```

## Integrity checks beyond the four commands
- **Statement file unchanged.** `OscInt/Statements/StationaryPhase.lean` has sha256 `cd43a116…c10aaecdff226c`, equal to its manifest entry. `git diff 533ae02..HEAD -- OscInt/Statements/` is empty.
- **Other changes since the stamp.** Only two files changed:
  - `StatementTypes.lean`: three `#assert_type_is` lines added for the S2/S3 theorems.
  - `docs/statements.md`: an appended clarification paragraph about where C⁴ is used. The stamped S2/S3 text is untouched.
  - `comparator-S2S3.json`, `lean-toolchain` and `lake-manifest.json` are unchanged.
- **Challenge file.** `Challenge/StationaryPhase.lean` states exactly `theorem nonStationary : Statements.NonStationaryStatement := sorry`, and the same for `stationaryPhase` and `fold`. The config `comparator-S2S3.json` names these three theorems and permits only the axioms {propext, Quot.sound, Classical.choice}.
- **Recorded replay.** `docs/replay/2026-11-06-S2S3-replay.txt` records RESULT PASS: per-module leanchecker, export sha `d78305cf…`, leanchecker and paranoid from the export, nanoda, con-leche, con-ron and lean4lean. I did not re-run it.

**Proof files: what I looked at.**
- I read `OscInt/StationaryPhase/Final.lean` in full. Each theorem is an application of `*_of` combinators to proved parts.
- I grepped every `OscInt/StationaryPhase/*.lean`, `Blueprint/StationaryPhase.lean`, `Blueprint.lean` and `OscInt/Basic.lean` for these keywords, with no hits: `axiom|sorry|admit|unsafe|implemented_by|extern|set_option|opaque|macro|elab|syntax|notation|attribute|instance|native_decide|ofReduceBool|initialize`.
- I checked the import graph. The proof files import only Mathlib, `OscInt.*` and `Blueprint.StationaryPhase`. `Blueprint.StationaryPhase` imports only the statement module and contains only `def … : Prop` declarations (the `*Facts`, `LocalBound` and `CoreHyps` definitions).
- **Conclusion:** the statement constants are elaborated in a module imported before every proof file. The type check is syntactic `Expr` equality with the constant, and the axiom closure is transitive and clean. So nothing in the proof files can change what the statements mean.

## Verdicts

**`OscInt.nonStationary` — FAITHFUL; scope full; pinned to commitment `238318a74792495f2009807e724673e80c4d3f66b91580c564105d84396fe8f8`.**
- It matches docs S2.1 symbol for symbol: compact Λ; `FamilyCk (N+1)`; `AmpBound N K A M`; `GradLower` (Euclidean, |∇Ψ_σ + p| ≥ c) on all of K, for every p ∈ ℝ²; m ≥ 1; bound `C*M/m^N`. `∃ C` comes before A, M, σ, p and m.
- It is the classical non-stationary phase lemma (N integrations by parts, needing D^{N+1} of the phase and D^N of the amplitude), uniform over compact families and unbounded linear terms.
- It is not vacuous: `sanity_NonStationary_hyps` and `sanity_ampBound_exists` exhibit data satisfying the hypotheses.

**`OscInt.stationaryPhase` — FAITHFUL; scope full; pinned to commitment `283a23fe63ba052ba6600edd08ee3def6d728a75dbbaa6d7f39fc031fc9eccff`.**
- It matches docs S2.2 exactly: a C⁴ phase; H ≠ 0 at critical points k ∈ K of Ψ + p· for p ∈ K′; `AmpBound 2`; bound `C*M/m`, uniform over p ∈ K′.
- It is the classical result in dimension 2 with a C⁴ phase and a C² amplitude (Hörmander, Thm 7.7.5, k = 1).
- It is not vacuous: the saddle k₁² − k₂² has a genuine critical point in K for p = 0 ∈ K′.

**`OscInt.fold` — FAITHFUL; scope full; pinned to commitment `2650f1484b3252166e9442f383ad734075f60f180d595c7d6729d9737edba5ad`.**
- It matches docs S3: `FamilyCk 4`, `FoldOrNondeg` at every σ and every k ∈ K, `AmpBound 2`, p ∈ K′, bound `C*M*m^(-5/6)` (rpow, m ≥ 1).
- `FoldOrNondeg` means: Hessian nondegenerate, or Hessian of rank one with the cubic term nonzero on its kernel. This excludes A₃ (k₁⁴ + k₂²) and D₄.
- Against the classical results (Duistermaat's uniform A₂ estimate), this is a correct special case:
  - **Narrower:** the fold-or-Morse condition is required at every point of K, not only at critical points for p ∈ K′.
  - **Broader:** it needs only a C² amplitude, where the brief has ‖A‖_{C⁴}.
  - Both deviations are documented.
- It is not vacuous: `sanity_Fold_hyps` uses a point with hessDet = 0, so the fold branch is exercised.

## Findings
- **MINOR (provenance).** The prompt says `build/commit/commitments.txt` was computed by `make verify-all` "on this commit" (c355ee7). Its mtime (01:37) and `docs/replay/2026-11-06-S2S3-verify-all.txt` show it was computed on 1e6c73f.
  - This is harmless here: the statement module and toolchain files are byte-identical from the stamp commit 533ae02 to HEAD, and my step 2 and step 4 runs on HEAD agree.
  - Still, the record should say which commit computed the file, or the file should be recomputed on the commit under review.
- **MINOR (S3 scope, carried over from pre-proof referee A).** The hypothesis `∀ σ, ∀ k ∈ K, FoldOrNondeg (Ψ σ) k` applies at every point of K, not only at critical points. The theorem is therefore weaker than the most general classical form. It is documented and not a fidelity defect, but it matters only if S4's rescaled phases fail the condition at non-critical points of K.
- **NIT.** `docs/statements.md` was edited after the stamp: a clarification was appended and the file hash differs from the manifest entry `ff86bfbd…`. The stamped S2/S3 text is unchanged, and the addition does not change what any statement means.
- **NIT.** `∀ (Λ : Type)` is universe 0 only (both pre-proof referees noted this). It is harmless for Λ ⊆ ℝ.
- **NIT.** S2.2 is stated for a single phase, not uniformly over a family; the docs agree.
- **NIT.** In S3, compact K′ is weaker than the true uniformity over all p ∈ ℝ².
