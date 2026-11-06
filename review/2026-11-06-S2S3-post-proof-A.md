<!-- Post-proof fidelity review of S2.1, S2.2, S3, referee A (fresh-context agent). Prompt: review/prompts/S2S3-post-proof.md. Read commits c355ee7 and d932c0d (HEAD moved during the review). Verbatim final report from the agent's hand-back call. -->

# Referee A: post-proof fidelity review of S2.1, S2.2 and S3

**Bottom line:** all three proved theorems are FAITHFUL to `docs/statements.md`. Each theorem's type is, syntactically, the frozen statement constant, and each uses only the axioms propext, Classical.choice and Quot.sound. There is no BLOCKER and no MAJOR finding.

**HEAD moved during the review.** It was `c355ee7a720e36e729f4fc484eca0740d2a9e782` when I started. The lead committed `d932c0dbdae632a2e9fd596ab9948498eac5262c` partway through. That commit adds `OscInt/StationaryPhase/Sanity.lean`, an import of it in `OscInt.lean`, a clarification in `docs/statements.md`, and changes to comments and tools. `git diff c355ee7 d932c0d` shows no change to:
- `OscInt/Statements/`
- `Challenge/`
- `StatementTypes.lean`
- `comparator-S2S3.json`
- `stamps/pins.txt`

My first `StatementTypes` run and the `Axioms` run read a working tree whose modified files were the not-yet-committed d932c0d changes. I re-ran `StatementTypes` on the clean d932c0d tree and got the same output. All verdicts are pinned to d932c0d, and they hold equally for c355ee7.

## Required runs (verbatim; repository root, `nice -n 10`, one Lean process at a time)

**1. `git rev-parse HEAD`**
```
c355ee7a720e36e729f4fc484eca0740d2a9e782   (at start)
d932c0dbdae632a2e9fd596ab9948498eac5262c   (at the end, clean tree)
```

**2. `lake env lean StatementTypes.lean`** (same output on both runs; the second on clean d932c0d)
```
TYPE-OK OscInt.vanDerCorput_one : OscInt.Statements.VdC1Statement
TYPE-OK OscInt.vanDerCorput_two : OscInt.Statements.VdC2Statement
TYPE-OK OscInt.vanDerCorput_three : OscInt.Statements.VdC3Statement
TYPE-OK OscInt.nonStationary : OscInt.Statements.NonStationaryStatement
TYPE-OK OscInt.stationaryPhase : OscInt.Statements.StationaryPhaseStatement
TYPE-OK OscInt.fold : OscInt.Statements.FoldStatement
```

**3. `cat build/commit/commitments.txt`**
```
2650f1484b3252166e9442f383ad734075f60f180d595c7d6729d9737edba5ad  OscInt.Statements.FoldStatement
a837c8bd8352929aa4ba6456ff19603cd34f7ae09b2896de0af2565fd0f803b4  OscInt.Statements.VdC1Statement
66cc331de7d7bf5fb38076895ff7014f280b41cced6492f70cd87134a78a39f5  OscInt.Statements.VdC2Statement
30b3f96ca215778d4034c6ca660818b04a842bb4b574f27f4a648a64bf9ab4f4  OscInt.Statements.VdC3Statement
238318a74792495f2009807e724673e80c4d3f66b91580c564105d84396fe8f8  OscInt.Statements.NonStationaryStatement
283a23fe63ba052ba6600edd08ee3def6d728a75dbbaa6d7f39fc031fc9eccff  OscInt.Statements.StationaryPhaseStatement
```
The S2/S3 lines (Fold 2650f148…, NonStationary 238318a7…, StationaryPhase 283a23fe…) are identical to the `commitment` lines in `stamps/20261105T234456Z-533ae0272521/manifest.txt`, the pinned stamp for all three statements and for `challenge:comparator-S2S3.json` in `stamps/pins.txt`.

This file was not computed on either HEAD (see MINOR 1). Two checks still tie the hashes to the current statements:
- The sha256 of `OscInt/Statements/StationaryPhase.lean` is `cd43a116…ec`, at HEAD and in the working tree, equal to its manifest entry.
- `Challenge/StationaryPhase.lean` (`eda6cebb…`) and `comparator-S2S3.json` (`fd682627…`) also equal their manifest entries.

**4. `lake env lean Axioms.lean | grep -E 'OscInt\.(nonStationary|stationaryPhase|fold) |AUDIT-TOTAL'`**
```
AUDIT OscInt.fold propext,Classical.choice,Quot.sound
AUDIT OscInt.nonStationary propext,Classical.choice,Quot.sound
AUDIT OscInt.stationaryPhase propext,Classical.choice,Quot.sound
AUDIT-TOTAL 267 267
```
Exit code 0. The tree included `Sanity.lean`.

## What I read
- **Repository files:**
  - `docs/statements.md`: S2 and S3, both clarifications, and the new 2026-11-06 clarification.
  - `OscInt/Statements/StationaryPhase.lean`, `StatementTypes.lean`, `comparator-S2S3.json`, `stamps/pins.txt` and the pinned manifest.
  - Both pre-proof reports, `review/2026-11-05-S2S3-pre-proof-A.md` and `-B.md`.
  - `OscInt/StationaryPhase/Final.lean`, `Challenge/StationaryPhase.lean`, `Axioms.lean`, `OscInt.lean`, and the header of `Blueprint/StationaryPhase.lean`.
- **Proof files, checked only for anything that could change meaning:**
  - I grepped every `OscInt/StationaryPhase/*.lean` and `Blueprint/StationaryPhase.lean` for axiom, sorry, admit, opaque, unsafe, implemented_by, extern, set_option, elab, macro, syntax, run_cmd, #eval, instance and namespace. There are no hits other than namespaces under `OscInt.StationaryPhase.*` and `OscInt.Blueprint`, plus one `infer_instance` tactic.
  - No file reopens `OscInt.Statements` or defines anything there.
  - I read `Sanity.lean` in full. It holds bite and exclusion theorems only and defines nothing that statements use.
- **Why the proof files cannot change the meaning:**
  - `StatementTypes` checks `Expr` equality of each theorem's type with the constant `OscInt.Statements.*Statement`.
  - That constant is elaborated in the stamped module, whose source hash and commitment match the stamp.
  - Later modules can neither redefine the constant nor change its elaborated value.
- I did not read the other referee's report (`review/2026-11-06-S2S3-post-proof-B.md`) or the adversarial report.

## Verdicts

| Theorem | Against docs/statements.md | Against the classical result | Scope | Pinned commitment |
|---|---|---|---|---|
| `OscInt.nonStationary` | FAITHFUL | FAITHFUL | full | `238318a74792495f2009807e724673e80c4d3f66b91580c564105d84396fe8f8` |
| `OscInt.stationaryPhase` | FAITHFUL | FAITHFUL | full | `283a23fe63ba052ba6600edd08ee3def6d728a75dbbaa6d7f39fc031fc9eccff` |
| `OscInt.fold` | FAITHFUL | FAITHFUL-WEAKER (documented hypothesis restriction) | full | `2650f1484b3252166e9442f383ad734075f60f180d595c7d6729d9737edba5ad` |

**S2.1 (`nonStationary`).** The Lean text matches the doc in every respect:
- `FamilyCk (N+1)` over a compact Λ, and `AmpBound N K A M`.
- `GradLower` stated with squares, i.e. the Euclidean condition |∇Ψ_σ + p| ≥ c on all of K.
- The bound `C * M / m ^ N` with a natural power and m ≥ 1.
- `∃ C` placed after (Λ, N, Ψ, K, c) and before (A, M, σ, p, m).

This is the classical non-stationary phase estimate: C^{N+1} phase, C^N amplitude, decay m^{-N}, with the constant depending on derivative bounds of the phase and the gradient lower bound. It is uniform over every p with the gradient bound, not only over a compact set of p. That is at least as strong as the textbook form and is documented. `bite_nonStationary_unbounded` in `Sanity.lean` shows the uniformity over unbounded p is really obtained.

**S2.2 (`stationaryPhase`).** The Lean text matches the doc:
- A single C⁴ phase.
- Nondegeneracy (`hessDet ≠ 0`) only at critical points k ∈ K of Ψ + p· for p ∈ K′.
- C² amplitude, and the bound C·M/m.

Classically this is Hörmander, Theorem 7.7.5 with k = 1 and n = 2 (C⁴ phase, C²₀ amplitude, O(ω^{-1}) times the C² norm), made uniform over compact K′. Neither pre-proof referee found a discrepancy, and I find none.

**S3 (`fold`).** The Lean text matches the doc, including "condition at every point of K":
- `FoldOrNondeg` is exactly "nondegenerate, or rank one with ∂_v³Ψ ≠ 0 along the kernel".
- `cusp_excluded` in `Sanity.lean` confirms that the A₃ point k₁⁴ + k₂² is excluded.
- `sanity_Fold_hyps` and `bite_fold_instance` confirm the rank-one branch is satisfiable and is used.
- The exponent m^{-5/6} = m^{-1/2}·m^{-1/3} is the classical A₂ (fold) oscillation index, uniform under C⁴ perturbations (Duistermaat; Arnold–Gusein-Zade–Varchenko).

Against the classical result the theorem is weaker, because the fold-or-nondegenerate condition is required at every point of K, critical or not, and independently of p. The classical estimate needs it only at critical points of Ψ_σ + p· for p ∈ K′. This is documented in the stamped modelling choices and in the 2026-11-06 clarification, which gives the example k₁³ + k₂³ + k₁. Per that clarification, it is satisfied by the planned S4 use.

## Findings

- **MINOR 1 (record).** `build/commit/commitments.txt` was not computed by `make verify-all` on the reviewed commit.
  - The file is dated 2026-11-06 01:37:30. That is after the proof commit 1e6c73f (00:56) and before 63ff52b (01:39), c355ee7 (02:05) and d932c0d (02:16).
  - `docs/replay/2026-11-06-S2S3-verify-all.txt` records verify-all on 1e6c73f only.
  - The hashes still match the stamp. The statement module's source is byte-identical to the stamped file at HEAD, and every commit since the stamp leaves `OscInt/Statements/` untouched.
  - The lead should still re-run `make verify-all` (commit, comparator and replay) on the final HEAD d932c0d and record it.
- **MINOR 2 (record).** d932c0d adds `OscInt/StationaryPhase/Sanity.lean` to the root module after the recorded verify-all and replay. My `Axioms.lean` run includes it, with all 267 theorems clean. But no recorded comparator run or `leanchecker` replay covers the new module. This does not affect the meaning of the three final theorems.
- **MINOR 3 (fidelity to classical, documented).** S3 imposes `FoldOrNondeg` at every point of K, including non-critical points. This is stronger than the classical hypothesis, so the theorem is weaker; it is the reason for the FAITHFUL-WEAKER verdict. It is already disclosed in the docs. I flag it only so that any citation says "fold condition on all of K".
- **NIT 4.** `∀ (Λ : Type)` restricts the family parameter to universe 0, in S2.1 and S3. This is harmless for Λ ⊆ ℝ.
- **NIT 5.** S2.2 is for a single phase, not uniform over a compact family. The doc says the same.
- **NIT 6.** S3 is uniform only over a compact K′, whereas uniformity over all of ℝ² would also hold. This is weaker but correct, and it is what the doc states.
- **NIT 7 (process).** The repository was committed to while post-proof referees were running, so HEAD changed between my required run 1 and the end of the review. Freezing the tree while referees run would make "this commit" unambiguous.

The scratch output of the background audit run is at `/tmp/claude-0/-home-user-lean-oscillatory/ce808543-6e2d-583b-be8e-5671768737ef/tasks/bf8svghkh.output`. No repository files were edited.