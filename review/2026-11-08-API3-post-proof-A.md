11a9ecfc89706e6868700b8fe3cf28256309254f

# Post-proof fidelity review of API3 (referee post-A)

**Bottom line:** all ten theorems are **FAITHFUL**, scope **full**. There is no BLOCKER and no MAJOR. The open items are all in the evidence layer: non-vacuity checks and the status file. None of them affects what the ten theorems mean.

## Commands (repository root, `export PATH=$HOME/.elan/bin:$PATH`, `nice -n 10`, one Lean process at a time)

**1. Tree state.**
```
$ git rev-parse HEAD
11a9ecfc89706e6868700b8fe3cf28256309254f
$ git status --short
(no output: the tree is clean)
```

**2. Statement types.**
```
$ lake env lean StatementTypes.lean | grep -E 'API\.(stationaryPhaseFamily|foldCrit|familyCk_of_uncurry|nonStationaryLocal|stationaryPhaseLocal|foldLocal|d4BoundLocal|nonStationaryOn|stationaryPhaseOn|foldOn) '
TYPE-OK OscInt.API.stationaryPhaseFamily : OscInt.Statements.StationaryPhaseFamilyStatement
TYPE-OK OscInt.API.foldCrit : OscInt.Statements.FoldCritStatement
TYPE-OK OscInt.API.familyCk_of_uncurry : OscInt.Statements.FamilyCkOfUncurryStatement
TYPE-OK OscInt.API.nonStationaryLocal : OscInt.Statements.NonStationaryLocalStatement
TYPE-OK OscInt.API.stationaryPhaseLocal : OscInt.Statements.StationaryPhaseLocalStatement
TYPE-OK OscInt.API.foldLocal : OscInt.Statements.FoldLocalStatement
TYPE-OK OscInt.API.d4BoundLocal : OscInt.Statements.D4BoundLocalStatement
TYPE-OK OscInt.API.nonStationaryOn : OscInt.Statements.NonStationaryOnStatement
TYPE-OK OscInt.API.stationaryPhaseOn : OscInt.Statements.StationaryPhaseOnStatement
TYPE-OK OscInt.API.foldOn : OscInt.Statements.FoldOnStatement
```
Exit 0; 37 TYPE-OK lines in all.

**3. Axiom audit.**
```
$ lake env lean Axioms.lean | grep -E 'OscInt\.API\.(stationaryPhaseFamily|foldCrit|familyCk_of_uncurry|nonStationaryLocal|stationaryPhaseLocal|foldLocal|d4BoundLocal|nonStationaryOn|stationaryPhaseOn|foldOn) |AUDIT-TOTAL'
AUDIT OscInt.API.d4BoundLocal propext,Classical.choice,Quot.sound
AUDIT OscInt.API.familyCk_of_uncurry propext,Classical.choice,Quot.sound
AUDIT OscInt.API.foldCrit propext,Classical.choice,Quot.sound
AUDIT OscInt.API.foldLocal propext,Classical.choice,Quot.sound
AUDIT OscInt.API.foldOn propext,Classical.choice,Quot.sound
AUDIT OscInt.API.nonStationaryLocal propext,Classical.choice,Quot.sound
AUDIT OscInt.API.nonStationaryOn propext,Classical.choice,Quot.sound
AUDIT OscInt.API.stationaryPhaseFamily propext,Classical.choice,Quot.sound
AUDIT OscInt.API.stationaryPhaseLocal propext,Classical.choice,Quot.sound
AUDIT OscInt.API.stationaryPhaseOn propext,Classical.choice,Quot.sound
AUDIT-TOTAL 720 720
```
Exit 0.

## What I read and checked

**Read:**
- `docs/statements.md`: S2/S3, S4, batch 2, and batch 3 with its clarification.
- `OscInt/Statements/{Family,StationaryPhase,Convert}.lean`.
- The two pre-proof reviews and the answers.
- `OscInt/Front/{Family,FamilyC10,Cutoff,Local,FamilySanity}.lean`.
- `StatementTypes.lean`, `Axioms.lean`, `comparator-API3.json`, `Challenge/Family.lean`, `stamps/pins.txt`, the manifest of stamp `20261108T002603Z-9d03130c8f3a`.
- `docs/replay/2026-11-08-API3-sanity-plants.txt` and the replay record `docs/replay/2026-11-08-session5-API3-verify-all.txt`.
- Also: `docs/proof-API3.md`, `OscInt/StationaryPhase/Assembly.lean`, the fact definitions in `Blueprint/StationaryPhase.lean` (LocalBound, LocalizationFacts, LocalNonCritFacts, LocalCritFacts, FamilyAddLinearFacts), and the signatures of `vecOf`, `isCritical_iff`, `integral_eq_oscInt2` and `foldOrNondeg_iff` in `OscInt/Front/Convert.lean`.

**Nothing outside the statement files can change what a statement means:**
- The statement files import only Mathlib and each other.
- The sha256 of these eight files equals the stamp manifest: `Challenge/Family.lean`, `OscInt/Statements/{Family,StationaryPhase,Convert,FrontEnd,D4,D4Limit}.lean`, `comparator-API3.json`.
- The type check is syntactic `Expr` equality.
- The audit shows only the three standard axioms.
- `git log d932c0d..HEAD -- OscInt/StationaryPhase/ Blueprint/StationaryPhase.lean` is empty, so the internal S2/S3 parts have not changed since the S2/S3 final record.
- The proof route and `OscInt/StationaryPhase/*` cannot alter a statement; they only supply proofs of it.

**Replay record:**
- It reports commit a638f70, `make verify-all` RESULT PASS 9/9, axiom audit 720/720, and the type check of all ten.
- Comparator: "comparator-API3.json accepted against stamps/20261108T002603Z-9d03130c8f3a", with six kernels (Lean default and paranoid, lean4lean, nanoda, con-leche, con-ron).
- Commitments match the pinned stamp, and the stamp verifies with RFC 3161 ×3.
- `git diff --stat a638f70 11a9ecf` touches only the record and two review prompts, so the proofs at HEAD are the ones replayed.

## Verdicts

| ID | Lean | Verdict | Scope | Goes through |
|---|---|---|---|---|
| S2.2F | `stationaryPhaseFamily` | FAITHFUL | full | Internal S2/S3 parts re-assembled over Λ × K′: `familyAddLinear`, `localization`, `localNonCrit`, `localCrit_of normalForm normalizedData coreEstimate` (the hessDet branch), and the helpers `isCritical_add_lin`, `hessDet_add_lin`, `familyCk_of_le`, `compactSpace_prod_subtype`. Not the frozen S2.2. |
| S3c | `foldCrit` | FAITHFUL (stronger than S3 by design) | full | The same parts, using the fold branch of `localCrit_of`, plus `foldOrNondeg_add_lin` and `LocalBound.of_one`. The hypothesis is used only under `IsCritical`. |
| C10 | `familyCk_of_uncurry` | FAITHFUL | full | Mathlib only (`iteratedFDeriv_comp_right`, `iteratedFDeriv_comp_add_left`, `continuous_iteratedFDeriv`, `compContinuousLinearMapL`). No project result. |
| FE-S2.1L | `nonStationaryLocal` | FAITHFUL | full | S2.1 `OscInt.nonStationary` with c/√2; C8 (iii) `gradLower_iff`; the cut-off (`exists_cutoff`, `familyCk_cutoff`, `cutoff_eventuallyEq`); `integral_eq_oscInt2`. |
| FE-S2.2L | `stationaryPhaseLocal` | FAITHFUL | full | S2.2F over `vecOf '' K′`; C3 `hessDet_eq_det`; `isCritical_iff`; the cut-off. |
| FE-S3L | `foldLocal` | FAITHFUL | full | S3c; C7 `foldOrNondeg_iff`; the cut-off. |
| FE-S4.1′L | `d4BoundLocal` | FAITHFUL | full | FE-S4.1′ `OscInt.API.d4BoundFE` applied to χφ. Derivatives at 0 transfer through the germ, and δ′ = min δ (r/2). |
| FE-S2.1l | `nonStationaryOn` | FAITHFUL | full | FE-S2.1L with E = ℝ, S = {0}, V = univ. |
| FE-S2.2l | `stationaryPhaseOn` | FAITHFUL | full | FE-S2.2L, same instantiation. |
| FE-S3l | `foldOn` | FAITHFUL | full | FE-S3L, same instantiation (critical-points-only hypothesis). |

For each statement I checked the quantifier order, the smoothness indices, the sign of `+ L`/`+ lin p`, S ⊆ V, K ⊆ U, `V ×ˢ U` and the max norm against the docs. All match the documented text.

## Non-vacuity: do the sanity theorems now witness the new cases?

**What the repository shows.** `FamilySanity.lean` discharges the hypotheses on genuinely new data, but each theorem takes the statement as a hypothesis:
- Critical-points-only fold: `foldCrit_fold_bite`, x³ + y³ with K′ = {(0, −3)}.
- Infinite family: σ(k₁⁴ + 4k₁) + k₂² over σ ∈ [1, 2], with `FamilyCk` via C10.
- Phase not C¹ on ℝ²: `kinkPhase`, through FE-S2.2l and FE-S3l.

**What it does not prove** (only the docstrings say so):
- that a critical point exists in K;
- that S2.2/S3 fail on the fold bite;
- that the planted hypotheses are false (the plant record marks this "CONJECTURED-by-hand").

**What I checked in scratch.** I closed these gaps in `/tmp/post-A/Check.lean` (sha256 f00371fe…). It compiles with exit 0 and its axioms are the standard three. It proves:
- All five sanity theorems instantiate with the *proved* constants (`foldCrit_fold_bite foldCrit`, and the same for the other four).
- **Fold bite:** (0, 1) ∈ K is critical for p = (0, −3) with hessDet = 0, so the S2.2-type hypothesis is false. FoldOrNondeg fails at 0 ∈ K, so S3's hypothesis is false. The p ↦ 0 plant hypothesis is false.
- **Sign family:** every σ ∈ [1, 2] has a critical point in K (by the intermediate value theorem). The −p plant (hessDet form) is false.
- **Kink:** a critical point of kinkPhase + L₀ exists in K. The −L plant is false.
- **Family-local case:** FE-S2.2L applied to σ(k₁⁴ + 4|k₁ + 3| − 12) + k₂² with S = [1, 2] ⊊ V = (0, 3), E = ℝ, U = {k₁ > −3}. This phase is not C¹ on ℝ².
- **Fold branch in Mathlib's idiom:** FE-S3l applied to x³ + y³ with K′ = {−3·snd}, discharged through the fold branch of `FoldOrNondegMatrix` via C7.

**Conclusion.** Within the repository, the three new cases are witnessed only at the level of S3c, S2.2F and FE-S2.2l/FE-S3l with the nondegenerate branch. With my scratch checks they are witnessed non-vacuously.

## Pre-proof derivative-level checks still open

Nothing in the repository covers these:
- **Referee A (a):** an arccos phase through FE-S2.2l.
- **A (b) / B:** a hemisphere on the Euclidean disc, with a non-symmetric K′. The kink data pins `+L` and the e₀/e₁ order for FE-S2.2l/S3l only.
- **A (c) / B:** `FoldOrNondegMatrix` for x³ + y³ at a critical point through FE-S3l. Done only in my scratch.
- **A (e) / B:** FE-S4.1′L on a generic cubic phase that is smooth only near 0. No FE-S4.1′L sanity exists at all.
- **A (f) / B:** a family with S ⊊ V and Ψ singular outside V (e.g. arccos in (a, b)). There is also no repository check of FE-S2.1L/l, FE-S2.2L or FE-S3L through the statement constants.

Done: A (d) (the sign bite: degenerate only off the critical set, p ≠ 0), and B's mixed-term `hessianMatrix` check (batch-2 `ConvertSanity.hessian_mixed`).

Still not caught by any data (as the answers say): p ↦ 0 in S2.2F, and L ↦ 0 in FE-S2.2l/S3l.

## Findings

**BLOCKER:** none. **MAJOR:** none.

**MINOR**
1. The post-proof checklist promised in `review/2026-11-08-API3-pre-proof-answers.md` was not delivered at a638f70 or HEAD. Those are the derivative-level checks of FE-S2.1L/S2.2L/S3L with S ⊊ V, and of FE-S4.1′L on a generic cubic (list above). Non-vacuity of FE-S2.1L/l, FE-S2.2L, FE-S3L and FE-S4.1′L beyond the trivial U = univ case is not witnessed in the repository.
2. `FamilySanity.lean` does not prove that critical points exist in K, or that S2.2/S3 fail on its data. Its "plants caught" evidence is that the proof script breaks, not that the planted hypothesis is false. My scratch shows these facts are true for the fold bite, the sign family (−p, hessDet form) and the kink (−L). Adding such lemmas would make the bites self-certifying.
3. `docs/STATUS.md` has no row or paragraph for API3 and names no replay record for this batch. The brief points to STATUS for the record; I used the record named by the caller.

**NIT**
4. The fold branch of `FoldOrNondegMatrix` (rank one, critical-points-only) is exercised in the repository only through S3c, not through FE-S3L/FE-S3l. The kink bites use the nondegenerate branch.
5. The −p plant for S3c (`foldCrit_sign_bite`) is still hand-argued. It needs ¬FoldOrNondeg at 0 for σ = 1, which follows from ∂³ₓ(σx⁴) = 24σx = 0 at 0, and is unproved.
6. The replay record is on a638f70, not HEAD. The diff is documentation only, and my step 2 and 3 runs at HEAD agree.
7. As already noted pre-proof: `E : Type` and `Λ : Type` live in universe 0; and C10 needs global joint smoothness and is not used by the FE-L forms.

Files touched outside the repository: `/tmp/post-A/run.sh`, `/tmp/post-A/st_full.txt`, `/tmp/post-A/ax_full.txt`, `/tmp/post-A/times.txt`, `/tmp/post-A/Check.lean`. The repository was not modified; `git status --short` is still empty.