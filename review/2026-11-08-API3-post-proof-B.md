11a9ecfc89706e6868700b8fe3cf28256309254f

# Post-proof fidelity review of API3: referee post-B

I'm a fresh referee and did not look at the other report. I wrote nothing in the repository, made no git changes, did not touch `build/` and ran no `make` target. My scratch is `/tmp/post-B/` (`runs.txt` and `Check.lean`). I ran one Lean process of my own at a time, each under `nice -n 10`. Another reviewer's Lean process was also on the machine.

## Runs (verbatim)

**1. `git rev-parse HEAD`; `git status --short`**
```
11a9ecfc89706e6868700b8fe3cf28256309254f
```
`git status --short` printed nothing, so the tree is clean. It was still clean after all my runs.

**2. `lake env lean StatementTypes.lean | grep -E '…'`**
```
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

**3. `lake env lean Axioms.lean | grep -E '…|AUDIT-TOTAL'`**
```
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

**Stamp integrity.** I recomputed sha256 for these files; each equals its line in `stamps/20261108T002603Z-9d03130c8f3a/manifest.txt`:
- `OscInt/Statements/Family.lean`
- `OscInt/Statements/Convert.lean`
- `OscInt/Statements/StationaryPhase.lean`
- `Challenge/Family.lean`
- `Challenge.lean`
- `comparator-API3.json`
- `Axioms.lean`

`StatementTypes.lean` differs from the stamp, but `git diff 9d03130 HEAD` shows only the ten added `#assert_type_is` lines, which is expected. `stamps/pins.txt` pins all ten constants and `challenge:comparator-API3.json` to that stamp. `comparator-API3.json` names exactly the ten theorems and permits only the three standard axioms.

**Replay record.** `docs/replay/2026-11-08-session5-API3-verify-all.txt` reports `make verify-all` on a638f70: RESULT PASS 9/9, axiom audit 720/720, all ten TYPE-OK, leanchecker PASS on `Front.{Cutoff,Family,FamilyC10,FamilySanity,Local}`, and `comparator-API3.json accepted against stamps/20261108T002603Z-9d03130c8f3a`. The only commit between a638f70 and HEAD (11a9ecf) changes just that record and two prompt files, none of them Lean files.

## Verdicts

| # | Statement | Theorem | Verdict | Scope |
|---|---|---|---|---|
| 1 | S2.2F | `OscInt.API.stationaryPhaseFamily` | FAITHFUL | full |
| 2 | S3c | `OscInt.API.foldCrit` | FAITHFUL (stronger than S3, as intended) | full |
| 3 | C10 | `OscInt.API.familyCk_of_uncurry` | FAITHFUL | full |
| 4 | FE-S2.1L | `OscInt.API.nonStationaryLocal` | FAITHFUL | full |
| 5 | FE-S2.2L | `OscInt.API.stationaryPhaseLocal` | FAITHFUL | full |
| 6 | FE-S3L | `OscInt.API.foldLocal` | FAITHFUL | full |
| 7 | FE-S4.1′L | `OscInt.API.d4BoundLocal` | FAITHFUL | full |
| 8 | FE-S2.1l | `OscInt.API.nonStationaryOn` | FAITHFUL | full |
| 9 | FE-S2.2l | `OscInt.API.stationaryPhaseOn` | FAITHFUL | full |
| 10 | FE-S3l | `OscInt.API.foldOn` | FAITHFUL | full |

Each theorem's type is, by `Expr` equality, the stamped constant, and each constant matches the text in `docs/statements.md` "Front end, batch 3":
- **Quantifier order.** `∃ C` (and `∃ δ > 0, ∃ C`) comes after all the data and before `A, M, σ, p/L, m/t`.
- **Rates.** `C*M/m`, `C*M*m^(-5/6)`, `C*M/m^N`, `C*M*t^(-2/3)`.
- **Critical-point-only hypotheses.**
  - S2.2F and S3c: `IsCritical (Ψ σ) p k →`, for `σ`, `p ∈ K'`, `k ∈ K`.
  - FE-S2.2L/S3L/S2.2l/S3l: `fderiv ℝ (Ψ σ) k + L = 0 →`.
- **Fold condition.** FE-S3L/l use `FoldOrNondegMatrix`, which is the span form (clarification (4)).
- **Local smoothness.** It is `ContDiffOn` on `V ×ˢ U`, or on `U`.
- **Derivatives only at points of open sets.** They are taken at `k ∈ K ⊆ U` with `σ ∈ S ⊆ V`, or at `0 ∈ U`, so junk `fderiv` values outside `U` are never used.

The proofs confirm both directions:
- **No hypothesis is used more strongly than stated.** S3c's proof calls `hfold` only inside the `IsCritical` branch.
- **No conclusion is weakened.** Each bridge returns the frozen bound for the same `A, M, σ, L, m`.

## Which proved results each proof goes through

**S2.2F and S3c** (`OscInt/Front/Family.lean`):
- These are re-assemblies of `stationaryPhase_of` and `fold_of` over `Λ × K'`.
- They use the internal parts of S2.2/S3: `familyAddLinear`, `localization`, `localNonCrit`, `localCrit_of normalForm normalizedData coreEstimate`, `LocalBound.of_one`, `compactSpace_prod_subtype`, `isCritical_add_lin`, `hessDet_add_lin`, `foldOrNondeg_add_lin`.
- They do not use the frozen S2.2 or S3 statements, as clarification (1) says.

**C10** (`OscInt/Front/FamilyC10.lean`):
- Mathlib calculus only. The `j`-th derivative of the slice is the `j`-th derivative of `uncurry Ψ` composed with `inr` in every argument (`iteratedFDeriv_comp_right` + `iteratedFDeriv_comp_add_left`).
- Continuity comes from `ContDiff.continuous_iteratedFDeriv` and `compContinuousLinearMapL`.

**Cut-off** (`OscInt/Front/Cutoff.lean`):
- `exists_cutoff` builds χ from `exists_contDiff_support_eq_eq_one_iff` between thickenings of K, with `tsupport χ ⊆ cthickening δ K ⊆ U` and χ = 1 on `thickening (δ/4) K`.
- `familyCk_cutoff` covers the parameter space by two regions:
  - on `S × U`: the local slice identity, via `iteratedFDerivWithin_comp_right` on an open set;
  - on `S × (tsupport χ)ᶜ`: every derivative is 0.
- This works for any normed E; no bump function on E is needed.

**FE-S2.1L.** The cut-off family plus the frozen S2.1 `OscInt.nonStationary` with `c/√2`. The gradient hypothesis goes through C8 (iii) `gradLower_iff`, with the `fderiv` transferred by germ equality. The integrals are equal pointwise via `integral_congr_on`, since A = 0 off K and χ = 1 on K.

**FE-S2.2L and FE-S3L.** The cut-off family plus S2.2F/S3c with `vecOf '' K'` (compact). They use C3 `hessDet_eq_det` and C7 `foldOrNondeg_iff`, applied to the globally C⁴ cut-off phase. `isCritical_iff`, and `fderiv`, Hessian and D³ transferred by germ equality (`LocalAux.transfer`).

**FE-S4.1′L.** Cut-off at {0} plus FE-S4.1′ `OscInt.API.d4BoundFE`. `D²` and `D³` at 0 are transferred by germ equality, and δ' = min(δ, r/2), where `closedBall 0 δ' ⊆ W`.

**FE-S2.1l, S2.2l, S3l.** The L forms with `E = ℝ`, `S = {0}`, `V = univ`, and the constant family.

**Could anything else change the meaning?** No:
- The statement constants live in stamped files whose import chain is Mathlib plus stamped `Statements` files only. No proof file, including `OscInt/StationaryPhase/*.lean`, `OscInt/Front/*` and `docs/proof-API3.md` (all of which I read), can affect how they elaborate.
- `StatementTypes` checks `Expr` equality, the comparator checks against the stamped challenge export, and the axiom audit is clean.
- Regularity indices are finite (`↑N + 1`, `4`), so there is no ω/⊤ issue.

## Do the sanity theorems in `FamilySanity.lean` now witness non-vacuity for the new cases?

They are stated conditionally (statement constant → instance). I instantiated them with the proved theorems in `/tmp/post-B/Check.lean`, and everything compiled:
- `foldCrit_fold_bite foldCrit`
- `stationaryPhaseFamily_sign_bite familyCk_of_uncurry stationaryPhaseFamily`
- `foldCrit_sign_bite …`
- `stationaryPhaseOn_kink stationaryPhaseOn`
- `foldOn_kink foldOn`

**Critical-points-only fold: yes, for S3c.** `foldCrit_fold_bite` covers x³+y³ with K = B̄(0,2) and K′ = {(0,−3)}.
- The stamped `sanity_FoldCrit_bite` already proves `¬FoldOrNondeg` at 0 ∈ K, so S3 does not apply.
- That S2.2 does not apply either (a degenerate critical point in K) was only argued in the docstring. I proved it in scratch: `IsCritical (x³+y³) (0,−3) (0,1) ∧ hessDet … (0,1) = 0 ∧ (0,1) ∈ B̄(0,2)`.
- I also discharged the matrix-level rank-one branch through **FE-S3l** in scratch: `FoldOrNondegMatrix` at the critical points, with `L₁ = −3•snd`, via C7, giving the m^{−5/6} bound from `foldOn`. And I proved `¬FoldOrNondegMatrix (x³+y³) 0`.
- The repository itself has no such theorem; see MINOR 2.

**Infinite family: yes.** The sign family σ(k₁⁴+4k₁)+k₂² over σ ∈ `Icc 1 2` gets `FamilyCk 4` through C10, with `p = (4,0) ≠ 0` and critical points at k₁ ≠ 0, where the Hessian is nondegenerate.
- At k₁ = 0 the Hessian degenerates with a zero cubic along the kernel, so frozen S3 does not apply.
- Frozen S2.2 is single-phase, so it gives no uniformity in σ. The S2.2F uniform rate m^{−1} on this family is therefore new.
- That a critical point exists in K (x³ = −1−1/σ, so x ≈ −1.14 to −1.26) is shown on paper, not in Lean.

**Phase not C¹ on ℝ²: yes, but only for FE-S2.2l and FE-S3l.** `kinkPhase_not_contDiff` plus `stationaryPhaseOn_kink` and `foldOn_kink`, with `U = {k₁ > −3}` and K ⊊ U. This pins `+L` and the e₀/e₁ order. Two limits:
- Only the nondegenerate branch is exercised there.
- Nothing exercises FE-S2.1l, FE-S2.1L, FE-S2.2L or FE-S3L with S ⊊ V, a phase singular outside V × U, or FE-S4.1′L.

**Negative controls** (`docs/replay/2026-11-08-API3-sanity-plants.txt`). Four plants are rejected and the unplanted copies are accepted. Plants that are documented as not caught: `p ↦ 0` in S2.2F, and `L ↦ 0` in FE-S2.2l/S3l.

## Post-proof derivative-level checks from the pre-proof reports that remain open

Referee A's list (a)–(f), adopted as the post-proof checklist in the answers:
- **(a) open.** The arccos phase, with `hessianMatrix` at a critical point, through FE-S2.2l.
- **(b) partly done.** The kink pins `+L` and the e₀/e₁ order. The hemisphere on the Euclidean disc U with a non-symmetric K′ is open.
- **(c) open in the repository.** x³+y³ with `FoldOrNondegMatrix` through FE-S3l/FE-S3L (rank-one branch). I discharged it in scratch only.
- **(d) done.** The sign family.
- **(e) open.** FE-S4.1′L on a generic cubic (1,2,3,5) smooth only near 0.
- **(f) open.** A family with E = ℝ², S ⊊ V, singular outside V (the arccos family in (a,b)), through FE-S2.1L/S2.2L/S3L.

Referee B's list:
- **Open:** the hemisphere Hessian at a non-central point; `FoldOrNondegMatrix` for x³+y³ at (0,1) (scratch only); the arccos family; FE-S4.1′L generic cubic times a function smooth only near 0; local-form bites through the constants for FE-S2.1l/L, FE-S2.2L, FE-S3L and FE-S4.1′L.
- **Covered in batch 2** (`ConvertSanity.hessian_mixed`): `hessianMatrix` of a quadratic with a mixed term.

## Findings

**BLOCKER:** none.

**MAJOR:** none.

**MINOR**
1. **`docs/STATUS.md` has no API3 rows and names no replay record for this batch.** The brief asks for "the replay record named in `docs/STATUS.md` for this batch"; none is named there. I used `docs/replay/2026-11-08-session5-API3-verify-all.txt`, as directed. STATUS should get the ten rows, with the record on a638f70 and the post-proof and adversarial results.
2. **The new features of the Mathlib-idiom local forms are only partly witnessed in Lean.**
   - The fold (rank-one) branch of `FoldOrNondegMatrix` is never exercised through FE-S3l or FE-S3L; the kink uses the nondegenerate branch.
   - FE-S2.1L/S2.1l, FE-S2.2L/S3L with S ⊊ V and singularities outside V × U, and FE-S4.1′L have no sanity theorem through their constants or bridges.
   - Checks (a), (c), (e), (f) and B's corresponding items are open (list above).
   - The proofs are kernel-checked and the meaning is fixed, so this is coverage, not fidelity.
3. **Two of the "neither S2.2 nor S3 applies" claims are only on paper.**
   - `foldCrit_fold_bite`: the degenerate critical point at (0,1) for S2.2.
   - The sign family: that a critical point exists in K.
   - Both are short Lean lemmas; I proved the first in scratch.

**NIT**
1. **The sanity theorems stay conditional.** Nothing in the repository instantiates them with the proved theorems. One-line `example`s such as `foldCrit_fold_bite OscInt.API.foldCrit` would turn them into unconditional, non-vacuous instances. All five compile (`/tmp/post-B/Check.lean`).
2. **`OscInt/Front/Local.lean` comment.** It says it applies "the frozen S2.1, the re-assembled S2.2F/S3c … or FE-S4.1′". That is accurate. Readers should still note that S2.2F/S3c are proved results of this batch, not frozen inputs, so FE-S2.2L/S3L rest on the internal S2.2/S3 parts.

Paths:
- `/home/user/lean-oscillatory/OscInt/Front/Family.lean`
- `/home/user/lean-oscillatory/OscInt/Front/FamilyC10.lean`
- `/home/user/lean-oscillatory/OscInt/Front/Cutoff.lean`
- `/home/user/lean-oscillatory/OscInt/Front/Local.lean`
- `/home/user/lean-oscillatory/OscInt/Front/FamilySanity.lean`
- `/home/user/lean-oscillatory/docs/STATUS.md`
- `/tmp/post-B/Check.lean`
- `/tmp/post-B/runs.txt`