9e5540ac7a07bd677156575352bbdc708aaea87b

# Post-proof fidelity review, front-end batch 2 (referee ppA)

**Verdict: all fourteen theorems are FAITHFUL, scope `full`. No BLOCKER and no MAJOR.** There are 2 MINOR findings and 3 NIT findings, all about non-vacuity coverage and process wording. None affects what is proved.

## Commands, verbatim results
I used `export PATH=$HOME/.elan/bin:$PATH` and `nice -n 10`, ran one process at a time, and ran no make targets.

**1.** `git rev-parse HEAD` printed `9e5540ac7a07bd677156575352bbdc708aaea87b`. `git status --short` printed nothing, so the tree was clean.

**2.** `lake env lean StatementTypes.lean | grep ...` (exit 0):
```
TYPE-OK OscInt.API.dd_iteratedFDeriv : OscInt.Statements.DdEqIteratedStatement
TYPE-OK OscInt.API.ddd_iteratedFDeriv : OscInt.Statements.DddEqIteratedStatement
TYPE-OK OscInt.API.hessDet_eq_det : OscInt.Statements.HessDetEqDetStatement
TYPE-OK OscInt.API.cubicCoeffs_eq : OscInt.Statements.CubicCoeffsEqStatement
TYPE-OK OscInt.API.disc_eq_cubic_discr : OscInt.Statements.DiscEqCubicDiscrStatement
TYPE-OK OscInt.API.disc_ne_zero_iff_isolated : OscInt.Statements.DiscNeZeroIffIsolatedStatement
TYPE-OK OscInt.API.foldOrNondeg_iff : OscInt.Statements.FoldOrNondegIffStatement
TYPE-OK OscInt.API.foldOrNondeg_of_hasFDeriv : OscInt.Statements.FoldOrNondegOfHasFDerivStatement
TYPE-OK OscInt.API.gradLower_iff : OscInt.Statements.GradLowerIffStatement
TYPE-OK OscInt.API.ampBound_conv : OscInt.Statements.AmpBoundConvStatement
TYPE-OK OscInt.API.nonStationaryFE : OscInt.Statements.NonStationaryFEStatement
TYPE-OK OscInt.API.stationaryPhaseFE : OscInt.Statements.StationaryPhaseFEStatement
TYPE-OK OscInt.API.foldFE : OscInt.Statements.FoldFEStatement
TYPE-OK OscInt.API.d4BoundFE : OscInt.Statements.D4BoundFEStatement
```
The 13 earlier statements also printed TYPE-OK, 27 in all.

**3.** `lake env lean Axioms.lean | grep ...` (exit 0):
```
AUDIT OscInt.API.ampBound_conv propext,Classical.choice,Quot.sound
AUDIT OscInt.API.cubicCoeffs_eq propext,Classical.choice,Quot.sound
AUDIT OscInt.API.d4BoundFE propext,Classical.choice,Quot.sound
AUDIT OscInt.API.dd_iteratedFDeriv propext,Classical.choice,Quot.sound
AUDIT OscInt.API.ddd_iteratedFDeriv propext,Classical.choice,Quot.sound
AUDIT OscInt.API.disc_eq_cubic_discr propext,Classical.choice,Quot.sound
AUDIT OscInt.API.disc_ne_zero_iff_isolated propext,Classical.choice,Quot.sound
AUDIT OscInt.API.foldFE propext,Classical.choice,Quot.sound
AUDIT OscInt.API.foldOrNondeg_iff propext,Classical.choice,Quot.sound
AUDIT OscInt.API.foldOrNondeg_of_hasFDeriv propext,Classical.choice,Quot.sound
AUDIT OscInt.API.gradLower_iff propext,Classical.choice,Quot.sound
AUDIT OscInt.API.hessDet_eq_det propext,Classical.choice,Quot.sound
AUDIT OscInt.API.nonStationaryFE propext,Classical.choice,Quot.sound
AUDIT OscInt.API.stationaryPhaseFE propext,Classical.choice,Quot.sound
AUDIT-TOTAL 648 648
```

**4. Consumer example.** I did not run `lake build` inside `examples/consumer`. It has no `.lake`, so that would have created one and resolved packages while `make verify-all` was running on the same tree. I compiled the same file against the root environment instead.
- `lake env lean examples/consumer/ConsumerFormula.lean` exited 0 with no output, in about 5 s.
- A scratch copy, `/tmp/ppA/CF.lean`, adds `#print axioms`. Both `consumer_d4_formula` and `consumer_fold_formula` depend only on `[propext, Classical.choice, Quot.sound]`.

## Integrity checks
- **Statement files match the stamp.** I recomputed hashes and compared them with `stamps/20261107T101640Z-4acb308f54f4/manifest.txt` (stamp commit 4acb308). These files are byte-identical:
  - `OscInt/Statements/{Convert,D4,D4Limit,FrontEnd,StationaryPhase,VanDerCorput}.lean`
  - `Challenge.lean` and `Challenge/*.lean`
  - `comparator-API2.json`
- **`docs/statements.md` differs only by an appended clarification paragraph** (git diff from 4acb308 to 9e5540a: 10 added lines, nothing changed above them).
- **Commit order is consistent with statement-first.** The order is: stamp a610a7a, prompt 9385017, reviews 8a710fc, route e1e735d, proofs 9e5540a. Every proof file and `ConvertSanity.lean` is first added in 9e5540a.
- **The pins are present.** `stamps/pins.txt` pins all 14 statements and `challenge:comparator-API2.json` to the stamp. `comparator-API2.json` lists exactly the 14 theorem names, permits only the three standard axioms and has no definition names.
- **Nothing in the part files can change a statement's meaning.**
  - I read the declaration lists of `OscInt/API/Convert{Deriv,Disc,Fold,Norm}.lean` and `OscInt/API/Poly.lean`, the whole of `OscInt/API/Convert.lean`, the header and declaration list of `ConvertSanity.lean`, and the start of `docs/proof-API2.md`.
  - None of them contains an instance, attribute, notation, macro, `set_option`, axiom or opaque declaration, `sorry`, `native_decide` or `decide`. The only scoped commands are `open … in`.
  - The statement constants are defined in the unchanged stamped files, and StatementTypes checks each theorem's type by `Expr` equality against them. Bridge files can only add names, not redefine them.

## Verdicts against docs/statements.md
I checked each Lean type against the prose and against the base definitions `dd`, `ddd`, `hessDet`, `cubicCoeffs`, `cubicForm`, `disc`, `GradLower`, `IsCritical`, `FoldOrNondeg`, `AmpBound`, `oscInt2` and `lin`.

| # | Theorem | Verdict | Scope | Notes |
|---|---|---|---|---|
| C1 | `dd_iteratedFDeriv` | FAITHFUL | full | `dd Ψ k v w = fderiv (fun y => fderiv Ψ y v) k w`, which is D²Ψ(k)[w, v], equal to D²Ψ(k)[v, w] by symmetry under `ContDiffAt 2`. |
| C2 | `ddd_iteratedFDeriv` | FAITHFUL | full | The stated argument order holds by full symmetry for C³. |
| C3 | `hessDet_eq_det` | FAITHFUL | full | |
| C4 | `cubicCoeffs_eq` | FAITHFUL | full | Expanding D³[κ,κ,κ] gives the 1/6, 1/2, 1/2, 1/6 weights of `cubicCoeffs`. |
| C5 | `disc_eq_cubic_discr` | FAITHFUL | full | Definitional. |
| C6 | `disc_ne_zero_iff_isolated` | FAITHFUL | full | True as stated, including q = 0. |
| C7 | `foldOrNondeg_iff` | FAITHFUL | full | Both the span and the rank forms are proved. |
| C7′ | `foldOrNondeg_of_hasFDeriv` | FAITHFUL | full | An iff; the global `HasFDerivAt` is as documented in the clarification. |
| C8 | `gradLower_iff` | FAITHFUL | full | (i)–(iii) as stated, with `0 ≤ c` and differentiability at k. |
| C9 | `ampBound_conv` | FAITHFUL | full | |
| FE-S2.1 | `nonStationaryFE` | FAITHFUL | full | C depends only on N, Ψ, K, c. Uniform over every L with `c ≤ ‖DΨ(k) + L‖` (max-norm dual) on K. Bound `C*M/m^N`. |
| FE-S2.2 | `stationaryPhaseFE` | FAITHFUL | full | K′ is a compact set of functionals; the condition is det ≠ 0 at critical points k ∈ K, L ∈ K′. |
| FE-S3 | `foldFE` | FAITHFUL | full | `FoldOrNondegMatrix` at every k ∈ K; bound `C*M*m^(-5/6)`. |
| FE-S4.1′ | `d4BoundFE` | FAITHFUL | full | The coefficient identity, `Cubic.discr ≠ 0`, δ > 0, uniform over all L and t ≥ 1, closed ball in the max norm. No ∇φ(0) = 0 hypothesis, as in S4.1′. |

## Do the front ends go through their frozen statements?
In `OscInt/API/Convert.lean`, each front end calls its frozen theorem and only conversions besides:
- **`nonStationaryFE`** calls `OscInt.nonStationary` with the one-point family `Unit`, via `sanity_familyCk_const`. It feeds in `c/√2` through `gradLower_iff` part (iii) and `NormAux.fderiv_add_lin`.
- **`stationaryPhaseFE`** calls `OscInt.stationaryPhase` with `vecOf '' K'`, which is compact by continuity. It uses `hessDet_eq_det` and `isCritical_iff`.
- **`foldFE`** calls `OscInt.fold` with `Unit` and `vecOf '' K'`. It uses `foldOrNondeg_iff`.
- **`d4BoundFE`** calls `OscInt.d4BoundNe`. It uses `dd_iteratedFDeriv`, `cubicCoeffs_eq`, `coeffs_eq_of_forms` and `disc_eq_cubic_discr`.

The integral is rewritten to `oscInt2` with `p = vecOf L` by `lin_apply_functional`, a pointwise identity. The four frozen theorems are TYPE-OK against their own stamped statements. Nothing else enters that could change the meaning, and in any case the types are fixed by `Expr` equality.

## Acceptance criterion (examples/consumer/ConsumerFormula.lean)
**Met.**
- **`consumer_d4_formula`** applies FE-S4.1′ to φ(x, y) = x³ − 3xy² + x⁴, the elliptic umbilic with `Cubic.discr = 108` and coefficients (1, 0, −3, 0) in the stated order.
- **`consumer_fold_formula`** applies FE-S3 to Ψ(x, y) = x³ + y² on the unit ball, uniformly over the operator-norm unit ball of functionals.
- **The statements are clean.** Both theorems have no hypotheses, and their statements mention only Mathlib terms (`ContDiff`, `tsupport`, `iteratedFDeriv`, `Metric.closedBall`, `Complex.exp`, `∫`) plus the user's own `def`s of the phases. `dd`, `ddd`, `AmpBound` and `cubicCoeffs` appear nowhere in the file.
- **The proofs use project helpers internally.** They use the P2 helpers (`OscInt.API.Poly`) and the project definitions `hessianMatrix` and `FoldOrNondegMatrix`, the latter being the stamped Mathlib-idiom form. This is allowed by the criterion.
- **The file compiles** and its two theorems use standard axioms only.

## Findings
**MINOR 1 (non-vacuity coverage short of what was accepted).**
- Pre-proof referee B's MINOR 4, marked "Accepted" in `review/2026-11-07-API2-pre-proof-answers.md`, asked for three checks: C8 on gradient (3, 4) (max-dual norm 7, Euclidean norm 5), C7′ with explicit D₁, D₂, D₃, and an FE-S2.1 gradient-hypothesis instance with its bite.
- None of these is in `OscInt/API/ConvertSanity.lean` or the consumer example. `nonStationaryFE`, `stationaryPhaseFE` and `foldOrNondeg_of_hasFDeriv` are never applied to an explicit phase anywhere in the tree.
- Their hypotheses are plainly satisfiable, so this does not affect fidelity. But the disposition overstates what was done. Either add these instances or correct the disposition.

**MINOR 2 (order claim not supported by git).**
- The answers file says `ConvertSanity.lean` was added "before any batch-2 proof".
- In git, `ConvertSanity.lean` and all proof files are first added in the same commit, 9e5540a, so git cannot show the order.
- The file's content is independent of the bridges: it imports only `Statements.Convert`, `D4.Sanity` and `StationaryPhase.Implicit`, and uses no batch-2 theorem. Even so, the "before" claim should be worded as unverifiable from the history, or backed by a timestamp.

**NIT 3.** `ConsumerFormula.lean` is not a default target that `make verify-all` checks unless the consumer `lakefile.toml` path is exercised. The file does add it to `defaultTargets`; the final record should confirm that the replay actually built it.

**NIT 4.** In `foldFE`, the uniform statement S3 is used with the one-point family `Unit`. The front end is therefore strictly the single-phase case, as documented. Restated only so the record is explicit.

**NIT 5.** I compiled the consumer file from the repository root (`lake env lean examples/consumer/ConsumerFormula.lean`), not from `examples/consumer` after `lake build`. I did this to avoid creating `examples/consumer/.lake` during the concurrent `make verify-all`. The import is the same `OscInt`, but the separate-package path (`require … path = "../.."`) was not exercised by me.

Scratch files I wrote: `/tmp/ppA/st.out`, `/tmp/ppA/ax.out`, `/tmp/ppA/CF.lean`. No repository files, git state or `build/` were modified.