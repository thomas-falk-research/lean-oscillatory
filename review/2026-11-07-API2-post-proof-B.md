9e5540ac7a07bd677156575352bbdc708aaea87b

# Post-proof referee B (ppB): front-end batch 2 (API2)

## Read this first: my run broke one replay step
My scratch Lean run (`/tmp/ppB/FEdeps.lean`, `import OscInt` plus a constant dump) ran at the same time as `make verify-all`. The kernel's memory-cgroup OOM killer then killed the replay's `leanchecker` process. The `make verify-all` log (`/tmp/claude-0/-home-user-lean-oscillatory/fcbe6bfc-8b3f-5437-8e7d-78671c19013e/scratchpad/verify-all-9e5540a.log`) now shows:
`FAIL  leanchecker OscInt.API  (59.5s)  non-zero exit:`
dmesg shows `Memory cgroup out of memory: Killed process 28315 (leanchecker) total-vm:28766180kB, anon-rss:13472120kB`. This FAIL comes from my memory use, not from the repository. `leanchecker OscInt.API` (or the whole `lean-replay`) must be rerun on its own before the replay record for 9e5540a is used. The other API2 modules passed in that log: Convert, ConvertDeriv, ConvertDisc, ConvertFold, ConvertNorm, ConvertSanity, Poly, Sanity.

Second side effect, already undone: `lake env` in `examples/consumer` started fetching dependencies and created the git-ignored `examples/consumer/.lake/` (198 MB, no Mathlib build). The Makefile has no `consumer` target, so `make` does not use that directory. I deleted it, which restores the earlier state. `git status --short` is empty again.

## Commands, verbatim
**1.** `git rev-parse HEAD` → `9e5540ac7a07bd677156575352bbdc708aaea87b`. `git status --short` → empty, so the tree is clean.

**2.** `lake env lean StatementTypes.lean | grep …` (exit 0):
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

**3.** `lake env lean Axioms.lean | grep …` (exit 0):
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

**4.** `cd examples/consumer && lake env lean ConsumerFormula.lean` did not run. That package has no built Mathlib: lake fetched the dependencies and then reported `error: unknown module prefix 'Mathlib'`, exit 1. Building Mathlib there would take hours, so I did not run `lake build`.
- Instead I ran `lake env lean /tmp/ppB/ConsumerFormula.lean` from the repository root on a byte-identical copy. The file imports only `OscInt`, so this checks the same thing. Result: exit 0, no output, 6 s.
- With `#print axioms` appended (`/tmp/ppB/CF2.lean`), both `consumer_d4_formula` and `consumer_fold_formula` depend only on `[propext, Classical.choice, Quot.sound]`.
- This is not the downstream-package build CI does. That build was not reproduced here.

## Integrity checks
- At 9e5540a, these files have the same SHA-256 as in `stamps/20261107T101640Z-4acb308f54f4/manifest.txt`: `OscInt/Statements/{Convert,FrontEnd,StationaryPhase,D4,D4Limit}.lean`, `Challenge/Convert.lean`, `Challenge.lean`, `comparator-API2.json`, `Axioms.lean`.
- Two files changed since the stamp, both by appending only:
  - `docs/statements.md`: the post-stamp clarification paragraph.
  - `StatementTypes.lean`: 14 `#assert_type_is` lines.
- `stamps/pins.txt` lines 26–40 pin all 14 statements and `challenge:comparator-API2.json` to the stamp.
- `comparator-API2.json` lists exactly the 14 theorem names. It has `definition_names: []` and permits only the three standard axioms.
- `Challenge/Convert.lean` states the same 14 names over the frozen statement constants, each closed by `sorry`.

## What I read to check that no proof file can change a statement's meaning
Files: `OscInt/API/Convert.lean`, `ConvertDeriv.lean`, `ConvertDisc.lean`, `ConvertFold.lean`, `ConvertNorm.lean`, `Poly.lean`, and `docs/proof-API2.md` (grep only).
- None of these files has `instance`, attributes (`@[`), `macro`/`elab`/`syntax`/`notation`, `set_option`, `axiom`, `opaque`, `unsafe`, `implemented_by`, `sorry` or `native_decide`.
- New definitions are only `DiscAux.cx`/`cy`, `NormAux.coordProd`/`linCLM` and `ConvertAux.vecOf`, all in sub-namespaces.
- The statements are elaborated in `OscInt/Statements/Convert.lean`, which imports only `FrontEnd`. Later files cannot change them, and StatementTypes compares the theorem types by syntax.

## Verdicts (against `docs/statements.md`, "Front end, batch 2")
| # | Theorem | Verdict | Scope |
|---|---|---|---|
| C1 | `dd_iteratedFDeriv` | FAITHFUL | full |
| C2 | `ddd_iteratedFDeriv` | FAITHFUL | full |
| C3 | `hessDet_eq_det` | FAITHFUL | full |
| C4 | `cubicCoeffs_eq` | FAITHFUL | full |
| C5 | `disc_eq_cubic_discr` | FAITHFUL | full |
| C6 | `disc_ne_zero_iff_isolated` | FAITHFUL | full |
| C7 | `foldOrNondeg_iff` | FAITHFUL | full |
| C7′ | `foldOrNondeg_of_hasFDeriv` | FAITHFUL | full |
| C8 | `gradLower_iff` | FAITHFUL | full |
| C9 | `ampBound_conv` | FAITHFUL | full |
| FE-S2.1 | `nonStationaryFE` | FAITHFUL | full |
| FE-S2.2 | `stationaryPhaseFE` | FAITHFUL | full |
| FE-S3 | `foldFE` | FAITHFUL | full |
| FE-S4.1′ | `d4BoundFE` | FAITHFUL | full |

Notes on the verdicts:
- C1: `dd` is ∂_w∂_v; `iteratedFDeriv_two_apply` gives ∂_v∂_w. They agree by symmetry for C², as the statement intends.
- C2: the doc states the same symmetry point.
- C5: the doc's dehomogenisation at κ₂ = 1 matches `Cubic.mk a b c d`.
- C6: "isolated" is written as `𝓝[≠] 0`, as documented.
- C7′: an iff with global `HasFDerivAt`, as the clarification records.
- C8: (i) is c² ≤ |g|₂² ⇔ c ≤ |g|₂ for c ≥ 0. (ii) is |g|₂ ≤ |g|₁. (iii) is |g|₁ ≤ √2·|g|₂.
- C9: (i) assumes `IsCompact K`.

## How each front end is proved
I dumped the `OscInt.*` constants each proof term uses (`/tmp/ppB/FEdeps.lean`). Each front end goes through exactly the frozen theorem it fronts, plus proved, axiom-clean conversions. Every imported theorem used has a type fixed by a stamped statement or is an auxiliary lemma with a concrete type.
- **`nonStationaryFE`** uses `OscInt.nonStationary` (one-point family `Unit`, constant c/√2).
  - Glue: `gradLower_iff` (C8 iii), `NormAux.fderiv_add_lin`, `ConvertAux.integral_eq_oscInt2` (by `simp only [oscInt2, vecOf, lin_apply_functional]`), `ConvertAux.vecOf`, `sanity_familyCk_const`.
- **`stationaryPhaseFE`** uses `OscInt.stationaryPhase` with K′ mapped to `vecOf '' K'`.
  - Glue: `hessDet_eq_det` (C3), `isCritical_iff`, `continuous_vecOf`, `integral_eq_oscInt2`.
- **`foldFE`** uses `OscInt.fold` (one-point family).
  - Glue: `foldOrNondeg_iff` (C7, the `.1` direction backwards), `sanity_familyCk_const`, `continuous_vecOf`, `integral_eq_oscInt2`.
- **`d4BoundFE`** uses `OscInt.d4BoundNe`.
  - Glue: `dd_iteratedFDeriv` (C1), `cubicCoeffs_eq` (C4), `coeffs_eq_of_forms` (evaluated at (1,0), (0,1), (1,1), (1,−1)), `disc_eq_cubic_discr` (C5), `integral_eq_oscInt2'`.
- Name resolution: `OscInt.API.OscInt.{nonStationary,fold,stationaryPhase,d4BoundNe}` and `OscInt.OscInt.nonStationary` do not exist. The references therefore resolve to the frozen theorems, whose types StatementTypes checks: `TYPE-OK OscInt.nonStationary : …NonStationaryStatement`, and likewise for the other three.

## Acceptance criterion (`examples/consumer/ConsumerFormula.lean`)
**Met.**
- `consumer_d4_formula` applies FE-S4.1′ (`d4BoundFE`) to φ(x, y) = x³ − 3xy² + x⁴, an explicit formula. It is the elliptic umbilic with discr = 108.
- `consumer_fold_formula` applies FE-S3 (`foldFE`) to Ψ = x³ + y². Here K is the max-norm unit ball and K′ is the unit ball of functionals; the fold condition is proved at every k.
- Both theorems are closed statements with no hypotheses. Their conclusions are written in Mathlib terms: `ContDiff`, `tsupport`, `iteratedFDeriv`, `Metric.closedBall`, CLMs.
- The proofs discharge the front-end hypotheses through the P2 helpers (`OscInt.API.Poly`), with `ring` and `fun_prop`.
- `dd`, `ddd`, `AmpBound` and `cubicCoeffs` appear nowhere in the file. Only the batch-2 definitions `FoldOrNondegMatrix`, `hessianMatrix` and `ofFin2` appear, as the FE-S3 hypothesis.
- The file elaborates and is axiom-clean, checked on the root-environment copy described in item 4.

## Findings
- **BLOCKER:** none.
- **MAJOR:** none against the repository. The replay FAIL of `leanchecker OscInt.API` described at the top must be rerun before it is recorded. It is caused by my process, not by the repository.
- **MINOR 1.** `make verify-all` does not elaborate `examples/consumer/ConsumerFormula.lean`: the Makefile has no `consumer` reference. Building `examples/consumer` here needs a full Mathlib build. The acceptance example is therefore checked only by CI or by hand; my check used the root environment. Consider either:
  - a Makefile target that elaborates it against the root build (`lake env lean examples/consumer/ConsumerFormula.lean`), or
  - recording which run checked it.
- **MINOR 2.** Both D4 checks have disc > 0 (elliptic):
  - the end-to-end consumer example;
  - `d4FE_hyps_elliptic` in `ConvertSanity`.

  The hyperbolic side (disc < 0) is checked only at the hypothesis level (`d4FE_hyps_generic`, disc = −367), not through `d4BoundFE`. That is a one-line addition.
- **NIT 1.** `review/2026-11-07-API2-pre-proof-answers.md` says the ‖L‖ = |L e₀| + |L e₁| helper is "in the bridges (`OscInt/API/Convert.lean`), with its two inequalities". It is actually `NormAux.norm_prod_functional` in `OscInt/API/ConvertNorm.lean`, stated as one equality.
- **NIT 2.** `Convert.lean` declares `theorem ConvertAux.coeffs_eq_of_forms` inside `namespace OscInt.API`, so its full name is `OscInt.API.ConvertAux.coeffs_eq_of_forms`. That matches the other ConvertAux lemmas, but it is declared away from that namespace block. Cosmetic.

Scratch files (all under `/tmp/ppB/`): `st.txt`, `ax.txt`, `ConsumerFormula.lean`, `CF2.lean`, `FEdeps.lean`.