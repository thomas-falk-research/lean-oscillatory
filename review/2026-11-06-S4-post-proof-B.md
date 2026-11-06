<!-- Post-proof review of S4.1, referee B (fresh-context agent, prompt review/prompts/S4-post-proof.md), commit a776d28. Verbatim final report. -->

# Referee B: post-proof fidelity review of S4.1 (`OscInt.d4Bound`), commit a776d28

`OscInt.d4Bound` proves exactly the stamped `D4BoundStatement`. I found no BLOCKER or MAJOR issue.

**Verdict for `OscInt.d4Bound : OscInt.Statements.D4BoundStatement`:**
- **Against `docs/statements.md` S4.1:** FAITHFUL.
- **Against the classical results:** FAITHFUL-WEAKER, because it covers the hyperbolic umbilic (D4⁺) only. On regularity it is stronger than the classical C^∞ setting (C⁴ phase, C² amplitude).
- **Scope:** `full` for S4.1. S4 as a whole remains `part`, because S4.2 is not stated.
- **Pinned to:** commitment `5205ebc0a6a6286803155f16135a6405e8217037c93cb17ff876a9ec2902cdfd` (`OscInt.Statements.D4BoundStatement`), stamp `stamps/20261106T033706Z-63564a8d78cd`.

## Commands (repository root, `nice -n 10`, one Lean process at a time), verbatim output

1. `git rev-parse HEAD`
```
a776d28861175f299dfc2adff34661c892c945b9
```
2. `lake env lean StatementTypes.lean`
```
TYPE-OK OscInt.vanDerCorput_one : OscInt.Statements.VdC1Statement
TYPE-OK OscInt.vanDerCorput_two : OscInt.Statements.VdC2Statement
TYPE-OK OscInt.vanDerCorput_three : OscInt.Statements.VdC3Statement
TYPE-OK OscInt.nonStationary : OscInt.Statements.NonStationaryStatement
TYPE-OK OscInt.stationaryPhase : OscInt.Statements.StationaryPhaseStatement
TYPE-OK OscInt.fold : OscInt.Statements.FoldStatement
TYPE-OK OscInt.d4Bound : OscInt.Statements.D4BoundStatement
```
3. `cat build/commit/commitments.txt` (the file is present, mtime Nov 6 06:51)
```
2650f1484b3252166e9442f383ad734075f60f180d595c7d6729d9737edba5ad  OscInt.Statements.FoldStatement
a837c8bd8352929aa4ba6456ff19603cd34f7ae09b2896de0af2565fd0f803b4  OscInt.Statements.VdC1Statement
66cc331de7d7bf5fb38076895ff7014f280b41cced6492f70cd87134a78a39f5  OscInt.Statements.VdC2Statement
30b3f96ca215778d4034c6ca660818b04a842bb4b574f27f4a648a64bf9ab4f4  OscInt.Statements.VdC3Statement
5205ebc0a6a6286803155f16135a6405e8217037c93cb17ff876a9ec2902cdfd  OscInt.Statements.D4BoundStatement
238318a74792495f2009807e724673e80c4d3f66b91580c564105d84396fe8f8  OscInt.Statements.NonStationaryStatement
283a23fe63ba052ba6600edd08ee3def6d728a75dbbaa6d7f39fc031fc9eccff  OscInt.Statements.StationaryPhaseStatement
```
   - **Comparison with the stamp:** the S4.1 line (`5205ebc0…2cdfd`) equals the `commitment … OscInt.Statements.D4BoundStatement` line of `stamps/20261106T033706Z-63564a8d78cd/manifest.txt`. The other six commitments also equal their manifest lines.
   - **Which commit it was computed on:** this `build/commit` was produced by `make verify-all` on a0b1fde, as `docs/replay/2026-11-06-S4-verify-all.txt` records, not on a776d28 itself. `git diff --stat a0b1fde a776d28` touches only `docs/STATUS.md`, `docs/replay/*` and `review/prompts/*`, with no Lean or configuration file. The commitment therefore applies unchanged to a776d28; I did not recompute it.
4. `lake env lean Axioms.lean | grep -E 'OscInt\.d4Bound |AUDIT-TOTAL'`
```
AUDIT OscInt.d4Bound propext,Classical.choice,Quot.sound
AUDIT-TOTAL 365 365
```

## Integrity of the statement
- **Statement files match the stamp.** The sha256 of the current files equals the stamped manifest:
  - `OscInt/Statements/D4.lean`: `6965ce63…`
  - `OscInt/Statements/StationaryPhase.lean`: `cd43a116…`
  - `comparator-S4.json`: `44debf14…`
  - `Challenge/D4.lean`: `199f9c6a…`
- **Changes since the stamp.** `git diff 63564a8 HEAD` over `OscInt/Statements`, `Challenge*`, `comparator-S4.json`, `Axioms.lean`, the lakefile, the toolchain and the manifest shows only:
  - one added `#assert_type_is OscInt.d4Bound …` line in `StatementTypes.lean`;
  - in `docs/statements.md`, only the appended clarification paragraph. The stamped S4 text is byte-identical.
- **Recorded verify-all.** The verify-all log records PASS 8/8, including:
  - "challenge: export … S4.ndjson sha256 01c2722e… matches the stamped manifest";
  - "comparator: comparator-S4.json accepted against stamps/20261106T033706Z-63564a8d78cd";
  - leanchecker on every module, both export kernels, and nanoda.
  - I did not rerun these.

## What I looked at in the proof files
- **`OscInt/D4/Final.lean`:** `theorem d4Bound : Statements.D4BoundStatement := d4Bound_of …`. The type is the frozen constant, and `StatementTypes` confirms syntactic `Expr` equality.
- **Search for anything that could change meaning.** I grepped `OscInt/D4/*.lean` and `Blueprint/D4.lean` for `axiom`, `instance`, `attribute`, `set_option`, `macro`/`syntax`/`elab`/`notation`, `unsafe`/`opaque`, `@[`, `initialize`/`run_cmd`, `export`, `scoped`/`local`, `sorry`/`admit`/`implemented_by`. There were no hits apart from `namespace` lines. A wider grep over `OscInt/StationaryPhase`, `OscInt/VanDerCorput`, `OscInt/Basic.lean` and `Blueprint` for instances, attributes, simp attributes, notation and set_option also found nothing.
- **Definitions in the proof files:** only `smulEquiv`, `pieces`, `remFam` and `genCubic`, all in `OscInt.D4`. None shadows any `OscInt.Statements` name.
- **Import order.** The statement modules import only Mathlib (`StationaryPhase.lean`) or `StationaryPhase` (`D4.lean`). No downstream file can alter what `D4BoundStatement`, `oscInt2`, `dd`, `ddd`, `AmpBound`, `lin`, `cubicCoeffs` or `disc` mean.
- **Sanity files.** `OscInt/D4/Sanity.lean` and the sanity theorems in `Statements/D4.lean` only compute instances; they assert nothing about the statement's meaning.
- **Not read:** the analytic content of `Assembly.lean`, `Rescale.lean`, `Gauge.lean`, `Open.lean` and `Basic.lean`. I read the header of `Assembly.lean` only.

## Mathematical fidelity
- **Against `docs/statements.md`.** Each piece of S4.1 matches the Lean text:
  - C⁴ phase: `ContDiff ℝ 4 φ`.
  - D²φ(0) = 0: `∀ v w, dd φ 0 v w = 0`. These are genuine second derivatives for C⁴ φ.
  - Disc C < 0: `disc (cubicCoeffs φ) < 0`. The coefficients a = ∂₁₁₁/6, b = ∂₁₁₂/2, c = ∂₁₂₂/2, d = ∂₂₂₂/6 are correct. Argument order is irrelevant by symmetry of third derivatives, and `sanity_D4_generic` pins it on (1,2,3,5) with Disc −367. The discriminant is the standard one for binary cubics: x³+y³ gives −27, x³−3xy² gives 108.
  - Quantifiers: `∃ δ > 0, ∃ C` after φ and before A, M, y, t.
  - Amplitude: `AmpBound 2 (closedBall 0 δ)`, which is the max-norm square.
  - Linear term: y ∈ ℝ² is unrestricted.
  - Time: `1 ≤ t`.
  - Bound: `C * M * t ^ (-(2:ℝ)/3)`, with rpow on t ≥ 1.
  - **Not vacuous:** `sanity_D4_hyps` and `sanity_D4_generic` exhibit admissible phases; nonzero amplitudes exist; and `AmpBound` forces M ≥ 0.
  - **Integral is genuine:** the integrand is continuous with compact support, so the Bochner integral never takes Lean's default value 0.
- **Against the classical result.**
  - At a D4 point, the uniform t^{-2/3} estimate holds under all linear perturbations; this is the oscillation index of D4 (Duistermaat; Varchenko/Karpushkin uniform estimates).
  - The theorem is exactly this estimate for D4⁺ (Disc < 0), with uniformity over every y ∈ ℝ². The absent ∇φ(0) = 0 hypothesis is a strengthening, absorbed by y ↦ y + t∇φ(0).
  - D4⁻ (Disc > 0, e.g. x³ − 3xy², which `sanity_D4_elliptic_excluded` checks is excluded) is not covered. Hence FAITHFUL-WEAKER in scope.
  - The regularity hypotheses (C⁴ phase, C² amplitude) are weaker than the classical C^∞ setting, so the result is stronger on that axis. This does not change the verdict, which is driven by scope.
  - The exponent 2/3 is sharp (y = 0, A(0) ≠ 0), so the bound is not weaker than the classical one in strength.

## Findings
- **BLOCKER:** none.
- **MAJOR:** none.
- **MINOR 1 (scope, owner decision; known).** `disc < 0` excludes the elliptic umbilic D4⁻, for which the same classical t^{-2/3} bound holds. The post-stamp clarification in `docs/statements.md` now records this and leaves widening to `disc ≠ 0` as an owner option. Any citation of `OscInt.d4Bound` should say "hyperbolic umbilic D4⁺", not "D4".
- **MINOR 2 (provenance of the brief's wording).**
  - The stamped S4 text says the brief's condition is "C has an isolated critical point"; that condition is equivalent to Disc ≠ 0.
  - The post-stamp clarification says the brief reads "negative discriminant", with the constant Γ(1/3)²/(√3|Disc|^{1/6}).
  - The brief is not in the repository, so I could not check which wording is right.
  - If the brief's only hypothesis is the isolated critical point, the theorem is narrower than the brief. If it is the negative discriminant, the theorem is exactly the brief's case.
  - The owner should confirm the wording, or a quotation of the brief should be added.
- **NIT 1.** The `commitments.txt` used here was built on a0b1fde, not on HEAD a776d28. This is harmless because the diff between them is documentation only, but the record should say so explicitly. `docs/replay/2026-11-06-S4-verify-all.txt` does name a0b1fde.
- **NIT 2.** The header and the stamped md still say "implied by Disc C < 0" for the isolated-critical-point property without the converse. The clarification now supplies the converse; nothing to change in the frozen text.

I wrote nothing in the repository; I created no scratch files.