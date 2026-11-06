<!-- Post-proof review of S4.1, referee A (fresh-context agent, prompt review/prompts/S4-post-proof.md), commit a776d28. Verbatim final report. -->

# Post-proof fidelity review of S4.1 (`OscInt.d4Bound`), referee A

**Bottom line:** `OscInt.d4Bound` is **FAITHFUL** to `docs/statements.md` S4.1 and **FAITHFUL-WEAKER** than the classical D4 result. Its scope is **`full`** for S4.1 (S4 as a whole is `part`, because S4.2 is not stated). The verdict is pinned to commitment **`5205ebc0a6a6286803155f16135a6405e8217037c93cb17ff876a9ec2902cdfd`** (stamp `stamps/20261106T033706Z-63564a8d78cd`). There are no BLOCKER or MAJOR findings.

I wrote nothing in the repository. I ran one Lean process at a time under `nice -n 10`, and waited for another referee's `Axioms.lean` run to finish before starting mine.

## What I read
- `docs/statements.md`: S2, S3 and S4, including the clarification after the S4.1 stamp.
- `OscInt/Statements/D4.lean` and `OscInt/Statements/StationaryPhase.lean`.
- `OscInt/D4/Final.lean`, `OscInt/D4/Sanity.lean`, `StatementTypes.lean`, `comparator-S4.json`, `Challenge/D4.lean`.
- `stamps/pins.txt` and the pinned stamp's `manifest.txt`.
- `review/2026-11-06-S4-pre-proof-A.md`, the findings lines of `-B.md` and of `-answers.md`.
- `docs/replay/2026-11-06-S4-verify-all.txt`, the comparator, commit and TYPE-OK lines only.

## Commands (verbatim output)
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
   - **Comparison with the pinned manifest:** the S4.1 line `5205ebc0…2cdfd OscInt.Statements.D4BoundStatement` is identical to the manifest's `commitment 5205ebc0a6a6286803155f16135a6405e8217037c93cb17ff876a9ec2902cdfd  OscInt.Statements.D4BoundStatement`.
   - The other six lines also equal the manifest's commitment lines.
   - **Extra checks I ran:** the working-tree hashes of these four files equal the manifest entries:
     - `OscInt/Statements/D4.lean`: `6965ce63…`
     - `OscInt/Statements/StationaryPhase.lean`: `cd43a116…`
     - `Challenge/D4.lean`: `199f9c6a…`
     - `comparator-S4.json`: `44debf14…`
   - `git diff --stat 63564a8 HEAD` over `OscInt/Statements`, `Challenge*` and `comparator-S4.json` is empty.
4. `lake env lean Axioms.lean | grep -E 'OscInt\.d4Bound |AUDIT-TOTAL'`
```
AUDIT OscInt.d4Bound propext,Classical.choice,Quot.sound
AUDIT-TOTAL 365 365
```

## Verdict for `OscInt.d4Bound`
**Against `docs/statements.md` S4.1: FAITHFUL.** Each part of the stamped text is in the Lean statement:
- The hypotheses: a C⁴ phase (`ContDiff ℝ 4 φ`), D²φ(0) = 0 (`∀ v w, dd φ 0 v w = 0`), and `disc (cubicCoeffs φ) < 0`.
- The constants come as `∃ δ > 0, ∃ C`, chosen after φ and before A, M, y, t.
- The amplitude condition is `AmpBound 2 (closedBall 0 δ) A M`, with `y ∈ ℝ²` unrestricted and `1 ≤ t`.
- The bound is `‖∫ exp((tφ(κ) + y·κ) i) A(κ) dκ‖ ≤ C·M·t^(-2/3)`.

I re-checked the conventions:
- **Cubic coefficients:** a = ∂₁₁₁/6, b = ∂₁₁₂/2, c = ∂₁₂₂/2, d = ∂₂₂₂/6 are the coefficients of (1/6)D³φ(0)[κ³]. The order of arguments to `ddd` does not matter for a C³ function. `sanity_D4_generic` pins this on the cubic (1, 2, 3, 5).
- **Discriminant:** `disc` is the standard binary-cubic discriminant. x³+y³ gives −27, i.e. D4⁺. `sanity_D4_elliptic_excluded` shows x³−3xy² gives +108, i.e. D4⁻, which is excluded.
- **No vacuity:** `AmpBound` forces M ≥ 0. The integrand is continuous with compact support, so the Bochner integral is genuine. The hypotheses are satisfiable (`sanity_D4_hyps`, `sanity_D4_generic`).
- **Gradient at 0:** leaving out ∇φ(0) = 0 is legitimate because y ↦ y + t∇φ(0) absorbs it, and y is unrestricted.
- **Power:** `t ^ (-(2:ℝ)/3)` is `Real.rpow` with t ≥ 1.

**Against the classical results: FAITHFUL-WEAKER.**
- The classical uniform t^{-2/3} bound (Duistermaat; Karpushkin's stability for simple singularities) holds at every D4 point, i.e. whenever Disc ≠ 0. The statement covers only the hyperbolic umbilic D4⁺ (Disc < 0). This is deliberate and documented in the post-stamp clarification; widening it is an owner option.
- Within D4⁺ it is the classical uniform bound. Its regularity hypotheses are milder than the usual C^∞ setting: a C⁴ phase and a C² amplitude with a C²-type constant. The exponent is sharp, so on that axis the statement is at least as strong as the textbook one.

**Scope:** `full` for S4.1. S4 as a whole is `part`, because S4.2 (the limit constant c_C) is not stated yet.

## Whether the proof files can change the meaning of the statement
- **Files read:** `OscInt/D4/Final.lean` and `OscInt.lean` in full, plus a grep over all of `OscInt/D4/*.lean`.
- **What the grep looked for:** `axiom`, `instance`, `attribute`, `set_option`, `notation`, `macro`, `syntax`, `elab`, `opaque`, `@[`, `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `ofReduceBool`, top-level `def`/`abbrev`.
- **Findings:** no match outside `Sanity.lean`, apart from three auxiliary `noncomputable def`s used inside proofs: `smulEquiv` and `pieces` in `Assembly.lean`, and `remFam` in `Rescale.lean`. None of these touch the statement constants.
- **Why the meaning is fixed:**
  - `#assert_type_is` checks syntactic `Expr` equality of `d4Bound`'s type with the constant `D4BoundStatement`.
  - The statement file is byte-identical to the stamped one.
  - The verify-all record shows `comparator: comparator-S4.json accepted against stamps/20261106T033706Z-63564a8d78cd` and leanchecker accepting every `OscInt.D4.*` module.
- **Conclusion:** nothing in the proof files can alter what is proved.

## Findings
- **BLOCKER:** none.
- **MAJOR:** none.
- **MINOR-1 (scope, carried over from both pre-proof referees and already documented):**
  - `disc < 0` keeps only D4⁺. The classical theorem, and "isolated critical point", correspond to `disc ≠ 0`.
  - The documented route would cover D4⁻ through the `hessDet ≠ 0` branch of `FoldOrNondeg`, but that would need a new statement and a new stamp.
  - This does not affect fidelity to the docs. It is the reason for FAITHFUL-WEAKER against the classical result.
- **NIT-1 (provenance wording):**
  - `build/commit/commitments.txt` (mtime 06:51) was produced by `make verify-all` on a0b1fde (committed 06:09), as `docs/replay/2026-11-06-S4-verify-all.txt` line 1 states. It was not produced on a776d28 itself (committed 07:14).
  - `git diff --stat a0b1fde a776d28` touches only `docs/STATUS.md`, two replay records and two review prompts, none of which enter a commitment. So the hash applies to a776d28, but the record should say "on a0b1fde" rather than "on this commit".
- **NIT-2:** the remaining pre-proof NIT is still open: no sanity theorem shows amplitudes exist for every δ (`sanity_ampBound_exists` is fixed at radius 1). The fact is mathematically obvious and does not affect the verdict.