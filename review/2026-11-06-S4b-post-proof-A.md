<!-- Post-proof review of S4.1', S4.2, S4.3, referee A (fresh-context agent, prompt review/prompts/S4b-post-proof.md), commit f35f35e. Verbatim final report. -->

# Post-proof fidelity review, referee A: S4.1′ (`OscInt.d4BoundNe`), S4.2 (`OscInt.d4Limit`), S4.3 (`OscInt.d4ConstantPos`)

Commit under review: f35f35e. I wrote nothing in the repository. I ran Lean one process at a time with `nice -n 10`. My only scratch file was `/tmp/claude-0/-home-user-lean-oscillatory/ce808543-6e2d-583b-be8e-5671768737ef/scratchpad/gf.lean`, used to check that `GammaFree.lean` really sees proof bodies.

## Summary

- **No BLOCKER and no MAJOR findings.** All three theorems have exactly the frozen statement types. Their axioms are only propext, Classical.choice and Quot.sound.
- The pinned commitments match the stamp manifest. The proof files do nothing that could change what the statements mean.
- `GammaFree.lean` really follows proofs, including the proofs of imported Mathlib lemmas.
- **What remains unproved for the brief's S4 is S4.4**, the closed forms of the constant.

## Commands run (verbatim output)

**1. `git rev-parse HEAD`**
```
f35f35eb730845950473e227c539eb879f6c9978
```

**2. `lake env lean StatementTypes.lean`**
```
TYPE-OK OscInt.vanDerCorput_one : OscInt.Statements.VdC1Statement
TYPE-OK OscInt.vanDerCorput_two : OscInt.Statements.VdC2Statement
TYPE-OK OscInt.vanDerCorput_three : OscInt.Statements.VdC3Statement
TYPE-OK OscInt.nonStationary : OscInt.Statements.NonStationaryStatement
TYPE-OK OscInt.stationaryPhase : OscInt.Statements.StationaryPhaseStatement
TYPE-OK OscInt.fold : OscInt.Statements.FoldStatement
TYPE-OK OscInt.d4Bound : OscInt.Statements.D4BoundStatement
TYPE-OK OscInt.d4BoundNe : OscInt.Statements.D4BoundNeStatement
TYPE-OK OscInt.d4ConstantPos : OscInt.Statements.D4ConstantPosStatement
TYPE-OK OscInt.d4Limit : OscInt.Statements.D4LimitStatement
```
Before this I ran `lake build --no-build OscInt`, which printed `All targets up-to-date (9096 jobs).` (exit 0), so the compiled files match the sources.

**3. `cat build/commit/commitments.txt`**
```
2650f1484b3252166e9442f383ad734075f60f180d595c7d6729d9737edba5ad  OscInt.Statements.FoldStatement
a837c8bd8352929aa4ba6456ff19603cd34f7ae09b2896de0af2565fd0f803b4  OscInt.Statements.VdC1Statement
66cc331de7d7bf5fb38076895ff7014f280b41cced6492f70cd87134a78a39f5  OscInt.Statements.VdC2Statement
30b3f96ca215778d4034c6ca660818b04a842bb4b574f27f4a648a64bf9ab4f4  OscInt.Statements.VdC3Statement
5205ebc0a6a6286803155f16135a6405e8217037c93cb17ff876a9ec2902cdfd  OscInt.Statements.D4BoundStatement
9490bf1bdc254b2bd297cb0c4a7f76db64fa363ccf1141a92a14fd78331552a9  OscInt.Statements.D4LimitStatement
f4e245bd4b1a3f0ca2e8fb006f574568849b717c089099de66c70f91843d4292  OscInt.Statements.D4BoundNeStatement
96eb2416b768396e5f29e3bfc865d4f181c6ec9ccaf1f1ac0aaf01ef18053be1  OscInt.Statements.D4ConstantPosStatement
238318a74792495f2009807e724673e80c4d3f66b91580c564105d84396fe8f8  OscInt.Statements.NonStationaryStatement
283a23fe63ba052ba6600edd08ee3def6d728a75dbbaa6d7f39fc031fc9eccff  OscInt.Statements.StationaryPhaseStatement
3f089384d33ac7f6d4a24195c64b10af9093125fec7456da342a0477e510e6cc  OscInt.Statements.D4ConstantClosedFormStatement
```
- **Which commit:** the file is dated Nov 6 10:48. Per the replay record `docs/replay/2026-11-06-S4b-verify-all.txt`, it was computed by `make verify-all` on a71b318 (clean tree).
- **a71b318 vs f35f35e:** `git diff --stat a71b318 f35f35e` shows only docs/STATUS.md, the replay record and two review prompts.
- **Comparison with the stamp:** the pinned stamp is `stamps/20261106T081634Z-e2d7771c358e` (manifest commit e2d7771). It lists:
  - `commitment f4e245bd…53be1 D4BoundNeStatement`
  - `commitment 9490bf1b…52a9 D4LimitStatement`
  - `commitment 96eb2416…be1 D4ConstantPosStatement`

  These three lines are identical to the ones above. The replay record also prints "matches its stamp" for all three.
- **File hashes:** I recomputed the sha256 of `OscInt/Statements/D4Limit.lean` (722952f5…), `D4.lean` (6965ce63…), `StationaryPhase.lean` (cd43a116…), `Challenge/D4Limit.lean` (0e661c0a…) and the three comparator JSONs. All equal the manifest. No statement or challenge file changed between e2d7771 and f35f35e; only `GammaFree.lean` was added and `StatementTypes.lean` gained three lines.

**4. `lake env lean Axioms.lean | grep -E 'OscInt\.(d4BoundNe|d4Limit|d4ConstantPos) |AUDIT-TOTAL'`**
```
AUDIT OscInt.d4BoundNe propext,Classical.choice,Quot.sound
AUDIT OscInt.d4ConstantPos propext,Classical.choice,Quot.sound
AUDIT OscInt.d4Limit propext,Classical.choice,Quot.sound
AUDIT-TOTAL 458 458
```

**5. `lake env lean GammaFree.lean`**
```
GAMMA-FREE CONTROL Real.Gamma_pos_of_pos rejected as expected (33 forbidden constant(s))
GAMMA-FREE CONTROL gammaProofControl rejected as expected (33 forbidden constant(s))
GAMMA-FREE OK OscInt.Statements.D4ConstantPosStatement (33099 constants in the closure)
GAMMA-FREE OK OscInt.d4ConstantPos (43612 constants in the closure)
```
EXIT 0.

**Does the check really follow proofs?** Yes.
- **How it works:** `gammaClosureBad` walks the transitive closure of every constant reached through `ci.type` and `ci.value? (allowOpaque := true)`. It flags any name with a component containing `Gamma`, `Beta`, `betaIntegral`, `mellin` or `Mellin`.
- **Proof-only control:** `gammaProofControl : (0:ℝ) < 1` has a Gamma-free type and a proof that uses `Real.Gamma_pos_of_pos`. It is rejected, so local theorem bodies are followed.
- **Imported proofs:** I checked independently (scratch file `gf.lean`) whether imported theorem bodies are visible at this Lean version. For `Real.Gamma_pos_of_pos`, `MeasureTheory.integral_add`, `hasSum_zeta_two`, `OscInt.D4.cosIBP` and `OscInt.d4ConstantPos`:
  - `value? (allowOpaque := true)` returns `some`;
  - plain `value?` returns `none`, confirming the lesson-18 note.

  So the walk goes through proofs in Mathlib modules too, not only through local ones.
- **Remaining limits:** the check is name-based, and values of `opaque` constants are not followed. I grepped `OscInt/D4/*.lean`: there is no `opaque`, `axiom`, `unsafe`, `extern`/`implemented_by`, `instance`, `attribute`, `macro`/`elab`/`syntax`/`notation`, `sorry` or `native_decide`. The only new `def`s are `smulEquiv`, `pieces`, `sinInt`, `sinPartial`, `piecesAt`, `psi`, `radialPrim`, `remFam` and `genCubic`; none hides a Gamma-type integral.

**Method of the S4.3 proof.** I read `OscInt/D4/ConstantPos.lean` and the list of theorems in `CosMoment.lean`. The proof integrates by parts once (`cosIBP`), then pairs the humps of sin u·u^{−4/3} over each period [2nπ, 2nπ+2π] (`sinInt_add_sinInt_add_pi_pos`, `integral_period_pos`, `sinPartial_period_mono`). This is the alternating-series argument as revised in the dated clarification of `docs/statements.md`. The angular part goes through simple zeros (`circleNondeg`, `singularPower`, `angularPos`).

**Proof files I looked at, and only to check meaning:**
- I read in full `Final.lean`, `LimitFinal.lean`, `ConstantPosFinal.lean`, `ConstantPos.lean`, `LimitSanity.lean`, and the relevant part of `Bite.lean`.
- I grepped all of `OscInt/D4/` for the meaning-changing constructs listed above.
- Since the types are checked by `Expr` equality against constants in the stamped statement files, and the comparator judges each theorem against the stamped challenge export, nothing in the proof files can change the statements.

**Replay record** (`docs/replay/2026-11-06-S4b-verify-all.txt`, a71b318):
- comparator-S41w, -S42 and -S43 accepted by six kernels each: Lean default, Lean paranoid, lean4lean, nanoda, con-leche, con-ron;
- per-module `leanchecker` PASS, and the full-export replay PASS in six kernels;
- stamp-verify PASS;
- overall `RESULT INCOMPLETE`, only because comparator-S44 has no theorem yet.

## Verdicts

The verdicts below are against `docs/statements.md` and against the brief as quoted in the decision record and review prompt ("∇²φ = 0, C has an isolated critical point and negative discriminant … t^{2/3}∫e^{itφ}A → c_C A(0), c_C = Γ(1/3)²/(√3|Disc C|^{1/6}) ≠ 0; c_C ≠ 0 via ∫₀^∞ cos u·u^{−1/3} du > 0 by an alternating series, no Mellin/Gamma").

| Theorem | vs `docs/statements.md` | vs brief | Scope | Pinned commitment |
|---|---|---|---|---|
| `OscInt.d4BoundNe` | FAITHFUL | FAITHFUL-STRONGER (Disc ≠ 0: covers D4⁺ and D4⁻; C⁴ phase) | full | `f4e245bd4b1a3f0ca2e8fb006f574568849b717c089099de66c70f91843d4292` |
| `OscInt.d4Limit` | FAITHFUL | FAITHFUL-STRONGER in its hypotheses (Disc ≠ 0), but the constant is the Gamma-free c_C = I·J/3 | full for S4.2; **part** of the brief's limit-with-closed-form (needs S4.4) | `9490bf1bdc254b2bd297cb0c4a7f76db64fa363ccf1141a92a14fd78331552a9` |
| `OscInt.d4ConstantPos` | FAITHFUL | FAITHFUL-STRONGER (convergence and c_C > 0, not only ≠ 0; for every q with Disc ≠ 0); proof mechanically Gamma/Beta/Mellin-free | full | `96eb2416b768396e5f29e3bfc865d4f181c6ec9ccaf1f1ac0aaf01ef18053be1` |

**Reasons for the verdicts:**
- **S4.1′ statement:** it differs from the stamped `D4BoundStatement` only in `< 0` → `≠ 0`, which I checked with `diff`. The δ and C are chosen before A, M, y and t. The bound is uniform in y ∈ ℝ².
- **Disc ≠ 0 matches "isolated critical point":** for a binary cubic, Disc = 0 exactly when there is a repeated or vanishing factor, and then the critical set is a line (e.g. x²y has Disc = 0).
- **The constant in S4.2:** I re-derived it. With r dr = (1/3)(t|C(θ)|)^{−2/3} u^{−1/3} du, polar coordinates give (1/3) t^{−2/3} ∫₀^{2π} |C(θ)|^{−2/3} (I ± iS) dθ. The sine parts cancel because C(θ+π) = −C(θ), leaving c_C = I·J/3.
- **The cubic coefficients:** `cubicCoeffs` gives b = ∂₁₁₂φ/2 and c = ∂₁₂₂φ/2, and `cubicForm_cubicCoeffs_genCubic` confirms it reproduces the cubic part for all coefficient values.
- **Hypotheses of S4.2:** φ(0) = 0 and ∇φ(0) = 0 are needed for the limit to exist without a phase factor. The amplitude support B̄(0, δ) with δ existential is "A supported near 0".
- **No junk values:** S4.3 proves that `cosMomentPartial` converges to `cosMoment` (so `limUnder` is the genuine limit) and that the angular integrand is integrable for Disc ≠ 0. So `d4Constant` is the real number intended, and it is > 0.
- **S4.2 is not vacuous:** `ampBound_exists_delta` gives an amplitude with A(0) = 1 for every δ, so the conclusion has content.

## What remains unproved for the brief's S4 (S4.4)

`D4ConstantClosedFormStatement` has no proof; `comparator-S44.json` reports "no challenge theorem is declared yet". It says:
- I = Γ(2/3)/2;
- c_C = Γ(1/3)²/(√3|Disc|^{1/6}) for Disc < 0;
- c_C = Γ(1/3)²/Disc^{1/6} for Disc > 0.

Consequences:
- The brief's limit with its explicit constant Γ(1/3)²/(√3|Disc C|^{1/6}) is **not** machine-checked. What is machine-checked is the limit with the Gamma-free c_C = (1/3)·∫₀^∞ cos u·u^{−1/3} du·∫₀^{2π}|C(cos θ, sin θ)|^{−2/3} dθ, and c_C > 0.
- The brief's S4 as a whole is S4.2 ∧ S4.4 (Disc < 0 clause) ∧ S4.3, and is therefore still open.
- `make verify-all` cannot report PASS until S4.4 is proved.

## Findings

**MINOR 1 (stale status documents at f35f35e).**
- `README.md`, row "S4.2–S4.4 …", still says "proofs not started", and the S4.1′ row says "post-proof review not yet run".
- The last paragraph of `docs/STATUS.md` (S4.1′–S4.4) still says "none is proved yet".
- The table rows of STATUS.md are current; these prose lines contradict them. Both need updating before any citation; the README row should say S4.2 and S4.3 are proved and S4.4 is open.

**MINOR 2 (the claim must name S4.4 as open).** Any status line for `d4Limit` should say it is the limit with the Gamma-free c_C. The brief's closed-form constant needs S4.4, which is unproved. STATUS.md says this in the pairing sentence, but the S4.2 row headline "t^{2/3}∫e^{itφ}A → c_C A(0)" could be read as the brief's statement.

**NIT 3 (`GammaFree.lean` header).** The module docstring contains a broken inline-code span: "Negative control: `#assert_gamma_free_expect_fail Real.Gamma_pos_of_pos" is not closed until after a pasted copy of the control theorem, which ends with "gammaProofControl`." The code lines actually run are correct. The header's baseline "(referee B, 33 082 constants)" differs from today's 33 099, presumably because proof bodies are now followed. Neither affects the check.

**NIT 4 (limits of the Gamma-free check).** The check is name-based and does not follow `opaque` values. Both limits are recorded in the answers file, and I confirmed neither is exercised by the D4 files. The "alternating series" part of the brief's method rule is not checkable by machine; my reading of `CosMoment.lean` confirms the IBP-plus-hump-pairing route described in the dated clarification.

**NIT 5 (record result).** The replay record's overall result is `RESULT INCOMPLETE` (exit 2), because S4.4 has no proof yet. The S4.1′/S4.2/S4.3 evidence rests on the per-configuration lines ("comparator-S41w/S42/S43.json accepted against stamps/20261106T081634Z-e2d7771c358e"). That is sufficient, but a citation should quote those lines rather than the overall result.
