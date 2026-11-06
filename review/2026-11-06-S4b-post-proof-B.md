<!-- Post-proof review of S4.1', S4.2, S4.3, referee B (fresh-context agent, prompt review/prompts/S4b-post-proof.md), commit f35f35e. Verbatim final report. -->

# Post-proof fidelity review B: S4.1′, S4.2, S4.3 (commit f35f35e)

**Summary.** All three proved theorems are faithful to `docs/statements.md`. Against the brief they are FAITHFUL-STRONGER: they assume `disc ≠ 0` where the brief assumes Disc < 0, and they prove c_C > 0 (with the integral's convergence) where the brief asks for c_C ≠ 0. I found no BLOCKER and no MAJOR. The brief's S4 limit *with its closed-form constant* is still only half machine-checked, because S4.4 has no proof.

## Mandated runs (verbatim; repository root, `nice -n 10`, one Lean process at a time)

1. `git rev-parse HEAD`
```
f35f35eb730845950473e227c539eb879f6c9978
```
2. `lake env lean StatementTypes.lean` (exit 0)
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
3. `cat build/commit/commitments.txt`, the three relevant lines:
```
9490bf1bdc254b2bd297cb0c4a7f76db64fa363ccf1141a92a14fd78331552a9  OscInt.Statements.D4LimitStatement
f4e245bd4b1a3f0ca2e8fb006f574568849b717c089099de66c70f91843d4292  OscInt.Statements.D4BoundNeStatement
96eb2416b768396e5f29e3bfc865d4f181c6ec9ccaf1f1ac0aaf01ef18053be1  OscInt.Statements.D4ConstantPosStatement
```
   - **Match with the stamp:** all three are identical to the `commitment` lines in `stamps/20261106T081634Z-e2d7771c358e/manifest.txt`, which is the stamp `stamps/pins.txt` pins for all three. The other eight lines also match their stamps.
   - **Commit the file was computed on:** a71b318, per the replay record `docs/replay/2026-11-06-S4b-verify-all.txt` (lines 246–248: "matches its stamp").
   - **Why it applies to f35f35e:** `git diff --stat a71b318 f35f35e` touches only `docs/STATUS.md`, the replay record and two review prompts.
   - **Statement sources unchanged since the stamp:** no commit in `e2d7771..f35f35e` touches `OscInt/Statements` or `Challenge*`. The current sha256 of each of these files equals the stamp manifest entry: `OscInt/Statements/D4Limit.lean` (722952f5…), `D4.lean` (6965ce63…), `StationaryPhase.lean` (cd43a116…), `Challenge/D4Limit.lean`, `Challenge.lean`, `comparator-S41w/S42/S43.json`, `lean-toolchain`, `lake-manifest.json`.
   - I did not recompute the commitments myself, because `make commit` writes under `build/`.
4. `lake env lean Axioms.lean | grep -E 'OscInt\.(d4BoundNe|d4Limit|d4ConstantPos) |AUDIT-TOTAL'`
```
AUDIT OscInt.d4BoundNe propext,Classical.choice,Quot.sound
AUDIT OscInt.d4ConstantPos propext,Classical.choice,Quot.sound
AUDIT OscInt.d4Limit propext,Classical.choice,Quot.sound
AUDIT-TOTAL 458 458
```
5. `lake env lean GammaFree.lean` (exit 0)
```
GAMMA-FREE CONTROL Real.Gamma_pos_of_pos rejected as expected (33 forbidden constant(s))
GAMMA-FREE CONTROL gammaProofControl rejected as expected (33 forbidden constant(s))
GAMMA-FREE OK OscInt.Statements.D4ConstantPosStatement (33099 constants in the closure)
GAMMA-FREE OK OscInt.d4ConstantPos (43612 constants in the closure)
```

**Does `GammaFree.lean` really follow proofs? Yes.**
- `gammaClosureBad` follows `ci.type` and `ci.value? (allowOpaque := true)` for every constant it reaches. That covers theorem proofs, definition bodies and opaque values.
- The proof-only control `gammaProofControl` has the Gamma-free type `0 < 1` and uses `Real.Gamma_pos_of_pos` only in its proof. It is rejected, which shows that proof terms are traversed.
- Inductives, constructors and recursors contribute only their types. That is harmless: anything a proof uses appears as a referenced constant.
- **Limitation:** the filter matches names. A Gamma, Beta or Mellin identity re-proved from scratch under another name would pass. I therefore read `OscInt/D4/CosMoment.lean`, `ConstantPos.lean` and `Blueprint/D4Limit.lean`. The route is:
  - one integration by parts, cos·u^{-1/3} → R^{-1/3} sin R + (1/3)∫ sin u·u^{-4/3} (C1);
  - then pairing the humps on each period [2nπ, 2nπ+2π] via the shift u ↦ u+π, so that ∫₀^{2nπ} increases (C2);
  - no special-function computation.
- This is the alternating-series argument as revised in the "Clarification on the S4.3 method" in `docs/statements.md`. It is not the original grouping ∫₀^{π/2} + ∫_{π/2}^{3π/2}, a change the documents state.

## Replay and comparator (read from `docs/replay/2026-11-06-S4b-verify-all.txt`, a71b318, clean tree)
- `comparator-S41w.json`, `-S42.json` and `-S43.json` were each accepted against the pinned stamp. Each challenge export's sha256 matches the stamped manifest. Six kernels accept each one: Lean default, Lean paranoid, lean4lean, nanoda, con-leche and con-ron.
- Per-module leanchecker PASS for all D4 modules, including Angular, ConstantPos(Final), CosMoment, LimitAssembly, LimitFinal, Polar, PolarLimit, Radial, SingularPower and Tail.
- The overall result is INCOMPLETE only because `comparator-S44.json` has no theorem yet.

## What I read in the proof files
- I read `Final.lean`, `ConstantPosFinal.lean`, `LimitFinal.lean`, `LimitSanity.lean`, `ConstantPos.lean`, the head of `LimitAssembly.lean` (including `d4Limit_of`), the head of `CosMoment.lean` and `Blueprint/D4Limit.lean`.
- I grepped all of `OscInt/D4/*.lean` and `Blueprint/*.lean` for `axiom`, `opaque`, `unsafe`, `macro`, `syntax`, `elab`, `notation`, `instance`, `attribute`, `set_option`, `run_cmd`, `#eval`, `sorry`, `admit`, `native_decide` and `import Lean`. The only hit is a docstring line.
- Nothing in the proof files can change what the statements mean. The comparator also checks the types against the frozen challenge export independently.

## Verdicts

### `OscInt.d4BoundNe` : `D4BoundNeStatement`, pinned to commitment `f4e245bd4b1a3f0ca2e8fb006f574568849b717c089099de66c70f91843d4292`
- **Against `docs/statements.md` S4.1′: FAITHFUL.**
  - Hypotheses: C⁴ phase, `dd φ 0 = 0`, `disc (cubicCoeffs φ) ≠ 0`.
  - Quantifiers: `∃ δ > 0, ∃ C` before every A, M, y and every t ≥ 1.
  - Amplitude: `AmpBound 2 (closedBall 0 δ)`, the max-norm ball on ℝ×ℝ.
  - Conclusion: `‖oscInt2 (tφ + y·) A‖ ≤ C M t^{-2/3}`.
  - The coefficients a, b, c, d are correct: the coefficient of x²y in (1/6)D³φ(0)[κ³] is 3∂₁₁₂φ/6 = ∂₁₁₂φ/2.
- **Against the brief: FAITHFUL-STRONGER.** `disc ≠ 0` is the brief's "isolated critical point" condition; it covers D4⁻ as well as D4⁺. Disc < 0 is the special case, which is S4.1.
- **Scope: full.**

### `OscInt.d4Limit` : `D4LimitStatement`, pinned to commitment `9490bf1bdc254b2bd297cb0c4a7f76db64fa363ccf1141a92a14fd78331552a9`
- **Against `docs/statements.md` S4.2: FAITHFUL.**
  - Hypotheses: φ(0) = 0, fderiv φ 0 = 0, D²φ(0) = 0, disc ≠ 0.
  - Quantifiers: `∃ δ > 0` before every A, M.
  - Conclusion: `t^{2/3} · oscInt2 (tφ) A → (d4Constant (cubicCoeffs φ) : ℂ) · A 0` along `atTop`.
- **I re-derived the constant.**
  - Substituting u = |s| r³ gives ∫₀^∞ e^{isr³} r dr = (1/3)|s|^{-2/3} ∫₀^∞ e^{±iu} u^{-1/3} du.
  - The imaginary parts cancel under θ ↦ θ+π because C is odd and |C|^{-2/3} is even.
  - The limit is therefore A(0)·I·J/3, a real number, independent of the sign convention in `exp(iQ)`.
- **The constant has its intended value, not a junk one.** `d4Limit` uses `d4ConstantPos`, which proves that `cosMomentPartial` converges and that the angular integrand is interval-integrable. So `limUnder` and the Bochner interval integral take their real values here.
- **Non-vacuity:** `sanity_D4Limit_hyps` (x³+y³) and `sanity_D4Limit_hyps_elliptic` (x³−3xy², disc 108) show the hypotheses are satisfiable. `ampBound_exists_delta` shows a nonzero amplitude exists for every δ.
- **Against the brief: FAITHFUL-STRONGER in hypotheses** (disc ≠ 0). The constant is the Gamma-free c_C, not the brief's Γ(1/3)²/(√3|Disc|^{1/6}).
- **Scope:** full for S4.2. It is **part** of the brief's limit statement: that statement is S4.2 ∧ S4.4 (the Disc < 0 clause), and S4.4 is unproved.

### `OscInt.d4ConstantPos` : `D4ConstantPosStatement`, pinned to commitment `96eb2416b768396e5f29e3bfc865d4f181c6ec9ccaf1f1ac0aaf01ef18053be1`
- **Against `docs/statements.md` S4.3: FAITHFUL.** The statement has three parts:
  - `Tendsto cosMomentPartial atTop (𝓝 cosMoment)`, so the improper integral converges;
  - `0 < cosMoment`;
  - for every q with `disc q ≠ 0`: interval integrability of |C(cos θ, sin θ)|^{-2/3} on [0, 2π], and `0 < d4Constant q`.
- **Proof method:** Gamma, Beta and Mellin free, checked mechanically by a check that does follow proofs (see run 5). The route is the IBP plus hump-pairing alternating argument.
- **Against the brief: FAITHFUL-STRONGER** (> 0 instead of ≠ 0; convergence and integrability are stated explicitly).
- **Scope: full.**

## What remains unproved for the brief's S4: S4.4
`D4ConstantClosedFormStatement` has no proof (`comparator-S44.json`: "no challenge theorem is declared yet"). Three identities are therefore not machine-checked:
- I = Γ(2/3)/2;
- c_C = Γ(1/3)²/(√3|Disc C|^{1/6}) for Disc < 0, the brief's formula;
- c_C = Γ(1/3)²/Disc^{1/6} for Disc > 0.

So the brief's limit "t^{2/3}∫e^{itφ}A → c_C A(0) with c_C = Γ(1/3)²/(√3|Disc C|^{1/6})" is machine-checked only with the Gamma-free c_C. "c_C ≠ 0 by the alternating series" is fully checked (S4.3), and the uniform bound is fully checked (S4.1 and S4.1′).

## Findings
- **BLOCKER:** none.
- **MAJOR:** none.
- **MINOR 1 (stale status prose, a citation risk).**
  - `docs/STATUS.md` line 56 still says of S4.2–S4.4 "none is proved yet", while lines 13–15 of the same file say S4.1′, S4.2 and S4.3 are proved and replayed.
  - `README.md` line 5 ("the limit and its constant S4.2–S4.4 are stated, not yet proved") and line 17 ("proofs not started") are also stale.
  - When updated, these should keep the wording "the brief's limit with its constant is S4.2 ∧ S4.4", and S4.4 is open.
- **NIT 2.** Clarification (2) in `docs/statements.md` says the `angularMoment` integrand "is integrable iff `disc q ≠ 0`". This is false at q = 0: the integrand is identically `0 ^ (-2/3) = 0`, which is integrable, while disc 0 = 0. The conclusion `d4Constant q = 0` when disc = 0 still holds, because J = 0. Suggested fix: "for q ≠ 0, integrable iff disc q ≠ 0".
- **NIT 3.** `review/2026-11-06-S4b-pre-proof-answers.md` says "values of `opaque` constants are not followed". This is stale: the current check uses `value? (allowOpaque := true)`, which follows them. The same file's "7 forbidden constants" for the control is also outdated; the run prints 33.
- **NIT 4.** The `GammaFree.lean` module docstring has an unmatched backtick and repeats the control code inside the docstring. Cosmetic only.
- **NIT 5.** The Gamma-free check matches names. It is adequate together with the human reading above (the route in `CosMoment.lean` is the hump-pairing argument), but a reader citing the check alone should know it would not catch a renamed re-derivation.

## Files
- `/home/user/lean-oscillatory/OscInt/Statements/D4Limit.lean`
- `/home/user/lean-oscillatory/OscInt/D4/Final.lean`
- `/home/user/lean-oscillatory/OscInt/D4/ConstantPosFinal.lean`
- `/home/user/lean-oscillatory/OscInt/D4/LimitFinal.lean`
- `/home/user/lean-oscillatory/OscInt/D4/CosMoment.lean`
- `/home/user/lean-oscillatory/OscInt/D4/ConstantPos.lean`
- `/home/user/lean-oscillatory/Blueprint/D4Limit.lean`
- `/home/user/lean-oscillatory/GammaFree.lean`
- `/home/user/lean-oscillatory/docs/replay/2026-11-06-S4b-verify-all.txt`
- `/home/user/lean-oscillatory/docs/STATUS.md`
- `/home/user/lean-oscillatory/README.md`

Nothing was written in the repository.