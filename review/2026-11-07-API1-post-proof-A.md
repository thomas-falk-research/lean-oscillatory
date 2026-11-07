<!-- Post-proof review of front-end batch 1 (F1, F2), referee A (fresh-context agent, prompt review/prompts/API1-post-proof.md), commit 9a79382. Verbatim final report. -->

# Post-proof referee A: front-end batch 1 (F1, F2), commit 9a79382

## Summary

- **F1 `OscInt.API.ampBoundOfContDiff`: FAITHFUL, scope full.** Pinned to commitment `ec40ed3e51ec4cc137fcc2c1a5462f076cabd712d0701b729f9cb64856a50c58`.
- **F2 `OscInt.API.d4LimitClosedForm`: FAITHFUL to `docs/statements.md` F2, scope full.** Pinned to commitment `7db2d5f188ee0984ee684caa10e18c74af554e0c718a903cd643e540d278f741`.
  - Against the brief's S4, as quoted in statements.md, it is **FAITHFUL-STRONGER**: it adds the elliptic branch Disc > 0, and it covers C² amplitudes rather than smooth ones.
  - It is only **part** of the brief's whole S4, because the uniform O(t^{-2/3}) bound is S4.1/S4.1′ and c_C ≠ 0 is S4.3.
- There are **no BLOCKER and no MAJOR findings**: 2 MINOR and 5 NIT, all about docstrings and STATUS wording.

I edited nothing in the repository and changed no git state, and I ran no `make` or `lake build`. I ran one Lean process at a time under `nice -n 10`, and wrote no scratch files.

## Required runs (verbatim)

**1. HEAD and tree state**
```
$ git rev-parse HEAD
9a79382ab00552443b9945c6cef6651eea3948d7
$ git status --short
(no output: the tree is clean)
```

**2. Statement types**
```
$ lake env lean StatementTypes.lean
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
TYPE-OK OscInt.d4ConstantClosedForm : OscInt.Statements.D4ConstantClosedFormStatement
TYPE-OK OscInt.API.ampBoundOfContDiff : OscInt.Statements.AmpBoundOfContDiffStatement
TYPE-OK OscInt.API.d4LimitClosedForm : OscInt.Statements.D4LimitClosedFormStatement
```

**3. Commitments**
```
$ cat build/commit/commitments.txt
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
7db2d5f188ee0984ee684caa10e18c74af554e0c718a903cd643e540d278f741  OscInt.Statements.D4LimitClosedFormStatement
ec40ed3e51ec4cc137fcc2c1a5462f076cabd712d0701b729f9cb64856a50c58  OscInt.Statements.AmpBoundOfContDiffStatement
3f089384d33ac7f6d4a24195c64b10af9093125fec7456da342a0477e510e6cc  OscInt.Statements.D4ConstantClosedFormStatement
```

- **Which commit computed this file:** 2ddcbe0, per `docs/replay/2026-11-07-API1-verify-all.txt` ("make verify-all on commit 2ddcbe0 (clean tree) … RESULT PASS (9 of 9 steps)"). The file is dated Nov 7 02:23.
- **The commit range after that changes no statement:** `git diff --stat 2ddcbe0 9a79382` touches only `docs/STATUS.md`, the replay record and `review/prompts/API1-post-proof.md`.
- **Both lines match the pinned stamp:** `stamps/pins.txt` pins both statements to `stamps/20261107T012459Z-2d5356432156`. That stamp's `manifest.txt` (commit 2d53564…) has these lines, identical to the file:
  - `commitment 7db2d5f1…f741  OscInt.Statements.D4LimitClosedFormStatement` (line 295)
  - `commitment ec40ed3e…0c58  OscInt.Statements.AmpBoundOfContDiffStatement` (line 296)
- **Statement files at HEAD match the manifest:** I compared sha256 sums for `OscInt/Statements/{FrontEnd,D4Limit,D4,StationaryPhase}.lean`, `Challenge/FrontEnd.lean` and `comparator-API1.json`, and all match.
  - `StatementTypes.lean` differs from the manifest, as expected. The only change since the stamp is the two added `#assert_type_is` lines for F1 and F2.
  - `tools/src/bin/statements.rs` also changed after the stamp. The change only adds an "INCOMPLETE vs FAIL" exit code, and the commitments are computed by the `commit` tool, not by this file.

**4. Axiom audit**
```
$ lake env lean Axioms.lean | grep -E 'OscInt\.API\.(ampBoundOfContDiff|d4LimitClosedForm) |AUDIT-TOTAL'
AUDIT OscInt.API.ampBoundOfContDiff propext,Classical.choice,Quot.sound
AUDIT OscInt.API.d4LimitClosedForm propext,Classical.choice,Quot.sound
AUDIT-TOTAL 536 536
```

The replay record also shows `comparator-API1.json` accepted against the pinned stamp by six kernels (Lean default, Lean paranoid, lean4lean, nanoda, con-leche, con-ron), with the challenge export sha256 `1a23282e…d7b` equal to the manifest's.

## Verdicts

### F1 `OscInt.API.ampBoundOfContDiff`: FAITHFUL, scope full

Commitment `ec40ed3e51ec4cc137fcc2c1a5462f076cabd712d0701b729f9cb64856a50c58`.

- **Type:** checked by `Expr` equality to be the frozen constant `AmpBoundOfContDiffStatement`, which is `∀ n K A, IsCompact K → ContDiff ℝ n A → tsupport A ⊆ K → ∃ M, AmpBound n K A M`.
- **Match with the docs:** this is exactly docs F1. `AmpBound` is `ContDiff ℝ n A ∧ tsupport A ⊆ K ∧ ∀ j ≤ n, ∀ k, ‖iteratedFDeriv ℝ j A k‖ ≤ M`, matching "‖D^j A(k)‖ ≤ M for all j ≤ n and all k".
- **The proof is the textbook argument, with no shortcut:**
  - `ContDiff.continuous_iteratedFDeriv` gives continuity of each derivative, and `IsCompact.exists_bound_of_continuousOn` gives a bound on K.
  - Outside K the derivative is 0, via `tsupport_iteratedFDeriv_subset` and `image_eq_zero_of_notMem_tsupport`.
  - M is the sum of the per-order bounds `max C 0` for j ≤ n.
- **What is lost:** only uniformity in M, as the docs say.

### F2 `OscInt.API.d4LimitClosedForm`: FAITHFUL to docs F2, scope full

Commitment `7db2d5f188ee0984ee684caa10e18c74af554e0c718a903cd643e540d278f741`.

- **Type:** checked by `Expr` equality to be `D4LimitClosedFormStatement`. I re-checked that statement against docs F2:
  - The phase hypotheses are exactly S4.2's: C⁴, φ(0) = 0, `fderiv ℝ φ 0 = 0`, `dd φ 0 = 0`, `disc (cubicCoeffs φ) ≠ 0`.
  - The quantifier order is `∃ δ > 0` before `∀ A`, so δ depends only on φ.
  - The amplitude hypothesis is `ContDiff ℝ 2 A` with `tsupport A ⊆ closedBall 0 δ` (the max-norm ball).
  - The integral is written out and is the same term as `oscInt2 (fun κ => t * φ κ) A`.
  - The prefactor is `Real.rpow` t^{2/3} cast to ℂ, and the limit is along `atTop`.
  - The limit is `d4ClosedConstant (disc (cubicCoeffs φ)) · A 0`.
- **`d4ClosedConstant` is right:** it is Γ(1/3)²/(√3|D|^{1/6}) for D < 0 and Γ(1/3)²/D^{1/6} otherwise, which is exactly S4.4's two branches. D = 0 is unreachable.
- **The proof is the advertised bridge, with nothing stronger hidden:**
  - δ comes from `OscInt.d4Limit` (S4.2), and M from F1 on `closedBall 0 δ`.
  - The constant is rewritten by `d4Constant_eq_closed`, which splits on the sign of the discriminant and uses `OscInt.d4ConstantClosedForm.2.1` / `.2.2` (S4.4).
  - S4.2 and S4.4 are themselves machine-checked as stated (STATUS, earlier replays), so F2 rests on proved frozen theorems.
- **Against the brief's S4:**
  - On Disc < 0 it is the brief's limit with the brief's constant Γ(1/3)²/(√3|Disc C|^{1/6}).
  - It adds the elliptic branch and allows C² amplitudes, hence FAITHFUL-STRONGER.
  - The brief's uniform bound (S4.1/S4.1′) and "c_C ≠ 0" (S4.3) are not part of F2, so relative to the whole brief S4 it is part. A nonzero limit does follow from F2 together with `sanity_d4ClosedConstant_pos`.

## `OscInt/API/Sanity.lean`: do its theorems answer the pre-proof MINORs, and do they test what they claim?

- **`apiSanity_elliptic_hyps`** (answers A-MINOR 2 and B-MINOR 2).
  - It proves F2's five phase hypotheses for `genCubic 1 0 (-3) 0` = x³ − 3xy², with `disc = 108`.
  - It uses the same `cubicCoeffs`, `dd` and `fderiv` predicates as F2, and `genCubic` is the literal polynomial (`OscInt/D4/Sanity.lean:20`). It tests what it claims.
- **`apiSanity_generic_hyps`** (answers A's "no cubic with all coefficients nonzero").
  - It covers x³ + 2x²y + 3xy² + 5y³, with `disc = -367`. It is correct.
- **`apiSanity_elliptic_constant`** (answers B-MINOR 1 and partly A-MINOR 1).
  - It proves `d4ClosedConstant 108 = √π Γ(1/6)/3` using `108^{1/6} = 2^{1/3}√3` and `gammaSixth` (√πΓ(1/6) = √3Γ(1/3)²/2^{1/3}, from Mathlib's duplication and reflection formulas).
  - This is a genuine non-unfolding check of the elliptic branch against referee B's hand value, c = √πΓ(1/6)/3 ≈ 3.28868 via J = 2B(1/2, 1/6). The arithmetic checks out.
  - Caveat (NIT): `gammaSixth` is also an ingredient of the S4.4 proof (`ClosedFormFinal.lean:32`), so the check shares that one lemma. The lemma is a proved, audited Gamma identity, so this is not a soundness concern.
  - A-MINOR 1 ("nothing in Lean ties `d4ClosedConstant` to `d4Constant`") is now fully answered by S4.4 being proved, together with `OscInt.API.d4Constant_eq_closed`, rather than by this file.
- **`apiSanity_elliptic_bite`** (bite).
  - It derives `∃ A c, c ≠ 0 ∧ Tendsto (t^{2/3} ∫ e^{it(x³−3xy²)} A) atTop (𝓝 c)` from F2, using a `ContDiffBump` of radii δ/2 < δ, so A(0) = 1 and the support lies in the δ-ball. Here c = `d4ClosedConstant 108 · 1`, which is nonzero by `sanity_d4ClosedConstant_pos`.
  - The hypotheses are discharged by proved facts, so the conclusion is reached without vacuity. It tests what it claims: t^{2/3}|∫| does not tend to 0.
  - NIT: A and c are existential in the statement, so as written it does not show that A is a bump or what c is. `examples/consumer/Consumer.lean`'s `consumer_elliptic_limit` gives the explicit form (limit √πΓ(1/6)/3 · A(0) for every admissible A).
- **Not answered (NIT):** the pre-proof NITs on the frozen `FrontEnd.lean` are untouched: the D = 0 junk value is not documented, and `sanity_AmpBoundOfContDiff_hyps` is fixed at n = 2. That is correct, since that file is frozen.

## `OscInt/API.lean` docstring: does it claim anything the files do not support?

- **MINOR 1.** The sentence "Every theorem below has, as its type, a statement that was frozen, stamped and reviewed" is literally false for `OscInt.API.d4Constant_eq_closed`. That is a helper theorem in this file whose type is not a frozen statement. Suggested wording: "every theorem in the table …".
- **MINOR 2.** The phrase "frozen, stamped and reviewed before it was used" does not repeat the disclosure in `docs/statements.md` (Process note) that the F1/F2 bridge proofs were drafted before the statements were stamped and reviewed. A reader of this file alone could take it to mean "statement fixed before the proof" for F1 and F2, which the docs explicitly do not claim.
- **NIT 1.** The S4.2–S4.4 table row gives only the Disc < 0 constant. S4.4 and F2 also give the Disc > 0 branch.
- **NIT 2.** "Re-exported here" is loose: S1–S4 are imported, not re-declared, under their existing `OscInt.*` names. Those names do exist (StatementTypes TYPE-OK).
- **Checked and fine:**
  - The Stein constants: 5·2^{k−1} − 2 gives 3, 8, 18, matching `VdC1–3Statement`.
  - The F1 and F2 rows are accurate.
  - The textbook references are properly caveated as unchecked.

## Other

- **NIT (outside the prompt's file list).** The `docs/STATUS.md` F2 row says "the brief's S4 as one theorem". The brief's S4 also includes the uniform bound (S4.1), so "the brief's S4 limit with its closed-form constant as one theorem" would be accurate. The same row already records FAITHFUL-STRONGER, which I confirm.

## Findings

- **BLOCKER:** none.
- **MAJOR:** none.
- **MINOR:**
  - API.lean says "Every theorem below" has a frozen statement as its type; `d4Constant_eq_closed` does not.
  - API.lean's "before it was used" omits the drafted-before-review disclosure for F1/F2.
- **NIT:**
  - The S4.2–S4.4 table row omits the elliptic branch.
  - "Re-exported" is loose wording.
  - The bite theorem hides A and c behind existentials.
  - `gammaSixth` is shared with the S4.4 proof.
  - The STATUS F2 row wording ("the brief's S4 as one theorem").

## Files read

- Lean: `/home/user/lean-oscillatory/OscInt/API.lean`, `/home/user/lean-oscillatory/OscInt/API/Sanity.lean`, `/home/user/lean-oscillatory/OscInt/Statements/FrontEnd.lean`, `/home/user/lean-oscillatory/StatementTypes.lean`
- Configuration and stamps: `/home/user/lean-oscillatory/comparator-API1.json`, `/home/user/lean-oscillatory/stamps/pins.txt`, `/home/user/lean-oscillatory/stamps/20261107T012459Z-2d5356432156/manifest.txt`
- Records and docs: `/home/user/lean-oscillatory/docs/replay/2026-11-07-API1-verify-all.txt`, `/home/user/lean-oscillatory/docs/statements.md`
