<!-- Post-proof review of S4.4, referee B (fresh-context agent, prompt review/prompts/S44-post-proof.md), commit e5da8a5. Verbatim final report. -->

# Post-proof fidelity review, S4.4: referee B

**Verdict: FAITHFUL, scope `full`.** It is pinned to commitment `3f089384d33ac7f6d4a24195c64b10af9093125fec7456da342a0477e510e6cc` for `OscInt.Statements.D4ConstantClosedFormStatement` (stamp `stamps/20261106T081634Z-e2d7771c358e`).

Against `docs/statements.md` S4.4 and against the brief's Disc < 0 constant Γ(1/3)²/(√3|Disc C|^{1/6}), the result is exact. The Disc > 0 clause goes beyond the brief and is also correct. There are no BLOCKER and no MAJOR findings.

## Required runs (repository root, `nice -n 10`, one Lean process at a time)

**1. `git rev-parse HEAD` and `git status --short`**
```
e5da8a5fa9b6b381371332f588f02c8aac697724
```
`git status --short` printed nothing, so the tree is clean. It was still clean at the end of my run.

`git diff --stat 1c7ebe3 e5da8a5` lists only `CHANGELOG.md`, `README.md`, `docs/HANDOFF.md`, `docs/STATUS.md`, `docs/lessons.md` and `docs/replay/2026-11-06-S44-verify-all.txt`. That is documentation and the replay record only.

Two further checks on files that could change the statement:
- `git diff --stat e2d7771 HEAD -- OscInt/Statements Challenge Challenge.lean` is empty.
- The hashes of `OscInt/Statements/D4Limit.lean` (722952f5…), `D4.lean` (6965ce63…), `StationaryPhase.lean` (cd43a116…) and `docs/decisions/2026-11-06-S4.md` (c0b9c4a8…) equal the pinned manifest.
- `docs/statements.md` differs from the manifest only by the 18 appended clarification lines. They change no statement.

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
TYPE-OK OscInt.d4ConstantClosedForm : OscInt.Statements.D4ConstantClosedFormStatement
```

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
- **Which commit:** this file was computed on 1c7ebe3. The replay record `docs/replay/2026-11-06-S44-verify-all.txt` says "make verify-all on commit 1c7ebe3 (clean tree) … RESULT PASS (9 of 9 steps)". Its line 153 is the same hash, and line 164 reads "commit: OscInt.Statements.D4ConstantClosedFormStatement matches its stamp stamps/20261106T081634Z-e2d7771c358e".
- **Pinned stamp:** `stamps/pins.txt` pins this statement to `stamps/20261106T081634Z-e2d7771c358e`. That manifest (commit e2d7771) has `commitment 3f089384d33ac7f6d4a24195c64b10af9093125fec7456da342a0477e510e6cc  OscInt.Statements.D4ConstantClosedFormStatement`. The two are **identical**.
- **Comparator:** the record says comparator-S44.json was accepted against that stamp. `comparator-S44.json` names only `OscInt.d4ConstantClosedForm`, with axioms propext, Quot.sound and Classical.choice.

**4. `lake env lean Axioms.lean | grep -E 'OscInt\.d4ConstantClosedForm |AUDIT-TOTAL'`**
```
AUDIT OscInt.d4ConstantClosedForm propext,Classical.choice,Quot.sound
AUDIT-TOTAL 521 521
```

## What the statement says
I elaborated it with `pp.numericTypes` in the scratch file `/tmp/refB/Check.lean`:
```
(cosMoment = Real.Gamma ((2/3):ℝ) / 2) ∧
(∀ q, disc q < 0 → d4Constant q = Real.Gamma ((1/3):ℝ) ^ (2:ℕ) / (√3 * |disc q| ^ ((1/6):ℝ))) ∧
(∀ q, 0 < disc q → d4Constant q = Real.Gamma ((1/3):ℝ) ^ (2:ℕ) / (disc q ^ ((1/6):ℝ)))
```
- **Numerals and powers:** every numeral is real-valued, so there is no truncating ℕ division. The power `^2` applies to Γ(1/3). The exponent of `u` in `cosMomentPartial` is the real (−1)/3.
- **I = Γ(2/3)/2:** correct, since I = Γ(2/3)cos(π/3).
- **`limUnder`:** the first conjunct is about the `limUnder` value. The proved S4.3 (`d4ConstantPos`, first conjunct `Tendsto cosMomentPartial atTop (𝓝 cosMoment)`) makes that value the actual improper integral. Without convergence the value would be unspecified, so it could not be proved equal to Γ(2/3)/2 on purpose. There is no escape.
- **Sign convention of `disc`:** `disc` = b²c² − 4ac³ − 4b³d − 27a²d² + 18abcd, the standard binary-cubic discriminant. Disc < 0 is one real factor, the hyperbolic umbilic D4⁺ (x³ + y³ gives −27). Disc > 0 is three real factors, D4⁻ (x³ − 3xy² gives 108). This matches the brief's "negative discriminant".
- **Power of |Disc|:** 1/6 is correct by covariance. Disc(λC∘L) = λ⁴(det L)⁶ Disc C, and c_C scales by |λ|^{−2/3}|det L|^{−1}.
- **Check on x³ + y³:** |Disc|^{1/6} = √3, so c = Γ(1/3)²/3, the Beta-integral value.
- **Non-integrable `angularMoment`:** both right-hand sides are strictly positive. So S4.4 itself forces `angularMoment q ≠ 0`, which rules out the Bochner junk value 0 for every q it covers. S4.3 also states integrability.
- **`Real.rpow` of a negative base:** none occurs. The bases are `|disc q|`, `disc q` under `0 < disc q`, `|C(cos θ, sin θ)|`, and `u` on (0, R]. The value 0^(−a) = 0 occurs only on null sets.
- **Junk at Disc = 0:** `d4Constant` is 0 there, but every clause excludes Disc = 0.

## Numerical check of the closed forms
I used my own mpmath script, `/tmp/refB/num.py`, at 30 digits.
- **Method:**
  - I was computed as 3∫₀¹ s·cos(s³) ds plus `quadosc` on [1, ∞).
  - J was computed by tanh-sinh quadrature on [0, 2π], with breakpoints at the zeros of C(cos θ, sin θ) at full precision.
  - The zeros are θ = arctan of the real roots of a + bu + cu² + du³, together with their shifts by π.
- **I:** 0.677058969713200208472644014077, which equals Γ(2/3)/2 to all printed digits.
- **(2, −3, 1, 4)**, i.e. 2x³ − 3x²y + xy² + 4y³, all coefficients nonzero, disc −1727 (Lean check `disc (2,-3,1,4) = -1727` by `norm_num` compiled): I·J/3 = 1.196234017460642, closed form 1.196234017463506, relative difference −2.4e−12.
- **(1, 1, −2, −1)**, disc 49 (Disc > 0): I·J/3 = 3.751683143286339, closed form 3.751683143321951, relative difference −9.5e−12.
- **(1, 1, 1, 1)**, disc −16: relative difference −8.7e−12.
- **Why this is decisive:** a missing √3, or the power 1/4 in place of 1/6, would change the value by O(1).
- **Pitfall I hit:** a first run with breakpoints rounded to float gave only about 1e−7 agreement, and a naive `quadosc` for I gave 1e−3. Both were artefacts of my script, which I fixed.

## Proof files
I looked at these only to check that nothing in them can change the meaning of the statement:
- `OscInt/D4/ClosedFormFinal.lean`, in full. The theorem is `d4ConstantClosedForm_of (cosMomentValue betaIoi) angularLine covariance normalForm (lineMomentValues betaIoi betaUnit) gammaSixth`.
- The head of `docs/proof-S44.md`.
- The definitions in `Blueprint/D4ClosedForm.lean`. They are new names in `OscInt.Blueprint`; none redefines a statement constant.
- A grep of `OscInt/D4/*` and the blueprint for axiom, opaque, unsafe, extern, implemented_by, instance, sorry, admit, native_decide, ofReduceBool, `debug.skipKernelTC` and `attribute [-`. The only hit is a docstring.

The statement type is checked by `Expr` equality, and `OscInt/Statements` is unchanged since the stamp, so nothing in the proof files can alter the statement.

## Does S4.2 ∧ S4.4 give the brief's S4 limit?
Yes.
- `OscInt.d4Limit` gives t^{2/3}∫e^{itφ}A → d4Constant(cubicCoeffs φ)·A(0) under Disc ≠ 0.
- The Disc < 0 clause of `OscInt.d4ConstantClosedForm` rewrites d4Constant(q) as Γ(1/3)²/(√3|Disc C|^{1/6}).
- Together these are the brief's limit with its constant. For Disc > 0 they also give the D4⁻ analogue.
- "c_C ≠ 0" is S4.3, proved without Gamma by name.
- The integral convention matches: ∫_{ℝ²} e^{iC} = (1/3)Γ(2/3)cos(π/3)·J = I·J/3, with no 2π normalisation.

## Findings
- **BLOCKER:** none.
- **MAJOR:** none.
- **MINOR 1:** the brief's S4 exists only as the pair of two theorems, not as one combined Lean statement. This was already raised before the proof, and `docs/STATUS.md` says it correctly. Every citation must name both `d4Limit` and `d4ConstantClosedForm`, plus `d4ConstantPos` for "≠ 0" and for convergence of the improper integral. A one-line corollary would make the citation a single object, but it would need its own statement and stamp.
- **NIT 1:** read alone, S4.4's first conjunct is about the `limUnder` value, so "I is an improper integral equal to Γ(2/3)/2" needs S4.3's first conjunct. This is documented as clarification (3) in `docs/statements.md`. It is harmless because S4.3 is proved.
- **NIT 2:** `docs/STATUS.md` line 16 says "post: pending". It needs updating once both post-proof reports exist; that is an expected follow-up, not a defect.
