<!-- Post-proof review of S4.4, referee A (fresh-context agent, prompt review/prompts/S44-post-proof.md), commit e5da8a5. Verbatim final report. -->

# Post-proof fidelity review of S4.4, referee A (commit e5da8a5)

**Verdict: FAITHFUL, scope `full`.** The verdict is pinned to commitment `3f089384d33ac7f6d4a24195c64b10af9093125fec7456da342a0477e510e6cc` (`OscInt.Statements.D4ConstantClosedFormStatement`, stamp `20261106T081634Z-e2d7771c358e`). There are no BLOCKER, MAJOR or MINOR findings, only two NITs.

## Required runs (repository root, `nice -n 10`, one Lean process of mine at a time)

**1. Tree state.**
```
$ git rev-parse HEAD
e5da8a5fa9b6b381371332f588f02c8aac697724
$ git status --short
(no output: tree clean)
```
- `git diff --stat 1c7ebe3 e5da8a5` lists only `CHANGELOG.md`, `README.md`, `docs/HANDOFF.md`, `docs/STATUS.md`, `docs/lessons.md` and `docs/replay/2026-11-06-S44-verify-all.txt` (6 files, +474/−31). So 1c7ebe3 to e5da8a5 is documentation and the replay record only.
- `git diff --stat e2d7771 HEAD -- OscInt/Statements comparator-S44.json Challenge Challenge.lean` is empty: the statement files and the challenge are unchanged since the stamp.
- The sha256 of `OscInt/Statements/D4Limit.lean`, `D4.lean`, `StationaryPhase.lean` and `comparator-S44.json` all equal the stamp manifest entries.

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
- **Which commit:** the file was computed on 1c7ebe3, by the verify-all run recorded in `docs/replay/2026-11-06-S44-verify-all.txt` ("make verify-all on commit 1c7ebe3 (clean tree) … RESULT PASS (9 of 9 steps)").
- **Against the replay record:** the 11 commitment lines in the record are identical to this file (checked with `diff`).
- **Against the pinned stamp:** the `D4ConstantClosedFormStatement` line equals the stamp manifest line `commitment 3f089384…10e6cc  OscInt.Statements.D4ConstantClosedFormStatement`. All 11 lines equal the manifest (sorted `diff`).
- The record also has "commit: OscInt.Statements.D4ConstantClosedFormStatement matches its stamp stamps/20261106T081634Z-e2d7771c358e" and "comparator: comparator-S44.json accepted against stamps/20261106T081634Z-e2d7771c358e", plus all six export kernels and per-module leanchecker PASS.

**4. `lake env lean Axioms.lean | grep -E 'OscInt\.d4ConstantClosedForm |AUDIT-TOTAL'`** (took 6m39s)
```
AUDIT OscInt.d4ConstantClosedForm propext,Classical.choice,Quot.sound
AUDIT-TOTAL 521 521
```

## Fidelity analysis

The statement is `OscInt/Statements/D4Limit.lean`, with `disc` and `cubicCoeffs` from `D4.lean` and `dd`/`ddd` from `StationaryPhase.lean`.

**Conjunct 1: `cosMoment = Real.Gamma (2 / 3) / 2`.**
- This is correct: ∫₀^∞ cos u · u^{s−1} du = Γ(s) cos(πs/2) at s = 2/3.
- `cosMoment` is the `limUnder atTop` value of ∫₀^R. Read alone, the conjunct is about that value. The limit exists by S4.3's first conjunct (`OscInt.d4ConstantPos`, proved and TYPE-OK).
- A junk `limUnder` value could not be proved equal to a specific number anyway. So, with S4.3, this is I = Γ(2/3)/2 for the improper integral.

**Sign convention for `disc`.** `disc = b²c² − 4ac³ − 4b³d − 27a²d² + 18abcd` is the standard discriminant of a x³ + b x²y + c xy² + d y³. Disc < 0 means one real linear factor, the hyperbolic umbilic, for example x³ + y³ with disc = −27. This is the brief's "negative discriminant" case, and it gets the brief's √3 formula.

**Disc < 0 clause.** `d4Constant q = Γ(1/3)² / (√3 · |disc q|^{(1:ℝ)/6})`. This is exactly the brief's Γ(1/3)²/(√3|Disc C|^{1/6}).

**Disc > 0 clause.** `d4Constant q = Γ(1/3)² / disc q ^ ((1:ℝ)/6)`. The base is positive under the hypothesis.

**Power of |Disc|.** 1/6 is the right power:
- Under C ↦ λC, c_C scales by |λ|^{−2/3} and Disc by λ⁴, so |Disc|^{−1/6} scales by |λ|^{−2/3}.
- Under C ↦ C∘L, c_C scales by |det L|^{−1} and Disc by (det L)⁶, so |Disc|^{−1/6} scales by |det L|^{−1}.

**Normal forms by hand.**
- x³ + y³: Γ(1/3)²/(√3·27^{1/6}) = Γ(1/3)²/3, which is the Beta-integral value.
- x³ − 3xy² (disc = 108): Γ(1/3)²/108^{1/6}.

**Junk-value escapes.** There are none:
- **`Real.rpow` of a negative base:** in the Disc < 0 clause the base is `|disc q|`; in the Disc > 0 clause the base is `disc q > 0`.
- **Non-integrable `angularMoment`:** both right-hand sides are strictly positive (Γ(1/3) > 0, rpow of a positive base). So the theorem itself forces `angularMoment q ≠ 0`, which rules out the Bochner junk value 0. Integrability is also asserted separately by S4.3.
- **Numeric types:** `1/3`, `2/3` and `1/6` are all ℝ (the argument of `Real.Gamma`, and the explicit `(1 : ℝ) / 6`). The `^ 2` on Γ is the natural-number power.

**Quantification.** S4.4 quantifies over every q with disc q < 0 (resp. > 0). So it applies to q = `cubicCoeffs φ`.

**`cubicCoeffs` against `cubicForm`.** b = ∂₁₁₂φ(0)/2 is the x²y coefficient of (1/6)D³φ(0)[z³], since that coefficient is 3∂₁₁₂/6. The other coefficients check the same way, so the orders agree.

**Numerical check of my own** (`/tmp/refA/check.py`, mpmath at 30 digits).
- Method: I = quad on [0, π/2] plus quadosc on [π/2, ∞). J is computed from the definition by tanh–sinh quadrature, split at the zeros θ = arctan(real roots of a + bt + ct² + dt³), mod π. Then I·J/3 is compared with the closed form.
- I = 0.67705896971320020847261, against Γ(2/3)/2 = 0.67705896971320020847264.
- Results for cubics with all coefficients nonzero:

| Cubic (a, b, c, d) | disc | real roots | relative error vs closed form |
|---|---|---|---|
| (2, −1, 3, 1) | −419 | 1 | 1.7e−11 |
| (1, 2, 3, 5) | −367 | 1 | 1.9e−11 |
| (1, 1, −4, −1) | 321 | 3 | 7.1e−12 |
| (3, −2, −5, 1) | 1929 | 3 | 4.7e−13 |
| x³ + y³ (control) | −27 | 1 | 8.1e−12 |

- For (2, −1, 3, 1): I·J/3 = 1.51470898214713 and the closed form is 1.51470898217281.
- If the two clauses were swapped, the results would be off by a factor √3. If the power were wrong, the error would grow with |disc|. Neither happens.
- My first run used quadosc on [0, ∞) for I and gave a uniform 1.1e−3 error. That was my quadrature failing at the u^{−1/3} singularity, not the statement; the split computation above fixed it.

**What I looked at in the proof files.** I read `OscInt/D4/ClosedFormFinal.lean` in full: the theorem is `d4ConstantClosedForm_of` applied to the parts, plus `d4Constant_example` at disc = −367. I also read:
- the signature and opening of `d4ConstantClosedForm_of` in `OscInt/D4/ClosedForm.lean`, which takes Prop-valued blueprint hypotheses and concludes `D4ConstantClosedFormStatement`;
- the definition list in `Blueprint/D4ClosedForm.lean`;
- the first 40 lines of `docs/proof-S44.md`.

A grep over all `OscInt/D4/*.lean`, `Blueprint/D4ClosedForm.lean` and `OscInt.lean` found no `axiom`, `opaque`, `unsafe`, `implemented_by`/`extern`, `macro`, `elab`, `syntax`, `notation`, `instance`, `run_cmd`, `#eval` or `sorry`.

Nothing in these files can change the statement's meaning, for three reasons:
- the theorem's type is Expr-equal to the statement constant (TYPE-OK);
- the statement's commitment equals the stamp;
- the comparator accepted the solution against the frozen challenge export.

## S4.2 ∧ S4.4 and the brief

Yes: S4.2 ∧ S4.4 now gives the brief's S4 limit with its closed-form constant.
- `OscInt.d4Limit` gives t^{2/3}∫e^{itφ}A → `d4Constant (cubicCoeffs φ)` · A(0) for disc ≠ 0.
- Clause 2 of `OscInt.d4ConstantClosedForm`, at q = `cubicCoeffs φ` with disc < 0, rewrites the constant to Γ(1/3)²/(√3|Disc C|^{1/6}).
- So the brief's limit is machine-checked as the pair. "c_C ≠ 0" comes from S4.3 by the Gamma-free route, and also from S4.4.
- The Disc > 0 clause is an extension beyond the brief (the elliptic umbilic) and is correct.
- This relies on the C = (1/6)D³φ(0) normalisation in `docs/statements.md` S4. The decision record's direct 2D quadrature validates that normalisation for x³ + y³.

## Findings
- **BLOCKER:** none.
- **MAJOR:** none.
- **MINOR:** none.
- **NIT 1.** Read alone, the first conjunct is about the `limUnder` value. The improper-integral reading needs S4.3's first conjunct. This is already recorded as clarification (3) in `docs/statements.md`. Any citation of "I = Γ(2/3)/2 for the improper integral" should name `d4ConstantPos.1` as well.
- **NIT 2.** There is no single Lean object for the brief's S4. A citation must name both `OscInt.d4Limit` and `OscInt.d4ConstantClosedForm`, as the docs already require. The `docs/STATUS.md` S4.4 row still says "post: pending", which is expected until these reports are filed.

Scratch files: `/tmp/refA/check.py`, `/tmp/refA/st.txt`, `/tmp/refA/ax.txt`. No repository files, git state or `build/` were modified.
