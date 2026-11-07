<!-- Post-proof review of front-end batch 1 (F1, F2), referee B (fresh-context agent, prompt review/prompts/API1-post-proof.md), commit 9a79382. Verbatim final report. -->

# Post-proof referee B: front-end batch 1 (F1 `OscInt.API.ampBoundOfContDiff`, F2 `OscInt.API.d4LimitClosedForm`)

**Bottom line:** I find both theorems faithful. There are no BLOCKER or MAJOR findings, only one MINOR and some NITs. The sanity file answers both pre-proof referees' MINORs.

**Process disclosure.** I did not modify the repository, git state or `build/`, and the tree was clean before and after. My only scratch file is `/tmp/apipB/c.py`, with Lean outputs captured in `/tmp/apipB/st.txt` and `/tmp/apipB/ax.txt`. One breach of the "one Lean process at a time" rule: my `Axioms.lean` run (step 4) overlapped with an `Axioms.lean` run already in progress (pid 16225, presumably the other referee's). I started mine without checking first. Both were `nice`d and both completed, but for a while two Lean processes were running at once.

## Required runs (verbatim)

**1.** `git rev-parse HEAD` gave:
```
9a79382ab00552443b9945c6cef6651eea3948d7
```
`git status --short` printed nothing (clean tree). `git diff --stat 2ddcbe0 9a79382` touches only three files, so no Lean file changed between the replayed commit and HEAD:
```
 docs/STATUS.md                             |   2 +
 docs/replay/2026-11-07-API1-verify-all.txt | 413 +++++++++++++++++++++++++++++
 review/prompts/API1-post-proof.md          |  24 ++
```

**2.** `nice -n 10 lake env lean StatementTypes.lean` exited 0 with this output:
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
TYPE-OK OscInt.API.ampBoundOfContDiff : OscInt.Statements.AmpBoundOfContDiffStatement
TYPE-OK OscInt.API.d4LimitClosedForm : OscInt.Statements.D4LimitClosedFormStatement
```

**3.** `cat build/commit/commitments.txt`:
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
7db2d5f188ee0984ee684caa10e18c74af554e0c718a903cd643e540d278f741  OscInt.Statements.D4LimitClosedFormStatement
ec40ed3e51ec4cc137fcc2c1a5462f076cabd712d0701b729f9cb64856a50c58  OscInt.Statements.AmpBoundOfContDiffStatement
3f089384d33ac7f6d4a24195c64b10af9093125fec7456da342a0477e510e6cc  OscInt.Statements.D4ConstantClosedFormStatement
```
- **Which commit:** per `docs/replay/2026-11-07-API1-verify-all.txt`, this file was computed by `make verify-all` on 2ddcbe0 (clean tree), not on HEAD.
- **Against the pinned stamp:** `stamps/pins.txt` pins both statements, and the challenge `comparator-API1.json`, to `stamps/20261107T012459Z-2d5356432156`. That stamp's manifest (commit 2d5356432156…) contains:
  - `commitment 7db2d5f188ee0984ee684caa10e18c74af554e0c718a903cd643e540d278f741  OscInt.Statements.D4LimitClosedFormStatement`
  - `commitment ec40ed3e51ec4cc137fcc2c1a5462f076cabd712d0701b729f9cb64856a50c58  OscInt.Statements.AmpBoundOfContDiffStatement`
- **Both lines are identical** to `commitments.txt`. The record also states "commit: … matches its stamp stamps/20261107T012459Z-2d5356432156" for both.
- **Extra check (mine):** at HEAD, the sha256 values of these files equal the manifest entries:
  - `OscInt/Statements/FrontEnd.lean` (4851a954…)
  - `OscInt/Statements/D4Limit.lean`, `D4.lean`, `StationaryPhase.lean`
  - `Challenge/FrontEnd.lean` (c6fb982f…)
  - `comparator-API1.json` (799a507a…)

**4.** `nice -n 10 lake env lean Axioms.lean | grep -E 'OscInt\.API\.(ampBoundOfContDiff|d4LimitClosedForm) |AUDIT-TOTAL'` (exit 0, 6m43s):
```
AUDIT OscInt.API.ampBoundOfContDiff propext,Classical.choice,Quot.sound
AUDIT OscInt.API.d4LimitClosedForm propext,Classical.choice,Quot.sound
AUDIT-TOTAL 536 536
```
The helper `d4Constant_eq_closed` and all six `OscInt.API.Sanity.*` theorems are also clean. There is no `sorry`, `axiom`, `set_option`, `native_decide` or metaprogramming in `OscInt/API.lean`, `OscInt/API/Sanity.lean` or `FrontEnd.lean`.

The replay record (2ddcbe0) has these results:
- verify-all PASS, 9 of 9 steps.
- `comparator-API1.json` accepted against the pinned stamp by 6 kernels; "Your solution is okay!".
- leanchecker passed per module, including `OscInt.API`, `OscInt.API.Sanity` and `OscInt.Statements.FrontEnd`.
- All six export kernels accepted.

## Verdicts

**`OscInt.API.ampBoundOfContDiff` (F1): FAITHFUL, scope full. Pinned to commitment `ec40ed3e51ec4cc137fcc2c1a5462f076cabd712d0701b729f9cb64856a50c58`.**
- **Statement matches the docs.** The type is the stamped `AmpBoundOfContDiffStatement`: ∀ n K A, IsCompact K → ContDiff ℝ n A → tsupport A ⊆ K → ∃ M, AmpBound n K A M. This is exactly F1 in `docs/statements.md`.
- **What `AmpBound` means.** `AmpBound n K A M` = ContDiff ∧ tsupport ⊆ K ∧ ‖iteratedFDeriv ℝ j A k‖ ≤ M for all j ≤ n and all k.
- **The proof is the textbook argument:**
  - each `iteratedFDeriv` is continuous, hence bounded on K by `IsCompact.exists_bound_of_continuousOn`;
  - it vanishes off `tsupport A`, via `tsupport_iteratedFDeriv_subset`;
  - M is the sum of the per-order bounds max(C_j, 0).
- **Edge cases:** n = 0 and K = ∅ are fine, and compactness of K is genuinely used. The loss of uniformity in M is disclosed in the docs.

**`OscInt.API.d4LimitClosedForm` (F2): FAITHFUL to `docs/statements.md` F2, scope full. Pinned to commitment `7db2d5f188ee0984ee684caa10e18c74af554e0c718a903cd643e540d278f741`.**
- **Against the brief's S4, as quoted in statements.md: FAITHFUL-STRONGER.**
  - On Disc C < 0 it states exactly t^{2/3}∫e^{itφ}A → Γ(1/3)²/(√3|Disc C|^{1/6})·A(0).
  - It adds the elliptic branch, Disc > 0, with Γ(1/3)²/Disc^{1/6}.
  - It accepts any C² amplitude with tsupport in the max-norm ball B̄(0, δ).
  - The hypotheses φ(0) = 0 and ∇φ(0) = 0 are the D4-point normalisation the limit needs.
- **Proof.** δ comes from S4.2 (`OscInt.d4Limit`); M comes from F1 on `closedBall 0 δ`; the constant is rewritten through `d4Constant_eq_closed`, which splits on the sign of disc and uses S4.4's two sign clauses.
- **Nothing hidden:**
  - the quantifier order `∃ δ > 0, ∀ A` is the same as in S4.2;
  - the written-out integral is the body of `oscInt2`, since `exact` closes the goal with no conversion;
  - the coercions are identical to S4.2's;
  - the junk value `d4ClosedConstant 0` is unreachable, because the theorem assumes disc ≠ 0.
- **Sign conventions:**
  - x³+y³ has disc −27, one real linear factor: hyperbolic, D4⁺.
  - x³−3xy² has disc 108, three real linear factors: elliptic, D4⁻.
- **Independent numerical check of the elliptic constant.** For x³−3xy² I computed I·J/3 with I = Γ(2/3)/2 and J by quadrature (mpmath, `/tmp/apipB/c.py`): 3.2886794108, against Γ(1/3)²/108^{1/6} = √πΓ(1/6)/3 = 3.2886794109. The two agree to about 2e−11 relative, which is quadrature error at the singular points. This matches the analytic value J = ∫₀^{2π}|cos 3θ|^{−2/3}dθ = 2B(1/2, 1/6), hence c = √πΓ(1/6)/3.

## `OscInt/API/Sanity.lean`

The file answers every pre-proof MINOR, and each theorem tests what it claims.

| Theorem | Answers | What it shows |
|---|---|---|
| `apiSanity_elliptic_hyps` | A-MINOR 2, B-MINOR 2 | The elliptic phase `genCubic 1 0 (-3) 0` = x³−3xy² satisfies F2's phase hypotheses, through the same `cubicCoeffs`, `dd` and `fderiv` that F2 uses, with disc = 108. Genuine. |
| `apiSanity_generic_hyps` | B: "nothing connecting `disc (cubicCoeffs φ)` to a cubic with all coefficients nonzero" | x³+2x²y+3xy²+5y³ satisfies the hypotheses with disc = −367. It goes through `cubicCoeffs_genCubic`, so a permutation of coefficients in `cubicCoeffs` would be caught. |
| `apiSanity_elliptic_constant` | B-MINOR 1 (A-MINOR 1 is answered separately; see below) | `d4ClosedConstant 108 = √π Γ(1/6)/3`. The proof rewrites through `gammaSixth` (Legendre duplication plus Euler reflection) and is not a bare unfolding. The right-hand side is the analytically derived value of c for x³−3xy² (J = 2B(1/2, 1/6), checked numerically above). So a wrong exponent or a missing factor on the elliptic branch would fail this test. |
| `apiSanity_elliptic_bite` | bite | F2 applied to x³−3xy² with a `ContDiffBump` amplitude (A(0) = 1, tsupport = closedBall 0 δ) gives a limit c ≠ 0. This exercises F2 end to end on the Disc > 0 branch: the hypotheses can be met for every δ, and the conclusion forces t^{2/3}|∫e^{itφ}A| ↛ 0. |

Referee A's MINOR 1 ("nothing in Lean ties `d4ClosedConstant` to `d4Constant`") is now answered by the proved S4.4 together with `d4Constant_eq_closed`; that is a stronger answer than any sanity value.

## `OscInt/API.lean` docstring

Overall the docstring is accurate. The F1 and F2 rows of its table match the theorems; references are given at chapter level, are explicitly not re-checked, and point to ROADMAP §6. The points below are about wording.

## Findings

No BLOCKER. No MAJOR.

- **MINOR 1.** The `OscInt/API.lean` docstring says "Every theorem below has, as its type, a statement that was frozen, stamped and reviewed before it was used".
  - It is literally false for the helper `OscInt.API.d4Constant_eq_closed`, which is a bridge lemma and not a frozen statement.
  - For F1 and F2, "reviewed before it was used" is true. But the bridge proofs were drafted before the stamp (the process note in statements.md). A reader could take the sentence as a "statement before proof" claim, which the docs explicitly do not make for F1 and F2.
  - Suggested fix: say "every theorem in the table" and point to the process note.
- **NIT 1.** The S4.2–S4.4 row of the API table gives only the Disc < 0 closed form, Γ(1/3)²/(√3|Disc|^{1/6}). S4.4 and F2 also cover Disc > 0 (Γ(1/3)²/Disc^{1/6}), and the row should say so.
- **NIT 2.** The `apiSanity_elliptic_constant` docstring and the module header call √πΓ(1/6)/3 "an independent value" but do not say where it comes from: c = (Γ(2/3)/2)·2B(1/2, 1/6)/3 for x³−3xy², via J = ∫|cos 3θ|^{−2/3}. A one-line derivation would make the independence checkable. Note also that `gammaSixth` is one of the ingredients of the S4.4 proof (`OscInt/D4/ClosedForm.lean`, h7). This is harmless, since it is a proved Mathlib-level Gamma identity and the target value is derived off-line, but it is worth stating.
- **NIT 3 (carried over, still open).** The `d4ClosedConstant` docstring does not mention its junk value 0 at D = 0. `sanity_AmpBoundOfContDiff_hyps` is still fixed at n = 2. Both are in stamped `FrontEnd.lean`, so they can only be noted, not changed.

## Summary table

| Theorem | Verdict | Scope | Commitment |
|---|---|---|---|
| `OscInt.API.ampBoundOfContDiff` | FAITHFUL | full | `ec40ed3e51ec4cc137fcc2c1a5462f076cabd712d0701b729f9cb64856a50c58` |
| `OscInt.API.d4LimitClosedForm` | FAITHFUL (docs F2); FAITHFUL-STRONGER (brief's S4) | full | `7db2d5f188ee0984ee684caa10e18c74af554e0c718a903cd643e540d278f741` |

The commitments were computed on 2ddcbe0, per the replay record, and equal the pinned stamp `20261107T012459Z-2d5356432156`. HEAD 9a79382 differs from 2ddcbe0 only in the record, STATUS and the prompt.
