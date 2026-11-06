# Status

One line per statement. A status is derived from evidence files, never typed as a claim; "machine-checked as stated"
requires every row of the trust chain (README) for that statement.

| Statement | Lean | Statement frozen | Blind review | Proof | Replay | Status |
|---|---|---|---|---|---|---|
| S1 1D van der Corput | `OscInt.vanDerCorput_one/two/three` | yes, stamp `20261105T203058Z-7516eb518dce` (pinned) | pre: FAITHFUL ×3; post: FAITHFUL ×3, scope full | yes | 7 kernel runs + comparator | machine-checked as stated |
| S2.1 non-stationary phase | `OscInt.nonStationary` | yes, stamp `20261105T234456Z-533ae0272521` (pinned) | pre: FAITHFUL ×2; post: FAITHFUL ×2, scope full | yes | 7 kernel runs + comparator | machine-checked as stated |
| S2.2 nondegenerate stationary phase | `OscInt.stationaryPhase` | yes, stamp `20261105T234456Z-533ae0272521` (pinned) | pre: FAITHFUL ×2; post: FAITHFUL ×2, scope full | yes | 7 kernel runs + comparator | machine-checked as stated |
| S3 uniform fold | `OscInt.fold` | yes, stamp `20261105T234456Z-533ae0272521` (pinned) | pre: FAITHFUL ×2; post: FAITHFUL ×2 to the docs (one referee: FAITHFUL-WEAKER than the classical form), scope full | yes | 7 kernel runs + comparator | machine-checked as stated (fold condition on all of K) |
| S4.1 uniform D4 bound | `OscInt.d4Bound` | yes, stamp `20261106T033706Z-63564a8d78cd` (pinned) | pre: FAITHFUL ×2; post: FAITHFUL ×2 to the docs, FAITHFUL-WEAKER than the classical form (D4⁺ only, as the brief), scope full | yes | 7 kernel runs + comparator | machine-checked as stated (hyperbolic umbilic D4⁺) |
| S4.1′ uniform D4 bound, both umbilics (`disc ≠ 0`) | `OscInt.d4BoundNe` | yes, stamp `20261106T081634Z-e2d7771c358e` (pinned) | pre: FAITHFUL ×2 (STRONGER than the brief) | yes (same parts as S4.1, assembly `d4BoundNe_of`) | pending final verify-all | proved; replay pending |
| S4.2 D4 limit t^{2/3}∫e^{itφ}A → c_C A(0) | `OscInt.Statements.D4LimitStatement` | yes, stamp `20261106T081634Z-e2d7771c358e` (pinned) | pre: FAITHFUL ×2 | — | — | statement frozen, proof not started |
| S4.3 c_C > 0 (alternating series, Gamma-free) | `OscInt.Statements.D4ConstantPosStatement` | yes, same stamp | pre: FAITHFUL ×2 | — | — | statement frozen; Gamma-free check pre-registered (`GammaFree.lean`) |
| S4.4 closed forms of c_C | `OscInt.Statements.D4ConstantClosedFormStatement` | yes, same stamp | pre: FAITHFUL ×2 | — | — | statement frozen, proof not started |

Pipeline skeleton (M0): `OscInt.skeleton_two_mul` builds, audits clean (1 of 1) and replays in six kernels
(`build/replay/summary.txt` from `make lean-replay`; the CI run on each push records it).

S1 (2026-11-05). `OscInt.vanDerCorput_one`, `_two`, `_three` prove `VdC1Statement`, `VdC2Statement`,
`VdC3Statement` (constants 3, 8, 18; amplitude form; linear term in k = 2, 3). Evidence: axiom audit 36/36; statement
types checked syntactically; commitments recomputed and equal to the pinned stamp; `lake comparator --paranoid`
accepted against the stamped challenge export; replay by Lean's kernel (default, paranoid), nanoda, con-leche,
con-ron and lean4lean (`docs/replay/2026-11-05-M1-verify-all.txt`); blind pre-proof and post-proof reviews FAITHFUL
(`review/`), adversarial review answered. Proof route ported from J. Roos and M. Praveen, `roos-j/lean-oscillatory`
(Mathlib PR #39406), by four proof agents (parts P0–P4) and the lead (statements, blueprint, assembly). Relative to
Stein the theorems are weaker in the phase (φ′ differentiable; lower derivatives continuous up to the endpoints) and
more general in the amplitude (ψ′ only integrable). Reviewers are AI agents; no human has read the statements yet.

S2/S3 (2026-11-06). Proved: `OscInt.nonStationary`, `OscInt.stationaryPhase`, `OscInt.fold` (route
`docs/proof-S2S3.md`, parts by proof agents G1–G3 and H1–H6, assembly by the lead). Caveat on the review evidence:
referee calibration round 1 used short S1 statements; the S2/S3 statements are longer and use more Mathlib
machinery, a regime round 1 did not test (`docs/calibration.md`).

Final record for S2/S3: `docs/replay/2026-11-06-S2S3-final-verify-all.txt` (commit d932c0d, PASS 8/8: axiom audit
276/276, six commitments equal to the pinned stamps, comparator accepted both configurations, replay by per-module
`leanchecker` and six export kernels, both pinned stamps verified). Reviews: `review/2026-11-05-S2S3-pre-proof-{A,B}.md`,
`review/2026-11-05-S2S3-proof-route.md`, `review/2026-11-06-S2S3-post-proof-{A,B}.md`, `review/2026-11-06-S2S3-adversarial.md`
with answers in `review/2026-11-06-S2S3-answers.md`. "As stated" includes S3's hypothesis at every point of K
(`docs/statements.md`, clarification of 2026-11-06). Reviewers are AI agents; no human has read the statements.

S4.1 (2026-11-06). Proved: `OscInt.d4Bound` (route `docs/proof-S4.md`, refereed in
`review/2026-11-06-S4-proof-route.md`; blueprint `Blueprint/D4.lean`, parts D1–D9 by proof agents P, Q, R, S;
assembly `OscInt.D4.d4Bound_of` by the lead, from S3 and S2.1). Record: `docs/replay/2026-11-06-S4-verify-all.txt`
(commit a0b1fde, PASS 8/8: axiom audit 365/365, seven commitments equal to the pinned stamps, comparator accepted all
three configurations, per-module `leanchecker` and six export kernels); CI run 42172708736 green on a0b1fde. Reviews:
`review/2026-11-06-S4-pre-proof-{A,B}.md`, `review/2026-11-06-S4-post-proof-{A,B}.md`,
`review/2026-11-06-S4-adversarial.md`, answers in `review/2026-11-06-S4-answers.md`. Scope: `disc < 0` is the
hyperbolic umbilic D4⁺, which is the brief's case ("an isolated critical point and negative discriminant"); the
proof uses only `disc ≠ 0`, so D4⁻ is a small extension if the owner widens the statement. Non-vacuity:
`OscInt/D4/Sanity.lean`, `OscInt/D4/Bite.lean`.

S4.1′–S4.4 (2026-11-06). Decisions: `docs/decisions/2026-11-06-S4.md` (c_C defined Gamma-free; widening to
`disc ≠ 0` as a new statement; nanoda built from source in CI). The brief's S4 limit with its constant is S4.2 ∧ S4.4
(Disc < 0 clause), and "c_C ≠ 0" is S4.3; none is proved yet. Reviews: `review/2026-11-06-S4b-pre-proof-{A,B}.md`,
answers `review/2026-11-06-S4b-pre-proof-answers.md`.
