# Progress log

Sessions 1–3 only. Sessions 7–10 are in `docs/HANDOFF.md` (newest first); sessions 4–6 are in its git history and in
`CHANGELOG.md`.

## 2026-11-05 — M0
Toolchain v4.35.0 and elan v4.2.4 installed from hash-pinned downloads; the installed toolchain is byte-identical to
the pinned archive. Mathlib pinned at tag v4.35.0. Library skeleton with one theorem; axiom audit enumerating
theorems from the environment and cross-checked against a lexical count; statement-type checker; Rust tools (guard,
audit, replay, commit, challenge, stamp, toolchain, verify_all; 17 unit tests, none for the orchestration-only `challenge` and `toolchain`). Commitment producers agreed byte
for byte on a 4810-constant probe closure, after binder data was dropped from the format (lessons 4). Negative
controls: `native_decide`, `sorryAx`, a kernel-bypassed `1 = 2` (lessons 3), a stale olean, an empty export.
Prior-art gate: S1 anticipated (roos-j/lean-oscillatory, Mathlib PR #39406), S2 partial, S3 and S4 not found.
M1 not started, pending the owner's decision on S1.

CI run 1 (https://github.com/thomas-falk-research/lean-oscillatory/actions/runs/42099595128, commit `80d59ea`):
verify-all INCOMPLETE (PASS: verify-toolchain, tools-test, guard, lean, lean-replay; SKIPPED: commit, comparator,
stamp-verify, nothing to check yet). The CI export of the skeleton had the same SHA-256 as the local one
(`c266c461…`).

Numerics (`make numerics`, output `numerics/results-2026-11-05.txt`): none of the S1 constants is exceeded on 9 probe
families (worst ratio 0.53); m|I| (S2, indefinite), m^{5/6}|I| (S3, fold) and t^{2/3}|I| (S4) are flat in m, and the
D4 limit for x³+y³ matches Γ(1/3)²/(√3·27^{1/6})·A(0) to 3·10⁻⁶ at t = 3000; for x²y+y³ (Disc −4) the 2D quadrature
reaches 0.441 at t = 300 against the predicted 0.445 and is still increasing.

## 2026-11-05 — M1 (S1, van der Corput)
Owner chose to port roos-j/lean-oscillatory. Statements `VdC{1,2,3}Statement` written with `docs/statements.md`,
sanity theorems, challenge copy; commitments agree between producers; stamped (`stamps/20261105T203058Z-7516eb518dce`,
RFC 3161 ×3, OpenTimestamps ×2). Blind pre-proof review FAITHFUL ×3. Blueprint P0–P4; four proof agents in parallel
(P2 in ~1.5 min, P3–P4 ~2 min, P0 ~2 min, P1 ~6 min of agent time; 84 + 137 + 104 + 234 lines) plus the lead's
assembly (55 lines) and final file. Post-proof review FAITHFUL ×3 (scope full). Adversarial review: 2 MAJOR (no
recorded comparator/commitment verdict; stamped commitments not enforced, newest stamp used) fixed by
`stamps/pins.txt` enforcement and a committed `verify-all` record; MINORs fixed or answered (`review/`). CI had been
red since the stamp (lessons 9), fixed.

## 2026-11-05/06 — session 2 (raise the bar)
Mathlib-from-source CI job made to prove it compiled Mathlib (count of `Built Mathlib.*`, no fetched/replayed
modules); first run compiled 2512 modules, then failed on `MathlibNames.lean` (needs all of Mathlib); fixed to build
all of Mathlib. Calibration round 1: 4/4 planted errors caught, 0/2 false alarms. S2.1/S2.2/S3 statements frozen
with C² amplitudes and compact families (needed by S4), stamped, two independent blind reviews FAITHFUL ×3.
On-paper route refereed (no BLOCKER, amendments folded in). Infrastructure parts F1a–d, F2a–b proved by three agents;
agent G3 caught `ContDiff ℝ ⊤` = analytic in the blueprint with a Lean counterexample (lessons 12, guard check
added). Analytic parts launched to six agents; lead's assembly of S2.2/S3 from interfaces compiled.
Analytic parts proved by agents H1–H6; S2.1, S2.2, S3 machine-checked as stated (final record
`docs/replay/2026-11-06-S2S3-final-verify-all.txt`, d932c0d, PASS 8/8; post-proof FAITHFUL ×2; adversarial answered).

## 2026-11-06 — S4.1 (uniform D4⁺ bound)
Statement frozen and stamped (`20261106T033706Z-63564a8d78cd`), blind pre-proof FAITHFUL ×2 (D4⁺ only, as the
brief). Route by dyadic rescaling to S3 (`docs/proof-S4.md`), refereed; blueprint D1–D9; the lead's assembly
`d4Bound_of` compiled against the parts before any part was proved; parts by agents P, Q, R, S. Record
`docs/replay/2026-11-06-S4-verify-all.txt` (a0b1fde, PASS 8/8); post-proof FAITHFUL ×2; adversarial answered.
Calibration round 2 (S2–S4 statements, separate planter, sealed key): 4/4 detected, 0/2 false alarms; pooled 8/8,
95% CP [0.63, 1]; lesson 17 (generic sanity witnesses).

## 2026-11-06 — S4 decisions, S4.1′, S4.2, S4.3
The owner delegated three decisions (`docs/decisions/2026-11-06-S4.md`): c_C defined Gamma-free with the limit
(S4.2), positivity (S4.3) and closed forms (S4.4) as separate statements; S4.1′ for `disc ≠ 0` (both umbilics);
nanoda built from source in CI at `8de7e0c` (first run: CI run 58, accepted). Numerical validation
(`numerics/src/bin/d4const.rs`): closed forms for both signs to ≤ 8e-15 on eight cubics, including the elliptic
constant Γ(1/3)²/Disc^{1/6}. Four statements stamped (`20261106T081634Z-e2d7771c358e`), blind pre-proof FAITHFUL ×2.
S4.1′ proved by generalising the S4.1 assembly. S4.3: route by one integration by parts and pairing the humps of
sin u·u^{-4/3} (no numerical margin), refereed; parts by agents U, V, W. `GammaFree.lean` found not to follow
proofs (lesson 18), fixed with a proof-only control; the S4.3 proof's closure (43 612 constants) is clean.
S4.2: route by rescaling at R t^{-1/3}, dominated convergence and a polar evaluation via a radial identity,
refereed; assembly `d4Limit_of` by the lead, parts by agents X, Y, Z, Q2. Records
`docs/replay/2026-11-06-S4b-verify-all.txt` (a71b318) and `-S4b-final-verify-all.txt` (17e5478): every proved
configuration accepted by the comparator and six kernels; INCOMPLETE only for S4.4. Post-proof FAITHFUL ×2 for
S4.1′, S4.2, S4.3; adversarial (bite for both umbilics, seven Gamma-hiding attempts rejected) answered.
Open: S4.4.

## 2026-11-06/07 — session 3 (S4.4; depending on OscInt)
Housekeeping: build-noise diff of 7bd3151 re-applied (0 warnings), `lakefile.toml` 0.2.0; verify-all on 828309a failed
only for missing `zstd`, `bwrap` and a shallow clone, the three steps passing after installing and unshallowing
(record `docs/replay/2026-11-06-housekeeping-verify-all.txt`; lessons 21, preflight added). S4.4: the hand-off's route
needed a complex-rate Gamma integral that Mathlib does not state (lessons 19); new real-variable route
(`docs/proof-S44.md`): Fubini and dominated convergence for the cosine moment, the chart u = tan θ, GL₂ covariance of
J by polar coordinates and a linear change of variables, reduction to x(x² + y²) and xy(x + y), Beta integrals,
duplication and reflection. Blueprint E1–E7 with the lead's assembly checked first; the route referee found a
blueprint name clash (lessons 20). Parts by agents M, N, O, T (2.5–6 min each) and K (9.5 min, resumed after a
container restart); E4, E7 and the assembly by the lead. verify-all PASS on 1c7ebe3 (the first full PASS);
post-proof FAITHFUL ×2; adversarial: no finding on S4.4. S4.4 machine-checked as stated, so all eleven pinned
statements are. Depending on OscInt: `stamps/statements.json`, `tools/oscint_check.py`, `examples/consumer/`,
`docs/policy.md`, `CONTRIBUTING.md`, CI split (`quick`, `verify`, `consumer`). The adversarial referee broke the first
checker (a redefined statement and a kernel-skipped theorem both passed; lessons 22); hardened (module of the
statement, kernel replay of the dependency closure, recomputed commitments, toolchain and Mathlib match) with 13
negative controls and the referee's two reproductions now rejected. Front-end batch 1 (F1, F2) drafted.
Front-end batch 1 (2026-11-07): F1 (amplitude bounds from `ContDiff` and compact support) and F2 (the D4 limit with
its closed-form constant for one C² amplitude) frozen, stamped `20261107T012459Z-2d5356432156`, reviewed FAITHFUL ×2,
proved in `OscInt/API.lean` (the new entry point) with a bite file, verify-all PASS on 2ddcbe0, post-proof FAITHFUL ×2.
The bridges were drafted before the review (lessons 23). The audit's strict count caught two `private theorem`s,
which it does not enumerate (CONTRIBUTING). `statements-check` now reports INCOMPLETE, not FAIL, for a new
statement file not yet stamped (lessons 9).
