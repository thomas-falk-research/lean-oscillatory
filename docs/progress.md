# Progress log

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
