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
