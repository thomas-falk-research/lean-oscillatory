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
