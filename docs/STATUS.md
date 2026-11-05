# Status

One line per statement. A status is derived from evidence files, never typed as a claim; "machine-checked as stated"
requires every row of the trust chain (README) for that statement.

| Statement | Lean | Statement frozen | Blind review | Proof | Replay | Status |
|---|---|---|---|---|---|---|
| S1 1D van der Corput | `OscInt.Statements.VdC{1,2,3}Statement` | yes (commitments in `stamps/`) | pending | — | — | statement frozen; port of roos-j/lean-oscillatory chosen (owner, 2026-11-05) |
| S2 2D nondegenerate stationary phase | — | no | — | — | — | not started |
| S3 uniform fold | — | no | — | — | — | not started |
| S4 uniform D4 | — | no | — | — | — | not started |

Pipeline skeleton (M0): `OscInt.skeleton_two_mul` builds, audits clean (1 of 1) and replays in six kernels
(`build/replay/summary.txt` from `make lean-replay`; the CI run on each push records it).
