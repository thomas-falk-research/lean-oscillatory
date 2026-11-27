# Registration ledger

Every pre-registered numeric or computational test of this repository, in order, including failed, superseded and
abandoned ones. A registration is the commit that adds its file; after that only its run log (if it has one) changes.
Outcomes are quoted from the committed output files; nothing here is a new claim. Numerics are tooling, never evidence
for a Lean theorem (README).

| Date | ID | File | Program and output | Outcome (verbatim from the output) | Status |
|---|---|---|---|---|---|
| 2026-11-08 | P1 | `docs/prereg/2026-11-08-P1-classify.md` | `numerics/src/bin/classify.rs` → `numerics/results-classify-2026-11-08.txt` | control CUSP; L NFD4; six arccos phases NFD4; part B PASS | Completed. The NFD4 verdicts rest on a 2048² grid that cannot see sub-grid cusps (lessons 43); the arccos verdicts are re-examined by CENSUS (model M11) |
| 2026-11-08 | P3b | `docs/prereg/2026-11-08-P3b-leading-term.md` | `numerics/src/bin/spleading.rs` → `numerics/results-spleading-2026-11-08.txt` | RESULT PASS; control discriminating | Completed |
| 2026-11-08 | LE | `docs/prereg/2026-11-08-LE-lattice-constants.md` | `numerics/src/bin/lattice1.rs` → `numerics/results-lattice1-2026-11-08.txt` | OVERALL: PASS; controls c1–c3 fail as required | Completed (uses Landau's constant rounded to 0.7858; no verdict depends on it, `docs/prior_art.md`) |
| 2026-11-08 | VV-classify | `docs/prereg/2026-11-08-VV-classify.md` | `numerics/src/bin/classify_vv.rs` → `numerics/results-classify-vv-2026-11-08.txt` | Q(1) CUSP; Q(0.5) CUSP; Q(3) NFD4; T CUSP; controls C CUSP, S(0.5) CUSP | Completed; the Q(3) verdict is wrong (exact cusp points missed by the grid), retracted by the erratum `docs/design/vector-amplitudes.md` §6 |
| 2026-11-08 | VV-qwz-decay | `docs/prereg/2026-11-08-VV-qwz-decay.md` | `numerics/src/bin/qwz_decay.rs` → `numerics/results-qwz-decay-2026-11-08.txt` | (a) FAIL; (b) PASS; OVERALL: NOT PASS | Completed, failed; criterion (b) found non-discriminating afterwards (erratum §6) |
| 2026-11-09 | CENSUS | spec `docs/prereg/2026-11-09-CENSUS-spec.md`; registration `docs/prereg/2026-11-09-CENSUS-prereg.md` | implementations not yet written | — | Spec FROZEN at 61d227c (2026-11-10, after two spec-fidelity referees); registration DRAFT; no run |
| 2026-11-16 | CTQW-chain | `docs/prereg/2026-11-16-CTQW-chain.md` | `experiments/ctqw-chain/` (reference, circuits, simulators, analysis); no hardware output yet | — | REGISTERED, NOT RUN (Addendum 1 of 2026-11-16, before any run: the first run on a no-cost plan of IBM Quantum, approved by the owner; to be stamped before the first job): reference values certified, three implementations agree, tolerances fixed from a simulated noise model; a hardware run needs the owner's approval |
| 2026-11-19 | SPL | `docs/prereg/2026-11-19-SPL-quadratic-remainder.md` | `numerics/review/spl_remainder_checks.py` (SHA-256 at registration 80ba7065d7745e2bc36fd909bf287c2d919301fd980323adecea22ab754db5f1) → `numerics/results-spl-remainder-checks-2026-11-19.txt` (run 2026-11-19T22:05:36Z, after the registration commit 7f54a0b; exit code 0) | OVERALL: PASS (12 of 12 lines PASS); controls C1–C4 came out as required | Completed |
| 2026-11-20 | TSD | `docs/prereg/2026-11-20-TSD-core.md` | `numerics/review/tsd_core_checks.py` (SHA-256 at registration c057a781a5dd1db0d09dd48159369c2569d8235d0de3e5299e1de41e6ea0201e) → `numerics/results-tsd-core-checks-2026-11-20.txt` (run 2026-11-20T17:45:48Z, after the registration commit 4c67249 was pushed; exit code 1) | OVERALL: FAIL (4 of 6 lines PASS): (h), (a), K1 and K2 PASS; (q) and (im) FAIL, in case C9 only | Completed; the failing criteria are quadrature criteria, and the claim under test, (a), holds in all nine cases; a second registration resolves C9 |
| 2026-11-20 | TSD-2 | `docs/prereg/2026-11-20-TSD-core-2.md` | `numerics/review/tsd_core_checks2.py` (SHA-256 at registration 8b09702ee47f1c65ad6292da65d846023b942bdb3c7572bac404a01646fc677c) → `numerics/results-tsd-core-checks2-2026-11-20.txt` (run 2026-11-20T17:49:46Z, after the registration commit 44dd583 was pushed; exit code 0) | OVERALL: PASS (6 of 6 lines PASS); controls K1 (8 of 9) and K2 (7 of 9) came out as required | Completed; registered with knowledge of the first run, so it decides the cause of that run's failure and is not an independent test of (a) |
| 2026-11-27 | TRI | `docs/prereg/2026-11-27-TRI.md` | `numerics/review/tri_checks.py` (SHA-256 at registration 1446a8d4dea8675a6e582114bd1b02f00db754c85d3c0629062441df5a402d81) → numerics/results-tri-checks-2026-11-27.txt (not yet run) | (not yet run) | Registered; confirms known numbers (not blind, see the registration) |

Earlier numeric checks were not pre-registered as such: `numerics/results-2026-11-05.txt` (S1 constants, `make numerics`,
`docs/progress.md`) and `numerics/results-d4const-2026-11-06.txt` (D4 closed forms, `docs/decisions/2026-11-06-S4.md`).
Symbolic checks of a specification (not tests of a hypothesis) are recorded with the specification they support:
`numerics/census/spec_checks.py` → `numerics/results-census-spec-2026-11-09.txt`, superseded on 2026-11-10 by
`numerics/results-census-spec-2026-11-10.txt` after control K-QWZm was added before registration, and regenerated after
the spec referees' repairs (39/39 at the frozen spec commit 61d227c; checks R4, CORPUS and M07-LINES added) (CENSUS).

<!-- Attribution, appended 2026-11-19 by owner decision; the text above is the record as written.
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
SPDX-License-Identifier: CC-BY-4.0 -->
