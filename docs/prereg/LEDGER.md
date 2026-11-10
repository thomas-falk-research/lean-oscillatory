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

Earlier numeric checks were not pre-registered as such: `numerics/results-2026-11-05.txt` (S1 constants, `make numerics`,
`docs/progress.md`) and `numerics/results-d4const-2026-11-06.txt` (D4 closed forms, `docs/decisions/2026-11-06-S4.md`).
Symbolic checks of a specification (not tests of a hypothesis) are recorded with the specification they support:
`numerics/census/spec_checks.py` → `numerics/results-census-spec-2026-11-09.txt`, superseded on 2026-11-10 by
`numerics/results-census-spec-2026-11-10.txt` after control K-QWZm was added before registration, and regenerated after
the spec referees' repairs (39/39 at the frozen spec commit 61d227c; checks R4, CORPUS and M07-LINES added) (CENSUS).
