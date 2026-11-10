# Review records

**What is here.** The lead's answers to every review, each finding stated in the lead's words with its severity and
the evidence it cites, plus the calibration test data (planted statement variants and answer keys).

**What is not here (owner privacy rule, `docs/lessons.md` 46).** On 2026-11-10 the following were removed from the
current tree:
- the referee prompts and briefs (`review/prompts/`);
- the verbatim referee and agent reports (pre-proof, post-proof, adversarial, route, agent reports, calibration
  reports);
- the CENSUS prior-art sweep report and its query log.

They remain in git history, and `main`'s history was deliberately not rewritten, because that would invalidate every
stamp. A path under `review/` cited elsewhere in the repository that no longer exists can be read with
`git show 58a86d0:<path>`. New reviews follow CONTRIBUTING step 5: no prompts, no verbatim reports, findings in the
lead's words in an answers file.

**Naming.** `<date>-<batch>-<kind>-answers.md`, where kind is `pre-proof`, `post-proof` or `route`; adversarial-review
answers use plain `-answers`. External reviews are `<date>-external-<topic>-answers.md`.

## Answers

- `2026-11-05-S2S3-pre-proof-answers.md`
- `2026-11-06-S2S3-answers.md`
- `2026-11-06-S4-answers.md`
- `2026-11-06-S4-pre-proof-answers.md`
- `2026-11-06-S4b-answers.md`
- `2026-11-06-S4b-pre-proof-answers.md`
- `2026-11-07-API1-answers.md`
- `2026-11-07-API2-answers.md`
- `2026-11-07-API2-pre-proof-answers.md`
- `2026-11-07-S44-answers.md`
- `2026-11-08-API3-answers.md`
- `2026-11-08-API3-pre-proof-answers.md`
- `2026-11-08-GD-post-proof-answers.md`
- `2026-11-08-GD-pre-proof-answers.md`
- `2026-11-08-LE-post-proof-answers.md`
- `2026-11-08-LE-pre-proof-answers.md`
- `2026-11-08-VT-pre-proof-answers.md`
- `2026-11-08-step5-rule-answers.md`
- `2026-11-09-A3-pre-proof-answers.md`
- `2026-11-09-VT-post-proof-answers.md`
- `2026-11-10-external-audit-answers.md`
- `2026-11-10-external-dossier-answers.md`
- `2026-11-10-external-results-answers.md`

## Calibration test data

- `calibration/round1/`: six planted statement variants (`V*-Statements.lean.txt`) and `key.json`.
- `calibration/round2/`: six planted variants, the base statements, the statement prose and `key.json`.
