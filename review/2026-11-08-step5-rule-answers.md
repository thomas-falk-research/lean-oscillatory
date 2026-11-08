# Answers to the step-5 rule referee (2026-11-08)

Report (verbatim): `review/2026-11-08-step5-rule-referee.md`, on bbafeeb; prompt
`review/prompts/2026-11-08-step5-rule-referee.md`. Verdict ADOPTABLE-WITH-CHANGES. The referee wrote nothing in the
repository. The lead re-checked findings 1 and 2 against git before acting; both hold.

- **1 (BLOCKER), waiver overstates.** Agreed. The waiver is replaced by the referee's §F.2 text, with the commit
  filled in by today's re-run record (memo §3(iii)).
- **2 (MAJOR), "second part of the plant record" does not exist.** Agreed: `git log` shows one commit for
  `docs/replay/2026-11-08-API3-sanity-plants.txt`. The S2.2F plant sources were re-run today and recorded with output:
  `docs/replay/2026-11-08-session6-API3-plants-rerun.txt` (both plants fail at `binder_nondeg`, the discharge of the
  mutated hypothesis; unplanted copy compiles; the six earlier plants reproduce). The answers file
  `review/2026-11-08-API3-answers.md` gets an erratum line pointing here (the wrong sentence is kept, struck through
  by the erratum, not deleted).
- **3–7, 9–11, 13, 14, 16 (rule design).** Agreed. The memo no longer recommends a general exception; the referee's
  corrected text §F.1 is offered as option (i) verbatim by reference, with the consequence (API3 does not qualify)
  stated.
- **8 (MAJOR), comparative wording.** Agreed; memo §4 uses the referee's sentence.
- **12 (MINOR), amend step 2.** Agreed; it is the core of the recommended option (iii) (§F.3 text, with "with the
  compiler output" added, from finding 13).
- **15 (MINOR), lead's changes in the referee's file.** Agreed; they are here.
- **17 (NOTE), STATUS row 33 says "answered".** Agreed; changed to "addressed by conditional sanity theorems
  (owner decision pending)".
