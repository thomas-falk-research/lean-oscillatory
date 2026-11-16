# Application package (draft for the owner's review; nothing submitted)

Target: the EuroHPC Joint Undertaking **Quantum Access Pilot Mode**, cut-off **1 December 2026, 10:00 CET**
(`docs/funding/00-call-findings.md`). The owner fills in the placeholders, checks eligibility, copies the portal's
field list, and submits. This branch is public: the drafts contain only public facts about OscInt.

| File | Section | Status |
|---|---|---|
| `docs/funding/00-call-findings.md` | what is open, verified from the official pages | done |
| `docs/funding/01-scientific-case.md` | scientific case | draft |
| `docs/funding/02-work-plan.md` | work plan | draft |
| `docs/funding/03-resources.md` | resources requested, with justification; Development Access annex | draft |
| `docs/funding/04-impact-and-risks.md` | expected impact; risks | draft |
| `docs/funding/05-data-software-open-science.md` | data and software management plan; open-science statement | draft |

## Placeholders the owner fills in

| Placeholder | What goes there |
|---|---|
| `[APPLICANT-NAME]` | project leader |
| `[APPLICANT-AFFILIATION]` | employing organisation, or "none" (then settle eligibility first) |
| `[APPLICANT-COUNTRY]` | country of residence or establishment |
| `[APPLICANT-LEGAL-FORM]` | natural person, company, research organisation |
| `[CONTACT-EMAIL]` | contact address |
| `[TEAM]` | people and their time, in person-months |
| `[TARGET-SYSTEM]` | the quantum system requested; the drafts assume Euro-Q-Exa |
| `[CALIBRATION-DATA]` | qubit count, topology, native gates, gate and readout errors and shot rate of the target system, from the hosting site's documentation (not read in this session) |

## What the owner must do before submitting

1. Settle eligibility (an employment contract with an organisation is named in the Development and Benchmark rules; the
   quantum pilot's rule says "users residing, established or located in" an eligible country).
2. Log in to the access portal, open call 61, and copy the form's fields and length limits; cut the sections to fit.
3. Re-read the systems table on the call page (it was read once, from an image) and fill `[CALIBRATION-DATA]`.
4. Approve or change the experiment (`docs/funding/02-work-plan.md`); the protocol is registered before any run.

## Rules these drafts follow

Every claim about OscInt cites a path in this repository or carries an evidence label (`docs/README.md`, glossary).
Statement fidelity has been reviewed by AI referees, not yet by a human expert (`docs/policy.md`), and the drafts say
so wherever they say "machine-checked". Nothing is described as new physics.
