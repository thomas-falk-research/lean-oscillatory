<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# 5. Data and software management plan; open-science statement

The call asks for no data management plan. This section documents what the project already does and what it commits
to for the hardware data.

## 5.1 Software

- **Repository.** Public, `thomas-falk-research/lean-oscillatory`; code under Apache-2.0, documentation under
  CC BY 4.0 (`LICENSE`, `LICENSE-docs`, `REUSE.toml`).
- **Releases.** Tagged releases with a Zenodo record per version and a concept DOI, 10.5281/zenodo.24021328
  (`CITATION.cff`); release assets carry a build-provenance attestation (`docs/policy.md`).
- **Reproducibility.** The Lean toolchain is pinned by hash (`toolchain.sha256`) and Mathlib by commit
  (`lake-manifest.json`); `make verify-all` rebuilds, audits the axioms and replays every proof in six kernels
  (`CONTRIBUTING.md`).
- **Experiment code.** The circuit generator, the reference computation and the analysis script will be in the same
  repository, with pinned dependencies recorded at run time by the running interpreter.

## 5.2 Data

| Data | Format | Where | When public |
|---|---|---|---|
| registered protocol | Markdown, time-stamped | `docs/prereg/` | before the first run |
| certified reference values | text records with the script's SHA-256 | `numerics/` | already public for the 9-site chain |
| raw hardware counts with back-end name, calibration snapshot, job identifiers, seeds | JSON | the repository if small, otherwise a Zenodo deposit linked from it | with the final report |
| analysis outputs | text and JSON | the repository | with the final report |

Raw data is never edited after acquisition; corrections are new files. Failed and abandoned runs are kept and listed,
as the registration ledger already does for numerical tests (`docs/prereg/LEDGER.md`). No personal data is collected.

## 5.3 Open-science statement

Everything the project produces under this allocation is public: protocol before the run, code, raw data, analysis
and report, under the licences above. The registration fixes the analysis before any data exists, and the ledger
records every registered test including the ones that fail. The use of AI tools in proofs and reviews is disclosed
per statement (`docs/prior_art.md`, `docs/STATUS.md`): the lead, the proof agents and the referees are AI systems of
one model family, an external AI tool drafted some proofs, and no human expert has yet reviewed the fidelity of the
statements. The results will not be used for military purposes, as the access rules read for the sibling EuroHPC calls require.
