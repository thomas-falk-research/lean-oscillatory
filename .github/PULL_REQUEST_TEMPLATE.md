<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

## What this changes

<!-- One paragraph: what, and why. Name the statements, tools or documents touched. -->

## Checks run

- [ ] `make quick` (or `make docs-check` for a documentation-only change): exit code and time
- [ ] tool tests (`make tools-test`) if anything under `tools/` changed
- [ ] `reuse lint`; every new file names its copyright and licence

## Rules (`CONTRIBUTING.md`, "Rules in force" in `docs/lessons.md`)

- [ ] No frozen statement file, challenge file, stamp or record is edited (the fixed attribution block aside)
- [ ] No statement or test is weakened to get green; no `sorry`, no new axiom
- [ ] A new statement follows the order: prose, Lean statement with sanity layer and plants, challenge, stamp,
      blind review, then proofs
- [ ] Every number in a record comes from a command that was run; the command is in the session log
- [ ] `docs/STATUS.md` claims nothing that has no evidence file yet
- [ ] AI use is disclosed (which agents drafted what)

## Not done, or left open

<!-- Say it plainly. -->
