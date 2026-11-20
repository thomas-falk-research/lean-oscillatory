<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Security policy

OscInt is a library of machine-checked mathematics. What it protects is a claim: that each theorem listed in
`stamps/statements.json` is proved from three standard axioms, for a statement that was frozen and reviewed, in a
pinned environment. A security problem here is anything that lets that claim appear to hold when it does not.

## What to report privately

- A way to make `make verify-all`, the replay driver, the comparator or `tools/oscint_check.py` report success for
  a statement that is not proved, for a statement file or a commitment that differs from its stamp, for an added
  axiom, or for a declaration that the kernel did not check.
- A way to change a frozen statement, a pin, a stamp or a release so that the tools do not notice.
- A flaw in how the timestamps, the pins or the release attestations are produced or verified.
- A leaked credential, or a way for a pull request or a workflow run to reach one.
- A problem in a dependency (toolchain, Mathlib, the Rust and Python tools) that has one of these effects.

An error in the mathematics, a statement that does not say what its description says, or a wrong sentence in a
record is not a security problem: open an ordinary issue. Those reports are as welcome.

## How to report

Use "Report a vulnerability" on the repository's Security tab (GitHub private vulnerability reporting), or write to
<research@thomas-falk-research.com>. Please include the commit, the command, and what you observed. Do not open a
public issue for the items above before a fix or a statement is out.

## What to expect

This is a one-person research project. Reports are read by the owner; there is no service-level promise. A
confirmed problem is fixed on the development branch, described in `CHANGELOG.md` and in `docs/lessons.md` with the
check that now prevents it, and, where a release is affected, in the notes of the next release. Reporters are
credited unless they ask not to be.

## Supported versions

The development branch and the latest release. Earlier releases are not patched; their notes
(`docs/release-notes/`) record the pins they were checked against.

## Known limits

`README.md`, sections "Known caveats" and "What stays trusted", lists what the checks do not cover. Run from inside
the package, `tools/oscint_check.py` detects accidental drift, not deliberate tampering; `docs/downstream.md` says
how to pin against tampering.
