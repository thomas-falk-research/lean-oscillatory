<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# The post-K2 research packet of 2026-11-28: intake, re-run, and what follows (session 17)

Written by the lead, in the lead's words (lessons 46). This record exists before any statement of batches SPL-N, A5U
or LOC2 is frozen, as rule 2 of `docs/lessons.md` requires: it says what the packet contained, what was run or
compiled, when, and how the batches relate to it.

## 1. Provenance

- Delivered by the owner into the session at 12:08:17Z on 2026-11-28 (file time of the upload): an archive
  `oscint-frontier-post-K2-2026-11-28.zip` of 139 743 bytes and a companion checksum file.
- SHA-256 of the archive: `498ca140a4ae3c8928fb33f40c2737de43dde2e4c85cc2d42d26197f106ca227`, equal to the companion
  file's digest (companion file SHA-256 `e708713cc88eff60428218a1e38734524a8fa1f3e9507c7277bb3a59dafd0686`).
- Listed before extraction: 79 entries, all under one top directory, no absolute path, no `..`, no symbolic link.
  Extracted into the session scratch directory, outside the repository. The internal manifest `SHA256SUMS` (SHA-256
  `d9912a8ba8d5558848876adb413f09e109c77d6c0eeaf143ba5a289835449c49`) lists 78 files; all 78 verify, and the archive
  holds no other file. Integrity only: it says nothing about authorship or truth.
- The packet says of itself that it is external research, written against `main` at
  `5356e592514bc7372268d884733970f7d6baa177` (the merge of pull request 26). `main` was at that commit when this session
  read the remote state at 12:0xZ, so there is no drift.
- It contains no Lean proof text. It contains Python scripts (exact rational producers and checkers, symbolic checks,
  a synthetic Git fixture) and prose work packages for SPL-N, Report D, the A5 crossover, localisation and F-a, the
  push gate, a finite-range group (HOP), Strichartz estimates (PDE), operator material and an archive of older survey
  material.

## 2. What was run, and the results

Every script was read as text before it ran. They use the Python standard library (and SymPy for two), write only
to paths given on the command line or to temporary directories, start only the sibling checker or `git` in a
temporary repository, and make no network access. They ran with `python3 -I` from a working directory outside the
packet (one, the encoding test, imports its sibling module and ran without `-I`). Interpreter: Python 3.13.18; SymPy
was not installed system-wide, so the two symbolic scripts were run again with SymPy 1.14.0 (the version the packet
names) and mpmath 1.3.0 in a scratch virtual environment. Git 2.43.0.

All commands of the packet's reproduction list, run one by one with their own exit status (12:12:59Z to 12:13:45Z):

| Check | Result |
|---|---|
| packet manifest; pre-execution manifest of the SPL protocol; revised-execution hash | all OK |
| SPL producer, output against the packet's `results/spl-cells.json` | byte-identical; 11 cells for 73/100, 40 for 360987/500000 |
| SPL checker, normal and `-O` | PASS upper 73/100, upper 360987/500000, lower 72197399/10⁸ at 8123/5000 |
| SPL negative controls, normal and `-O` | 18 of 18 rejected with exit 1 and a `REJECT` message; log byte-identical to the packet's |
| A5 jets and interval-count arithmetic; identities | PASS (with SymPy 1.14.0; the first attempt without SymPy failed on the import and is not counted) |
| push-gate fixture | PASS: rename Lean → docs yields only the docs path under the current diff command |
| HOP producer against both receipts | byte-identical (8 models) |
| HOP checker, normal and `-O` | PASS 8 certificates |
| signed encoding test | PASS 160 models, 793 coefficients |
| HOP negative controls, normal and `-O` | 14 of 14 and 5 of 5 rejected |
| priority tables | byte-identical |

These are reproductions of the packet's own tests, not tests registered by this repository. An exact rational check
of a finite certificate proves a finite list of inequalities between rationals; the analytic statements that make
those inequalities imply a bound on κ are a separate matter (section 3).

## 3. The lead's own check of the SPL-N route (on paper)

Re-derived from the frozen definitions in `OscInt/Statements/StationaryLeading.lean`, before writing any statement:
- From `κ₊ = F/2 + τE/2 + (iτ²/2)(L − F)` with `E(v) = e^{iv²/2}`: `κ′ = E + iτ(L − F)` and `κ″ = i(L − F)`, with
  `κ(0) = 0`, `κ′(0) = 1`. Two integrations give `κ(x) = x + iLx²/2 − i∫₀ˣ (x − v)² E(v)/2 dv` for `x ≥ 0`.
- With the Taylor bound `|e^{ia} − Σ_{j<N} (ia)^j/j!| ≤ a^N/N!` (a ≥ 0) and `∫₀ˣ (x − v)² v^{2j} dv =
  2x^{2j+3}/((2j+1)(2j+2)(2j+3))`, the polynomial coefficients `I_j(x) = x^{2j+3}/(2^j j! (2j+1)(2j+2)(2j+3))` of the
  packet are right, and so is the remainder `I_32(x)`.
- `|L − F(x)| ≤ 2/x` (one integration by parts and `∫ₓ^∞ v^{−2} = 1/x`), so `|κ″| ≤ 2/a` on `[a, b]`, and the
  interpolation pad `(2/a)(b − a)²/8 = (b − a)²/(4a)` is right (the vector form of the interpolation bound needs no
  factor √2).
- The tail identity `κ − L/2 = −E/(2x³) − (3i/2)(x² + i)J₄` and `|J₄| ≤ 2/x⁵` give `|κ − L/2| ≤ 4/x³` for `x ≥ 2`; with
  `π < 22/7`, `|κ| ≤ 63/100 + 1/16 = 277/400` for `x ≥ 4`. For `x ≤ 1/2`, `|κ| ≤ x + (4/3)x²/2 + x³/6 ≤ 11/16`.
  Both are below 0.7219.

No error was found. This is the lead's check, of the lead's model family; it is not an independent review.

## 4. How the batches of session 17 relate to the packet

- **SPL-N** (four statements): the rationals 360987/500000 and 72197399/10⁸ and the point 8123/5000 are the packet's.
  The statements were written by the lead after the check of section 3. The remainder corollary and the "no smaller
  constant" statement are the lead's formulation of the packet's proposal.
- **A5U** (one statement): the envelope, its normalisation `E(0) = 1` and the two-sided window are the packet's
  proposal. The paper route (sections X1–X5 of its crossover package) is unrefereed; it goes to a route referee after
  the freeze.
- **LOC2** (one statement): the constant `4((3/2)‖χ‖ + ‖∂₁χ‖ + ‖∂₂χ‖ + ‖Δχ‖)` is the packet's; the lead checked the
  shell count (`Σ (1 + |n|²)^{−2} ≤ 13 < 16`) and the identity for `(1 − Δ)(χ e^{iρ·k})`.
- **Report D** (the constant 38/5): not opened. The report itself is not in the repository (by the owner's privacy
  rule, external reports are never committed) and the packet does not contain it. The only repository record is the
  lead's summary of a checker's verdict (`review/2026-11-20-external-reports-answers.md`, section 1), which is not a
  proof. Without the original argument no statement is frozen and the frozen constant 18 of S1.3 stands. What would
  unblock it: the owner supplies the report, which then goes through intake, an independent re-derivation and a
  prior-art check before any statement.
- **F-a** (the planted K2-F without its support condition): a compiled witness is attempted in scratch; the stamped
  ledger is not edited; a follow-up record is appended only if the witness compiles with the three axioms.
- **Push gate**: implemented as a tools change, reviewed separately; no hook is installed.
- **HOP, PDE, operator and ANT material**: not opened in this record; scope decided later in the session.

## 5. Order claim

No Lean proof of any statement of SPL-N, A5U or LOC2 is in the repository before the reviews of those statements
are answered and stamped. Older proofs on paper exist (this packet), and for SPL-N a one-point Lean prototype of
session 15 in scratch, as `docs/statements.md` says for each batch.
