<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Owner decision: the author's name and the licence inside every file that can carry them

Recorded 2026-11-19 (session 13) by the lead. The decision was taken by the owner in the session on 2026-11-19; the
owner's words are not reproduced.

## The facts

Until 2026-11-19, 2145 of the tracked files had no copyright line of their own; `REUSE.toml` assigned the owner's
copyright to them centrally. That satisfies the REUSE specification, and it does nothing for a file that is copied,
indexed or scraped on its own: a statement file taken out of the repository named no author. Among those files
were the 41 frozen Lean files (the statements and their challenges) and 223 text records.

Two rules stood in the way. A stamped statement file is never edited (its SHA-256 is pinned to a timestamped
stamp), and records are never edited (they are history).

## The decision

1. Living documents and sources get an ordinary SPDX header at the top.
2. The frozen statement and challenge files get one fixed attribution block appended at their end, and the pin
   check becomes "the bytes before the block equal the stamped file". Both rules above are amended by exactly this
   exception and by nothing else.
3. Text records get one fixed attribution block appended at their end, with a mechanical check that nothing else
   changed.
4. Machine output and cryptographic material are left byte for byte: compiler outputs of plant runs, timestamp
   tokens, manifests, OpenTimestamps proofs, JSON, lock files and toolchain pins. Each plant-run directory gets a
   `COPYRIGHT` file; `REUSE.toml` and `NOTICE` cover the rest.

## How it is done, and how it is checked

Statement files (`OscInt/Statements/*.lean`, 20 files). The block is a closed Lean comment after the last line of
the frozen text. There are two constants: one with the owner's copyright, one for
`OscInt/Statements/VanDerCorput.lean` with Joris Roos's copyright line as well (its statement forms follow
`roos-j/lean-oscillatory`). They are defined in `tools/src/sys.rs` (`ATTRIBUTION_BLOCKS`) and repeated in
`tools/oscint_check.py`; a unit test keeps the two copies identical. A statement file is now its frozen bytes, or
its frozen bytes followed by exactly one block and nothing after it. `make commit`, `make statements-check` and
the downstream checker hash the bytes before the block; a byte changed before the block, inside it or after it
makes the file match no stamp. `stamps/statements.json` keeps the SHA-256 values it had: they are the hashes of the
frozen bytes. To check one pin by hand: `head -c -211 OscInt/Statements/<File>.lean | sha256sum` (347 for
`VanDerCorput.lean`) gives the hash in the pinned stamp's manifest.

Challenge files (`Challenge.lean`, `Challenge/*.lean`, 21 files). Their bytes are not pinned; the export of their
theorems is, by its SHA-256 in the stamp. A comment at the top would shift the source positions that Lean stores
in each `sorry` and change the export; a comment at the end shifts nothing. The check is the comparator itself: it
refuses a challenge whose export is not the stamped one.

The inertness of the block for the mathematics is checked by the tools, not argued: every statement commitment
(the SHA-256 of the definitional closure of the statement constant) is recomputed after the change and must equal
the stamped one, and every challenge export must have the stamped SHA-256. The session log records the run.

Records (196 files with the block alone, and three answer files of the same day that also received a dated note):
`tools/attribution_blocks.py` appended the block and verified, against commit 580e34d, that each file is its
earlier text followed by the block; the list with the hashes before and after is
`docs/replay/2026-11-19-attribution-blocks.txt`. Sixteen files of `review/calibration/` are cited by their SHA-256
in other documents (sealed keys and planted copies); the whole directory was left untouched.

## What remains without a line of its own, and why

After the change 1829 files: 1488 outputs of plant runs (446 of them empty; a compiler log with a header is no
longer the compiler's output), 260 files under `stamps/` and `anchors/` (tokens, manifests, proofs; the stamp
verifier also rejects any file it does not expect there), 42 JSON files, 20 calibration files sealed by hashes, and
about twenty lock files, toolchain pins, licence texts and similar. For all of them `REUSE.toml` states the
copyright, and `make sbom` writes an SPDX document that lists every file with its copyright text and checksum.

## Consequences

- A compatibility break for downstream users, to be stated in the release notes: a copy of
  `tools/oscint_check.py` from v0.6.0 or earlier reports "the frozen statement file was edited" for every statement
  file of a later release, because it hashes the whole file. The checker shipped with the release must be used.
- `docs/policy.md` and `CONTRIBUTING.md` state the exception. A new statement file carries an ordinary header
  inside its frozen bytes from the start; a new record is written with its attribution.
- What a copyright line does: it states the claim and the licence in the file. It does not prevent copying. The
  obligation to keep it comes from the licences: section 4 of the Apache License 2.0 (notices of the source files
  and the contents of `NOTICE` must be kept in redistributions) and section 3(a) of CC BY 4.0. Much of the proof
  text and of the reviews was drafted by AI agents under the owner's direction, as the README discloses; how far
  copyright extends to such text differs between jurisdictions, and nothing here decides that.
