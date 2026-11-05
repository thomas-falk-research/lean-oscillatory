# Hand-off

For a reader who saw nothing. Read `docs/lessons.md` first.

## What exists (end of M0, 2026-11-05)
- A Lake project (`lakefile.toml`): library `OscInt` (one skeleton theorem, `OscInt.skeleton_two_mul`), empty
  `Blueprint` and `Challenge` libraries, and the executable `oscint-commit-env` (`tools/lean/CommitEnv.lean`).
- Checks: `Axioms.lean` (enumerates every theorem of the `OscInt` modules from the environment and prints its
  axioms), `StatementTypes.lean` (the `#assert_type_is` checker; no final theorems yet), `MathlibNames.lean`.
- Rust tools in `tools/` (std only, `cargo test` covers each): `guard`, `audit`, `replay`, `commit`, `challenge`,
  `stamp`, `toolchain`, `verify_all`. Formats: `docs/commitment-format.md`.
- CI (`.github/workflows/ci.yml`): `verify-all` on every push; manual job `mathlib-from-source`.
- Docs: toolchain and Mathlib-gap tables (`docs/toolchain.md`), prior-art gate (`docs/prior_art.md`).

## What is verified, by what
- Toolchain: `make verify-toolchain` (archive and installer hashes; archive ↔ installed toolchain `diff -r`).
- Skeleton theorem: axiom audit 1 of 1; replay by seven checker runs (`build/replay/summary.txt`; CI log).
- Gate self-tests, run by hand on 2026-11-05 (`docs/lessons.md` 3, 5, 6): each rejected by the step named there.
- Not yet exercised on a real statement: `commit` (validated on a probe statement only), `challenge` (never run;
  its list of constants required by `lake comparator` must be checked against comparator's `Exporting #[…]` line on
  first use), `stamp` (authorities and roots validated with a test digest; no manifest stamped yet).

## Decision pending (owner)
The prior-art gate found S1 anticipated: roos-j/lean-oscillatory proves the 1D van der Corput lemma with the
brief's constants and amplitude form (Lean v4.32.0-rc1, Apache-2.0 header), submitted as Mathlib PR #39406 (open).
Options for M1: (a) port that proof to v4.35.0 under our statement encoding, crediting it; (b) state S1 here and
depend on the PR once merged; (c) skip S1's proof and treat it as a named, cited hypothesis for S3/S4. Also: the
repository is named `lean-oscillatory` (the brief says `oscint-lean`), which collides with roos-j's repository name.

## Next (after the decision)
M1 per the brief's process: `docs/statements.md` entry, `OscInt/Statements/S1.lean` with sanity theorem, numerics
binary in `numerics/`, `make commit`, commit, `make stamp`, blind statement review into `review/`, then proofs.

## Commands
```bash
lake exe cache get
make verify-all
make stamp
```
`make verify-all` exits 0 on PASS, non-zero otherwise; CI accepts INCOMPLETE (steps with nothing to check) with a
warning.
