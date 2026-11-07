# Hand-off

For a reader who saw nothing. Read `docs/lessons.md` first (23 entries); every rule in it is binding.

## What exists (end of session 3, 2026-11-07)
- Lean v4.35.0, Mathlib `56a0058` (tag v4.35.0). **Every pinned statement is machine-checked as stated**
  (`docs/STATUS.md`): S1 (three van der Corput lemmas), S2.1, S2.2, S3, S4.1, S4.1′, S4.2, S4.3, S4.4 (new: closed
  forms of c_C, `OscInt.d4ConstantClosedForm`) and the front-end batch 1, F1 and F2 (new; bridges drafted before
  their review, disclosed).
- `make verify-all` reports PASS (records in `docs/replay/`, newest first). The brief's S4 limit with its closed-form
  constant is `OscInt.API.d4LimitClosedForm` (F2) as one theorem, or S4.2 ∧ S4.4.
- **Entry point for users:** `import OscInt.API` (a table of every theorem with the textbook statement it formalises,
  and the front-end theorems in Mathlib's idiom). Example consumer: `examples/consumer/`.
- **Depending on OscInt:** `stamps/statements.json` (generated, `make statements`; checked by verify-all),
  `tools/oscint_check.py` (toolchain and Mathlib match, statement files, the statement constant's module, syntactic
  types, axioms, kernel replay of each theorem's dependency closure, recomputed commitments; it detects drift, not
  tampering), its controls `tools/test_oscint_check.sh` (15/15, `docs/replay/2026-11-07-oscint-check-controls.txt`),
  README "Depending on OscInt", `docs/policy.md` (semver from v0.3.0, stable surface, deprecation, re-freeze rule).
- Developer experience: `make quick` (minutes), `make verify-all ONLY="…"`, verify-all preflight (`zstd`, `bwrap`,
  full clone), CI jobs `quick` (every push and PR), `verify` (every push, weekly), `consumer` (main, PRs, weekly),
  `CONTRIBUTING.md`, 0 build warnings.
- Released: v0.2.0 (DOI 10.5281/zenodo.24021329; all versions 10.5281/zenodo.24021328). v0.3.0 is prepared, not
  released: notes in `CHANGELOG.md` "Unreleased".

## Owner decisions (stop and ask)
- **Release v0.3.0.** Bump `lakefile.toml`, `CITATION.cff`, `.zenodo.json` to 0.3.0 together, publish the GitHub
  release with the CHANGELOG notes, and put in the notes the SHA-256 of `stamps/statements.json` and of
  `tools/oscint_check.py` at the tag (downstream projects pin them; README).
- Merge the session's pull request (CI: the `consumer` job runs there for the first time).
- Still the owner's: venue, outreach, money, publication, Mathlib PRs, branch protection, Reservoir listing, a human
  expert review of the statements, Mathlib built from source on a second machine.

## Next (ROADMAP order)
1. Closure-diff tool (ROADMAP §3, technical debt from `docs/policy.md`): per-constant canonical hashes with local
   numbering and a listing of changed constants; until it exists a Mathlib upgrade that changes a commitment means
   a new statement.
2. ROADMAP §2 front ends, next batches: conversions from `iteratedFDeriv`, `Matrix` Hessians and the classical
   discriminant to `dd`, `hessDet`, `cubicCoeffs`; front ends for S2.2, S3, S4.1′ with `ContDiff` amplitudes;
   `EuclideanSpace ℝ (Fin 2)` versions.
3. Explicit constants (downstream's first priority), local smoothness, parametric uniformity, hypothesis checkers,
   worked examples, sharpness lemma (ROADMAP §2).
4. Put `GammaFree.lean` into the next stamp.

## Process notes for the next lead
- Statement first; for a front end too. In session 3 the F1/F2 bridges were drafted in the scratch directory before
  the stamp and review; this is disclosed in `docs/statements.md` and no "fixed before the proof" claim is made for
  F1/F2. Do not repeat it.
- Agents were fast when the route named exact, `#check`ed lemmas with signatures (2.5–10 min per part).
- Elaborate a blueprint against `import OscInt` and `import Blueprint` (lessons 20).
- After an adversarial finding, re-run the referee's own reproduction against the fix (lessons 22).
- `verify-all` takes about an hour, `make commit` about 15 minutes, `test_oscint_check.sh` about 22 minutes.

## Commands
```bash
lake exe cache get
make quick
make verify-all            # about an hour; needs zstd, bubblewrap and a full clone (preflight checks)
make statements            # regenerate stamps/statements.json after a pin or StatementTypes change
cd examples/consumer && lake build && ../../tools/test_oscint_check.sh
make stamp
```
