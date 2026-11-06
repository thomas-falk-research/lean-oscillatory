# Versioning, stability and upgrade policy

Adopted 2026-11-06 (session 3). Applies from v0.3.0. Changing this policy is a CHANGELOG entry.

## What is stable
The **stable surface** of OscInt is:
1. the statement constants `OscInt.Statements.*Statement` listed in `stamps/statements.json`, with the commitment
   recorded there (the SHA-256 of the statement's definitional closure, `docs/commitment-format.md`);
2. the theorems proving them (`proved_by` in `stamps/statements.json`), whose types are syntactically the statement
   constants (`StatementTypes.lean`);
3. the front-end theorems in `OscInt/API.lean` once that file exists (ROADMAP §2), each with a frozen statement of
   its own.
Everything else (`OscInt.D4.*`, `OscInt.StationaryPhase.*`, `OscInt.Blueprint.*`, auxiliary namespaces) is internal:
it may be renamed or removed in any release. Depend on it only if you accept that.

## Versions (semantic versioning, from v0.3.0)
- **Patch** (0.3.x): no change to any statement constant, commitment or `proved_by` name. Proof refactors, tools,
  docs, CI. `stamps/statements.json` may change only in `version`.
- **Minor** (0.x.0): adds statements or theorems; existing entries of `stamps/statements.json` unchanged except
  `version`, and except `proved_by` going from `null` to a theorem (a statement newly proved).
- **Major** (x.0.0, and every 0.x.0 while the major version is 0): may change commitments, e.g. a Mathlib upgrade
  (below). Before 1.0.0 a minor version may therefore change commitments; it says so in the CHANGELOG under
  "Statement changes" and lists every changed commitment.
A downstream project pins a release tag and the SHA-256 of `stamps/statements.json`
(`tools/oscint_check.py --expect-sha256`), so any change to the statement list fails its CI until someone reads it.

## Never in place
A stamped statement file is never edited (lessons 10; `make commit`, `statements check`). A statement that has to
change becomes a new constant with a new name (for example `D4LimitStatement₂` or `D4LimitLocalStatement`),
written, stamped, pinned and blind-reviewed like any other (`CONTRIBUTING.md`). The old constant, its proof and its
pin stay until removed under the deprecation rule.

## Deprecation
A stable name is removed only after one minor release in which it is marked `@[deprecated NewName (since :=
"YYYY-MM-DD")]` and listed under "Deprecated" in the CHANGELOG. Statement constants are never deprecated while a
pinned stamp refers to them; they are superseded (the new constant's entry names the old one in its docstring).

## Mathlib and toolchain upgrades (the re-freeze rule)
A commitment is a hash of the statement's definitional closure, which includes Mathlib's definitions (ℝ, the
integral, `fderiv`, `Real.rpow`, …). A Mathlib upgrade can therefore change commitments without anyone touching
OscInt's statement files. Procedure:
1. On a branch, bump `lean-toolchain`, the Mathlib `rev` in `lakefile.toml` and `lake-manifest.json`; record the
   versions and the `#check` probes of `MathlibNames.lean` (lesson 1). Fix proofs; statement files stay byte for
   byte (the guard and `make commit` check this).
2. `make commit`. For each statement whose commitment is **unchanged**: nothing more to do; the old stamp still
   pins it (the commitment says the closure is identical up to binder names, `docs/commitment-format.md`).
3. For each statement whose commitment **changed**: Mathlib changed a definition it depends on. The statement keeps
   its text, but the old review and stamp no longer certify the new closure. Re-freeze:
   a. record the closure diff: `make commit` writes the new closure text `build/commit/<name>.env.txt`; the old one
      is reproduced by `make commit` at the old pin. Commit the `diff` of the two under `review/` and have **one**
      blind referee read it and answer one question: does any change alter the meaning of the statement? (verdict
      SAME-MEANING or CHANGED, naming the constants);
   b. on SAME-MEANING: a new stamp (`make stamp`), a new pin line for the statement (the old line stays in history),
      CHANGELOG "Statement changes: commitment of X changed from … to … by the Mathlib upgrade …; referee
      SAME-MEANING, review/…"; the release is a minor version (before 1.0) or a major one (after);
   c. on CHANGED: the statement is treated as a new statement (full review, two referees).
   A machine-checked equivalence `OldStatement ↔ NewStatement` is not available across a Mathlib version (the two
   closures live in different environments); the closure diff plus a referee is the evidence instead, and the
   rule says so rather than claiming more.
4. The full replay (`make verify-all`) on the upgraded tree, recorded in `docs/replay/`; then the release.
5. A scheduled CI job (ROADMAP §3) builds against the newest Mathlib weekly and only warns; it never changes pins.

## What a downstream project should do
- Pin a release tag (`require oscint from git "…" @ "v0.3.0"`) and the SHA-256 of `stamps/statements.json`.
- Run `python3 .lake/packages/oscint/tools/oscint_check.py --statement <each statement you use> --expect-sha256 <pin>`
  in CI (add `--commitments` to recompute the commitments; it takes a few minutes).
- Use the theorems listed as `proved_by`, not internal lemmas; or accept that internal names can change in a patch.
- On an OscInt upgrade, read the CHANGELOG's "Statement changes" section before updating the pin.
