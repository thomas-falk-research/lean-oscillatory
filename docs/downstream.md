# Depending on OscInt: an integration guide

For a project that uses OscInt's theorems and wants to know, in CI, that it depends on exactly the reviewed
statements. Policy background: `docs/policy.md`. What the checker does not cover: README, "Depending on OscInt".

## 1. Pin a release
```toml
# lakefile.toml
[[require]]
name = "oscint"
git = "https://github.com/thomas-falk-research/lean-oscillatory"
rev = "v0.5.0"   # or the full commit hash from docs/release-notes/v0.5.0.commit (against a moved tag)
```
Use OscInt's `lean-toolchain` (`leanprover/lean4:v4.35.0`); Mathlib comes with OscInt at the revision it was checked
with. Then `lake update oscint && lake exe cache get && lake build`.

## 2. Use only the stable surface
`import OscInt.API`. Use the theorems listed as `proved_by` in `stamps/statements.json` (and their statement constants
`OscInt.Statements.*Statement`); everything else (`OscInt.D4.*`, `OscInt.StationaryPhase.*`, `…Aux`, `Blueprint`) may be
renamed in a patch release. `docs/which-theorem.md` says which theorem fits which phase.

## 3. Check in CI that you got the reviewed statements
```bash
lake build OscInt Blueprint     # the checker replays every OscInt and Blueprint module
python3 .lake/packages/oscint/tools/oscint_check.py \
  --statement OscInt.Statements.FoldOnStatement \
  --expect-sha256 <SHA-256 of stamps/statements.json from docs/release-notes/<tag>.md>
# add --commitments to recompute the statement commitments (minutes)
```
It fails if the statement list changed (drift), if a statement's commitment differs from the stamped one, or if the
kernel rejects a module. Against tampering keep your own copy of `oscint_check.py` whose SHA-256 is the one in the
release notes, and pin the commit hash, not the tag.

## 4. Upgrading
1. Read the target release's CHANGELOG section "Statement changes" (every release has one, possibly "none").
2. A patch release (0.y.Z): no statement, commitment or `proved_by` name changes; `stamps/statements.json` is byte-identical,
   so your `--expect-sha256` pin survives. Update `rev` only.
3. A minor release (0.Y.0 before 1.0.0): new statements, possibly changed ones (listed). Update `rev` and the
   `--expect-sha256` value from the new release notes after reading the list.
4. A Mathlib upgrade changes commitments of statements whose definitional closure changed; those statements are
   re-frozen under new names (`docs/policy.md`, "the re-freeze rule"). Your code keeps compiling against the old names
   until they are removed after one deprecation release.

## 5. When your phase does not fit
Open an issue with the template "My phase doesn't fit a statement" (`.github/ISSUE_TEMPLATE/`): the phase, the set,
what the classifier or your own analysis says about its critical points, and the bound you need.
