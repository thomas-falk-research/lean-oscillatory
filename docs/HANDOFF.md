# Hand-off

For a reader who saw nothing. Read `docs/lessons.md` first (22 entries); every rule in it is binding.

## What exists (session 3, 2026-11-06)
- Lean v4.35.0, Mathlib `56a0058` (tag v4.35.0). All eleven pinned statements are proved: S1 (three van der Corput
  lemmas), S2.1, S2.2, S3, S4.1, S4.1′, S4.2, S4.3, and, new in session 3, **S4.4** (closed forms of c_C,
  `OscInt.d4ConstantClosedForm`). S1–S4.3 are machine-checked as stated (`docs/STATUS.md`); S4.4 is proved and replayed
  and its post-proof and adversarial reviews are the next step (status in `docs/STATUS.md`).
- `make verify-all` reports **PASS** (9 of 9 steps) on 1c7ebe3: `docs/replay/2026-11-06-S44-verify-all.txt`. The
  brief's S4 limit with its closed-form constant Γ(1/3)²/(√3|Disc|^{1/6}) is S4.2 ∧ S4.4.
- Released: v0.2.0 (DOI 10.5281/zenodo.24021329; all versions 10.5281/zenodo.24021328). `CHANGELOG.md` "Unreleased"
  holds the notes for v0.3.0; `lakefile.toml`, `CITATION.cff` and `.zenodo.json` say 0.2.0 and are bumped together
  when the owner cuts the release.
- Depending on OscInt (new): `stamps/statements.json` (generated, `make statements`; checked by `make
  statements-check` and verify-all), `tools/oscint_check.py` (downstream checker; negative controls in
  `tools/test_oscint_check.sh`), `examples/consumer/` (tested consumer project), README "Depending on OscInt",
  `docs/policy.md` (semver from v0.3.0, stable surface, deprecation, Mathlib re-freeze rule).
- Developer experience: `make quick`, `make verify-all ONLY="…"`, a preflight in verify-all (missing `zstd`, `bwrap`,
  shallow clone), CI jobs `quick`, `verify` (every push and weekly), `consumer` (main, PRs, weekly),
  `CONTRIBUTING.md`; build noise fixed (0 warnings).

## Owner decisions
Venue, outreach, money, publication, Mathlib PRs, release tags, and anything needing the owner's accounts (Zenodo,
ORCID, branch protection) are the owner's. Open: publish v0.3.0 once S4.4's reviews are in (notes in CHANGELOG).

## Next
The plan is `docs/ROADMAP.md`, in its order.
- S4.4 post-proof reviews (prompts `review/prompts/S44-post-proof.md`, `S44-adversarial.md`, committed before the
  final theorem existed), answers, STATUS row.
- Public API batch 1 (ROADMAP §2): front-end statements F1 (amplitude bounds from `ContDiff` and compact support) and
  F2 (the D4 limit with the closed-form constant, Mathlib-idiom amplitudes), then `OscInt/API.lean`.
- Put `GammaFree.lean` into the next stamp.
- Mathlib from source on a second machine (owner): `lake build Mathlib` in a fresh clone without `lake exe cache get`,
  then `make commit`; record in `docs/toolchain.md`.

## Commands
```bash
lake exe cache get
make quick
make verify-all            # about an hour; needs zstd, bubblewrap and a full clone (preflight checks)
make statements            # regenerate stamps/statements.json after a pin or StatementTypes change
make numerics
make stamp
```
