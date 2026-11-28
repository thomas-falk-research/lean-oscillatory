<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch SPL-N: negative controls of the kernel-checked cell certificate (2026-11-28, session 17)

The 40-cell certificate of SPL-NU is checked by `decide +kernel` on a Boolean checker over ℚ
(`OscInt/Front/StationaryLeadingSharpCellsData.lean`, soundness in `…CellsCore.lean`). This record shows that the
checker can fail: four mutations, each a theorem that the checker returns `false`, proved by the kernel.

`controls.lean.txt` (written by proof agent C in scratch; SHA-256 a262217bf935b2fd23a52761f911c78d8baa9e8bb4419ea9c327469664a75b99,
with `#print axioms` lines appended by the lead):
- `n1`: every cell checked against the cap `360986/500000` (one millionth below the stated cap): `false`;
- `n2`: the cover of `[1/2, 5]` instead of `[1/2, 4]`: `false`;
- `n3`: the cover starting at `1/4`: `false`;
- `n4`: the lower-point test with target `0.72197400`: `false`;
- `n5`: the table has 40 cells.

Run by the lead at 16:53:10–16:53:13Z with
`lake env lean -DautoImplicit=false controls.lean` against the repository build of commit 0274fe9 (Lean 4.35.0,
Mathlib 56a005855ea1): exit 0; output `controls.out` (SHA-256 c8d46932301671cf778e758d282d01358ea0b6f7af40e0ace02511779c362ea8):
each of `n1`–`n4` depends only on propext, Classical.choice, Quot.sound. Post-proof referee C ran six further mutations
of its own (record: `review/2026-11-28-SPLN-LOC2-post-proof-answers.md`).
