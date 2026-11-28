<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch K2, plant F-a: a compiled witness (follow-up of 2026-11-28, session 17)

Appended evidence. The stamped plant ledger of batch K2 (`docs/replay/plants/2026-11-28-K2/`, `README.md` and
`SUMMARY.txt` there) recorded F-a as NOT DETECTED; it is a record and is not edited. The paper refutation is
`docs/replay/plants/2026-11-28-K2/followup-F-a.md`. This directory adds the compiled witness that the paper
refutation lacked.

**The plant.** F-a is K2-F with its support condition `tsupport χ ⊆ (−π, π)²` dropped:
`P_TorusLocalizationStatement`, defined in `docs/replay/plants/2026-11-28-K2/witness-F-a.lean.txt`.

**The witness.** `witness-F-a-compiled.lean.txt` (793 lines, SHA-256
`057c3a24e24dc0eb707f9c5606dce5ce2d2e1613a05fb8f9d1673c1f0cbe8124`) proves

    theorem OscInt.API.TriangularDecaySanity.not_F_a : ¬ P_TorusLocalizationStatement

It imports only `OscInt.Front.TriangularDecaySanity` (the K2 sanity layer, SHA-256
`88b888728d9559e25273096eb5b10ee213f551bf468785180a5af974304d8ede` at this commit) and restates the planted
definition; the lead checked by script that the restated definition is byte-identical to the one in the stamped
`witness-F-a.lean.txt` (SHA-256 of that file `b7d59d571ca41e6d7242af35fdf4bd0f2bc224fc04ca004b9464b31f19bb5eca`).
The file contains none of the guard's forbidden tokens (lead's scan) and no `set_option`.

**Who and when.** Written in scratch by a proof agent of the lead's model family (launched 12:15:40Z, brief SHA-256
d74740b6102667f352248afa2d4fa0ee714fbadbdf52a86260547559b713d919; Lean only through the session lock; no git), and
re-checked by the lead in a fresh scratch directory:
- 12:47:50Z: `lake env lean -DautoImplicit=false --root=<dir> -o <dir>/FaWitness.olean FaWitness.lean`
  (Lean 4.35.0, Mathlib 56a005855ea1, the repository build at 6cd5617): exit 0, 8 s; output
  `witness-F-a-compiled.out`: `'OscInt.API.TriangularDecaySanity.not_F_a' depends on axioms: [propext,
  Classical.choice, Quot.sound]`.
- then `leanchecker FaWitness` with that directory first on `LEAN_PATH`: exit 0, 4 s, empty output
  (`witness-F-a-compiled.leanchecker.out`, 0 bytes). This is the acceptance criterion the repository's replay uses
  for a per-module `leanchecker` step (`tools/src/bin/replay.rs`: exit 0 and no error output). A failed lookup of the
  module earlier in the same minute exited 1 with "uncaught exception", so this path can fail.

**The construction** (the agent's, checked against the paper route by the lead; constants cruder than the paper's,
the divergence argument the same). With `χ ≡ 1`, `t = 1`, `p = (1/2, 0)`, for each N ≥ 1 a continuous biperiodic phase
`Ψ_N(x, y) = G(arccos(cos y)) · arccos(f_N(x))`, `f_N(x) = (1/(2N)) Σ_{k<N} (−1)^k sin((k+1)x)` (so `|f_N| ≤ 1/2`), `G` a
sum over `2^j` cells of trapezoid bumps with Rudin–Shapiro signs (`j = 2N + 3`, cell width `π/2^j`, ramp width
`π/(16·2^j N)`). Every integer coefficient of `e^{iΨ_N}` over the box is at most `5π²/N`; the half-integer one is at
least `(2πH_N − 3π²)/N`. A uniform D would give `H_N ≤ (5πD + 3π)/2` for all N, against the divergence of the
harmonic series (`Real.tendsto_sum_range_one_div_nat_succ_atTop`; N chosen after D). Writing the profile as
`G(arccos(cos y))` makes it continuous and 2π-periodic without a wrap-around ramp.

**Outcome.** Plant F-a: DETECTED (kind `not`, compiled witness), as of this follow-up. The K2 ledger keeps its
historical line; the support condition of K2-F is shown necessary by a compiled theorem. The witness is a record, not
part of the library build; it is not rebuilt by `make quick`.
