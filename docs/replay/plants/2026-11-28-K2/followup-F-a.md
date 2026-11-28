<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Follow-up 2026-11-28: plant F-a refuted on paper

Kept in its own file: `README.md` of this directory is listed in the K2 stamps and is not changed further.

After the replay, an external follow-up delivered by the owner derived a family of continuous biperiodic phases that
refutes F-a (K2-F with `tsupport χ ⊆ (−π, π)²` dropped) at `χ = 1`, `t = 1`, `p = (1/2, 0)`: Rudin–Shapiro step signs
in one variable and a sine polynomial in the other make every lattice coefficient at most `4π²/(2N)` while the box
integral at the half-integer velocity is at least `4π²(H_N/(2πN) − 1/(4N))`, so the planted constant would satisfy
`D ≥ H_N/π − 1/2` for every `N`. The lead checked the derivation step by step and checked finite instances
numerically (`review/2026-11-28-K2-pr26-external-review-answers.md`, section "Plant F-a";
`numerics/results-k2-fa-check-2026-11-28.txt`).

Outcome: FALSE on paper, not machine-checked. The compiled outcome in `README.md` stays NOT DETECTED until a witness
compiles; none is written.
