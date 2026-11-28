<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch A5U: answers to the route referee, and the proof (2026-11-28, session 17)

Written by the lead. The blueprint `Blueprint/TriangularCrossover.lean` and the lead's assembly
`OscInt/Front/TriangularCrossoverAssembly.lean` were drafted by an architect agent of the lead's model family
(launched 16:00:11Z, brief SHA-256 25cad8cc518f7be4e61583d3ef0c5ebcfaedfb277ca40389a2bfd2724989d9dc) after the review
answers were stamped, and reviewed by the lead before any part was briefed. One fresh-context route referee read the
route, the blueprint, the assembly and the frozen statements on a snapshot packet (launched 16:18:50Z, brief SHA-256
ebc913541eea09e43ee7712d130a6c5169acde53e3ee2b4b5cf32ce72b7777f9, task record 833 s; Python 3.13.18, mpmath 1.3.0,
numpy 2.5.3, scipy 1.18.1; no Lean). The six proof agents were launched at the same time and worked in scratch while
it read (lessons 42); no part was in the repository before this commit, and none changed after the review.

**Verdict: all 18 interfaces TRUE; the assembly with the parts implies the frozen statement; no FATAL, no MAJOR.**
Its checks: the 18 cuts of A3 attained on random polynomials (so 19 pieces cannot be lowered); A6 attacked with
400 000 adversarial inputs per case for five `(d_min, d_max)`, 0 violations, smallest margin 8.1 times η (a first
attack script of its own had a feasibility bug and produced spurious violations; fixed by checking every hypothesis
before counting); A7 on 12 000 high-precision cases, sharp at `t ε³ = 1`; A8 to 10⁻⁶⁰; A11's jet identities to 10⁻⁴⁹
at 50 digits, both signs of `a₀`; TRI-W's `−60√2 sign a₀` recovered; A9's bounds and the evenness of the curve
numerically.

| ID | Severity | Finding | Lead's answer |
|---|---|---|---|
| R-1 | MINOR | The route says "window α a₀ > 0"; the needed condition is `α* a₀ > 0`, automatic from `\|ys 0\| < π/4`; the blueprint is right. | Accepted; revision section of `docs/proof-A5U.md`. |
| R-2 | MINOR | The constants are tiny (δ about 10⁻³ because `\|g⁽⁸⁾\|` reaches 6·10⁴). | Noted; every constant is existential in A5U. |
| R-3 | NIT | The blueprint header names scratch files. | Accepted; the committed route is `docs/proof-A5U.md`. |
| R-4 | NIT | 19 pieces cannot be lowered in general. | Noted. |

## The proof

18 parts in 19 modules (B1 in two), the assembly and the final file `OscInt/Front/TriangularCrossoverFinal.lean`
(`OscInt.API.triCrossoverUpper`). Integrated by the lead in a scratch mirror of the build before entering the tree:
all 21 modules compile with empty output; `#print axioms OscInt.API.triCrossoverUpper`: propext, Classical.choice,
Quot.sound; `leanchecker` on each of the 20 new modules: exit 0, empty output.
