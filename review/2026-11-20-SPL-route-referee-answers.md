<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch SPL: answers to the route referee (2026-11-20)

Written by the lead. One agent with a fresh context, of the lead's model family, was launched on 2026-11-20 at
01:44:13Z on a read-only copy of commit be3c000, after its brief's SHA-256 had been logged and pushed (session
log; the brief is not committed, and the report is not reproduced here: every finding is in the lead's words). It
finished at about 02:17Z. It read the route (`docs/proof-SPL.md`, with section 10) and the blueprint
(`Blueprint/StationaryLeading.lean`, then five propositions). The assembly did not exist at that commit; the
referee says it did not read the one that appeared in the repository while it worked.

Verdict: launch provers after changes to section 10 and to the briefs; no change to the Lean text of the
blueprint is needed. No FATAL and no MAJOR finding. Weakest step named: the third clause of P-fresnel (the value
of the Fresnel integral tied to the frozen closed form), for the Lean effort, not for a gap; second, the
bookkeeping of P-bump.

## What the referee did beyond reading

It went further than its brief asked, and this changes the plan, so it is said plainly.

- In its scratch directory it wrote Lean proofs, with the standard axioms only, of: P-bound from P-fresnel and the
  two VC2 theorems; all eight clauses of P-kernel from P-fresnel and P-bound; the half-line identity and P-line
  from P-kernel; an assembly of its own of the four statements from the propositions; the first two clauses of
  P-fresnel; and two lemmas for the Abel route (the shape of Mathlib's half-line Gaussian integral at
  `b = (ε − i)/2`, and that its value at `ε = 0` on the principal branch is the frozen closed form). The lead
  elaborated its three files (SHA-256 c336b4df…25cadb9e, 8668e5b0…bafd447e, 23ca1e98…27006770): each ends with exit
  code 0. They import all of Mathlib, are not in the repository, and prove neither the third clause of P-fresnel
  nor P-bump.
- It ran Lean directly while two provers were working, outside the session's lock (the brief gave it no rule for
  Lean; the lead's omission). No restart occurred.
- Numerics of its own (floating point): grids to `x = 330` for every constant of the blueprint; P-line and the
  scaling on amplitudes the lead's check lacks (class C³ and not C⁴, `g(0) = 0`, odd, centred away from 0,
  algebraic decay); the Abel identities at three values of ε; the bump construction with the amplitude built as a
  triple primitive, for the kernel of the batch and for kernels with a corner, with `|k(τ)| = M`, with `M = 0`, at
  `τ = 10⁻⁶` and at `T = 2τ`. No violation. One failing case came from a test kernel of its own that was not odd; it
  disclosed and corrected it, and it shows that oddness is used.

## Findings and answers

| # | Severity | Finding (lead's words) | Answer |
|---|---|---|---|
| 1 | MINOR | Section 10 does not say which proposition a part may assume. Two traps: P-bound needs the oddness of `F` (in P-fresnel) while the Abel route needs `F` bounded, so a careless pair of briefs is circular; and route (a) to the value of the limit needs Propositions 3 and 3′ for a kernel that is not the frozen one. | Accepted. The order is fixed in the revision of section 10: P-tail and P-value (no hypothesis), P-fresnel from them, P-bound from P-fresnel, P-kernel from P-fresnel and P-bound, P-line from P-kernel, P-bump (no hypothesis). Route (a) is withdrawn. |
| 2 | MINOR | "The lead's assembly, compiled before any part is proved": no assembly was in the copy it read. | The assembly was written while the referee ran and is in the tree since commit b3d589e, compiled and through `make quick`, before any part was assigned. The referee's own assembly, written without sight of it, needed nothing beyond the propositions; that is independent evidence that the interfaces suffice. |
| 3 | MINOR (planning) | P-bound, P-kernel, P-line and the assembly are short consequences of P-fresnel; the critical path is the third clause of P-fresnel and P-bump. It proposes to split that clause into two true propositions so that the existence of the limit and its value can be proved in parallel. | Accepted. The blueprint gains P-tail (`∃ L′, ∀ x > 0, \|F(x) − L′\| ≤ 2/x`) and P-value (every such `L′` is the closed form). The referee's scratch proofs of P-bound, P-kernel and P-line are taken as the starting point of those three parts: a fresh agent rewrites them into part files under the repository's rules (specific imports, declarations of at most about 60 lines, docstrings, no forbidden construct). The records will say that these three parts descend from proofs written by the route referee; the Lean kernel, the gate and the post-proof reviews check them as any other part. |
| 4 | MINOR | Existence of the limit through Cauchy's criterion is avoidable friction: for `x > 0` the function `e(v)/(iv²)` is integrable beyond `x`, which gives the limit and `L′ − F(x) = −e(x)/(ix) + ∫_x^∞ e/(iv²)` in one step. The rest of the Abel route is right as written; Mathlib has an integration by parts on a half-line that section 10 did not list. | Accepted; both go into the briefs of P-tail and P-value. |
| 5 | MINOR | On the negative half-line the primitives `E₂` and `κ₊` are unbounded (for instance `\|κ₊(−100)\| ≈ 12533`); a prover who integrates by parts on `[−T, 0]` with them will fail. The left half must come from the reflection. | The lead's brief for P-line already used the reflection; the part now starts from the referee's proof, which does the same. |
| 6 | MINOR | The lead's interface check does not exercise: the norm of `g‴` in P-bump (it is set, not computed), compact support and `g ≠ 0`, the choice of `w` from continuity, corner cases of P-bump, amplitudes with `g(0) = 0`, the statements SPL-S, SPL-K, SPL-A, the routes to P-bound and to the value of the limit. | Accepted as a description of that script, which stays what its record says: a plausibility check of interfaces. The referee's scripts cover the gaps; they are in scratch and are not evidence in this repository. |
| 7 | NIT | P-bump: define the amplitude by iterated primitives, not by the kernel formula; parity alone does not give compact support, the first moment must be computed once; Mathlib has a lemma for the mollifier step; `τ = 0` needs its own amplitude. | Agrees with section 10 and the brief; the lemma's name goes into the brief. |
| 8 | NIT | The referee's own error in one test kernel (see above). | Noted. |

## What is not established by this review

The third clause of P-fresnel (now P-tail and P-value) and P-bump are not machine-checked by anyone. The referee
checked about half of the Mathlib names of section 10. No replay, no independent checker and no comparator were
run on its scratch files. The referee and the lead are of the same model family.
