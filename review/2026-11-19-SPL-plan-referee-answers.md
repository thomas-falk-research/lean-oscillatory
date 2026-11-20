<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch SPL: answers to the plan referee and to the literature reader (2026-11-19)

Written by the lead. Two agents with fresh contexts, both of the lead's model family, were launched on 2026-11-19
after commit 567bfb8 and after their briefs' SHA-256 values had been logged (session log; the briefs are not
committed, and the reports are not reproduced here: every finding is in the lead's words). Neither edited the
repository. No statement of the batch was frozen and no Lean text of the batch existed when they ran.

## 1. Plan referee of `docs/proof-SPL.md` (first version, commit 567bfb8)

Method reported: its own derivation first (the quotient route with an exchange of integrals), then a re-derivation
of each step of the page, then numeric checks of its own design in double precision (four families of amplitudes
different from the registered ones, among them one with algebraic decay, one complex and not even, one with an
atomic third derivative, and the attainment construction with another mollifier). It did not read the session log
or the hand-off. Verdicts: SPL-S true as proved; SPL-K with 7/8 true as proved, given VC2-S and VC2-N, whose Lean
proofs it did not audit; SPL-A true as proved; SPL-N with 73/100 true by its numerics, with a gap in the proof.
No FATAL finding. Weakest step named: the certified enclosure for SPL-N.

| # | Severity | Finding (lead's words) | Answer |
|---|---|---|---|
| 1 | MINOR | Lemma 2 claimed the bound 3/2 for the kernel; the argument given proves 4. The value 3/2 was then used in Lemma 4 and in SPL-A. Nothing downstream needs more than some finite bound. | Accepted. Second version: the bound is 2, with a proof (Lemma 2), and 2 is what Lemma 4 and SPL-A use. |
| 2 | MINOR | The tail bound of section 5, 3/(2τ) + 1/τ³, is correct and wasteful: two terms cancel, and the kernel differs from its limit by at most 4/τ³. | Accepted, after the lead re-derived it (Lemma 1′ and Lemma 2 of the second version) and checked it on a grid (largest value of the ratio to 4/τ³: 0.25). The lead's check moved the threshold for 73/100 from the referee's 3.38 to 3.39. |
| 3 | MINOR | The derivative bound of section 5 was too large: the derivative of the kernel is τ times a tail integral, of modulus at most 1 and at most 2/τ². So the kernel is 1-Lipschitz and bounded by τ. | Accepted, re-derived and checked on a grid (largest modulus of the derivative found: 0.9991). Used in Lemma 2 and in SPL-A, where it makes the mollification error explicit. |
| 4 | NIT | In the proof of SPL-S the strict inequality was attributed to the wrong step; the supremum can be avoided by a first-moment argument. | Accepted. The second version uses the first-moment argument; no supremum appears. |
| 5 | NIT | The average form of the kernel over (0, 1) is right but not needed; the form with one integral to infinity gives the same bound without a change of variables. | Accepted (Lemma 2′). |
| 6 | NIT | The three primitives are differentiable on the whole line, so no one-sided derivative is needed; the left half-line can be obtained by reflection. | Accepted (Lemma 2, Proposition 3′). |
| 7 | NIT | Signs of the boundary terms, the scaling and Lemma 4 were re-derived and found right; Lemma 4 is not circular. | No change. |
| 8 | MAJOR (against the plan) | SPL-N has a plan and no proof, and the VC2 development has no enclosure of a Fresnel integral: it bounds a real profile with one-sided polynomial inequalities for the sine to degree 9. With findings 2 and 3 the range is [0.73, 3.39] and about 40 enclosures are needed for 73/100, about 19 for 3/4 (the referee's floating-point estimate, not a tested cost). It should not be frozen before a prototype compiles. | Accepted. SPL-N is taken out of the first freeze. It will be its own statement, with the rational chosen after a prototype of one certified enclosure exists. Section 5 of the second version says so, and so does the opening note. |
| 9 | MINOR | The attainment construction by convolution with a piecewise quadratic function is correct but costly to formalise; defining the third derivative as an explicit sum of four bumps and the amplitude as its triple primitive avoids convolutions, and the parameters can be given explicitly. | Accepted. Section 6 of the second version is that construction with `T = max(8τ/ε, 2τ)` and `w = min(τ/2, ε/2)`. |
| 10 | MINOR | The class with four integrability hypotheses is enough for every limit taken and should be the frozen hypothesis, not compact support; two of the four hypotheses are probably redundant (an inequality the referee cited from memory). | Accepted as a modelling note (section 7); the redundancy is not claimed. |
| 11–13 | NIT | No amplitude of the class has a third derivative of one sign; the behaviour as λ → 0 is consistent; the opening note and the proof page differ in an immaterial sign. | Section 7 records the first two. The sign is as in the proof page. |

Verification of the reduction to VC2 (the referee's second task): it read the frozen statement file and
`docs/statements.md` and lists the hypotheses to discharge for the phase `x²/2` on `[−c, c]` with rate 1; they are
copied into section 5 of the second version. It did not build anything.

What the referee did not check, by its own account: the Lean proofs of batch VC2; Mathlib signatures beyond the
existence of the names; the registered program; prior art; any rigorous enclosure (all its numbers are floating
point). Two of its own check runs were stopped (run time, memory) and redone in another form; it says no result
was discarded for its value.

What this review is not: it is one referee, of the lead's model family, on a proof on paper; the second version
has not been refereed. The blind review of the statements (step 5 of `CONTRIBUTING.md`) is still to come.

## 2. Literature reader

Asked to read, not only cite, the nearest sources and to report Mathlib names. Its report marks each item as read
or second-hand.

- **The identity is classical in substance.** Erdélyi's remainder representation (1956, section 2.8), read by the
  reader in the reproduction of Ali Mehmeti and Dewez (arXiv:1412.5789, Theorem 1.3), gives for a stationary point
  of order two, a regular amplitude and three integrations by parts a kernel `φ₃`; the reader derived
  `κ = i φ₃ + L/2` (not in any source it saw). The lead checked this relation in mpmath at five points (differences
  below 2 · 10⁻²⁵) on 2026-11-19. So (T2) is the two-sided form of that representation with the term in `g″(0)`
  folded into the kernel. Erdélyi's own bound of `φ₃` (0.6267, attained at 0) plus the separate term gives the
  constant 1.2533; the value 0.72197 and the two-sided bound in `‖g‴‖₁` were not found.
- **Olver (1974): still not read.** No open copy. Read instead: a later paper's account of its theorem (Ammari and
  Sabri, arXiv:2009.03153, Appendix A): one-sided integral, stationary point at an end point, error bounded by
  total variations divided by the large parameter. DLMF 2.3(iv), read, gives no error bound and points to Olver.
- **Other texts.** A Fourier-side bound (lecture notes after Zworski, read) with the norm `‖ξ² ĝ‖₁` and the constant
  `1/(2√(2π))`; neither that bound nor SPL-S implies the other. Hörmander's Lemma 7.7.3, read only as restated
  elsewhere: three derivatives in L², constant not explicit. Not read: Erdélyi's originals, Olver's and Wong's
  books, Zworski's book, Dimassi–Sjöstrand.
- **Formalisations.** Mathlib at the pin has neither a Fresnel integral nor stationary phase; the complex Gaussian
  integral needs a non-zero real part. The names and signatures the route needs exist (listed in section 8 of the
  proof page; to be re-checked by `#check`). The upstream repository was seen only through a summary of its
  README (van der Corput only; stationary phase a future goal); the reader's request to attach it was denied and
  the lead did not retry.

Consequence for wording (stop gate of the opening note): no sentence of this batch says "new". The supported
sentence is: the identity is the two-sided `N = 3` case of Erdélyi's representation; the bound with
`sup |κ| = 0.72197` was not found in the literature searched on 2026-11-19, with Olver (1974), Erdélyi's originals
and three books unread.
