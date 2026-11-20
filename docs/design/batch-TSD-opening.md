<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Batch TSD (two-saddle steepest descent): opening note

Written by the lead on 2026-11-20, before any statement of the batch is drafted and before the published proof
has been checked by anyone in this project. A frame, not a claim. Owner decision:
`docs/decisions/2026-11-20-batch-two-saddle.md`.

## The source

Lemma E.1 of hexagon:2611.00174v1 (appendix "Two-saddle steepest descent with a uniform remainder"; in the TeX
source the label is `lem:D.1`). CC BY 4.0; cited, not copied. The notation below is the preprint's.

Setting: the strip `N = {b : |Im b − 1/2| ≤ δ₁}` around the line `E₊ = {Im b = 1/2}`; a large parameter `c′`; a
band point `x`. On `N` the integrand of an integral over `E₊` factors as a constant times `e^{c′φ(b)} A(b)` with
`φ` and `A` analytic, where on `E₊` the function `φ` is purely imaginary with
`φ′(v + i/2) = (4πi/3)(x − F(v))` for a real, even, increasing, convex `F`. The phase is stationary at
`b₀ = v₀ + i/2` and at its mirror image, `F(v₀) = x`, with curvature `α_x = (4π/3) F′(v₀)`; the two points
coalesce as `x` decreases to `F(0)`.

Claim of the lemma: under three largeness conditions on `c′`, the integral equals
`Amp(x) (cos Ψ̂(x) + ε_sd(x))` with `ε_sd` real and `|ε_sd| ≤ ε_core + 2ε_tr + ε_mid + ε_far`, where the four
terms are explicit in `c′`, `α_x`, the chord slope `s_ch = (x − F(0))/v₀`, bounds `C₂`, `C₃` on `φ‴`, `φ⁗`,
bounds `M`, `M′` on `A′/A` and its derivative, and a window `ℓ` that is a minimum of seven quantities.

Proof in the preprint, six steps: (1) factorisation and symmetry; (2) the modulus of `e^{c′φ}` off the edge by
Taylor's theorem and convexity; (3) a contour of five pieces through both saddles along their directions of
steepest descent, and Cauchy's theorem; (4) the middle and far pieces; (5) the expansion at a saddle with
Gaussian moments; (6) assembly.

## What this batch would state (to be fixed after the checks below)

- **A core statement** about two analytic functions `φ` and `A` on the strip (steps 2 to 6): the integral of
  `e^{c′φ} A` over `E₊` in terms of `|A(b₀)|`, `arg A(b₀)`, `Im φ(b₀)`, `α_x` and the four error terms.
- **The lemma's own form** as a corollary (step 1): with `h₀`, the outer factor, the phases and a function `H` in
  the place of the Hankel function `H₀^{(1)}`. The lemma uses `H` only through the exact factorisation
  `H(z) = √(2/(πz)) e^{i(z−π/4)} (1 + ε_H(z))`, which defines `ε_H`; the bound on `ε_H` enters only the remark
  (E.14). Mathlib has no Hankel function at the pin, so `H` is a parameter and the statement says so.

Not in the batch: the verification of the hypotheses for the preprint's function (its appendix E.4 and sections
7.1 to 7.6), the corollaries with unnamed constants unless they come cheaply, and the preprint's theorems. So the
most that this batch can support is the sentence "Lemma E.1 of the preprint, as an abstract statement with the
Hankel function as a parameter, is machine-checked"; it says nothing about whether the preprint applies it
correctly.

## Before any statement is drafted

1. A step referee with a fresh context re-derives the published proof, constant by constant, and tests the lemma
   numerically on instances of its own (among them the Airy instance `F(v) = F₀ + κv²`, where the integral with
   `A = 1` has a closed form).
2. A prior-art reader: explicit remainders for steepest descent near coalescing saddles in print; formalisations
   of the method; what Mathlib has for contour deformation in a strip; any trace of the Lean development that the
   announcement mentions.
3. The owner may run a session of another model family on the lemma, as for batch SPL: an independent derivation
   and an attempt to break the constants. The lead prepares the prompt on request.

## Stop gates

- The step referee finds the lemma false as printed: stop, report to the owner, and decide between a corrected
  statement (which would then not be "Lemma E.1 as printed") and no batch.
- The lemma needs a hypothesis it does not state: the statement carries it and the records say that it differs
  from the printed lemma, and where.
- The contour deformation cannot be done with what Mathlib has at the pin (Cauchy's theorem on rectangles,
  primitives on convex sets) in a reasonable number of lemmas: report before building a general theory.
- The Lean development that the announcement mentions turns out to be public and to contain this lemma: report;
  the batch may then be redundant, or become a comparison.

## Risks, said in advance

The proof is a long chain of explicit constants; the same model family wrote it, will formalise it and will
review the formalisation, so an error in the reading of a hypothesis is the likely failure, not an error that Lean
would accept. The statement has many parameters; a faithful Lean text will be long, and the sanity layer needs an
instance on which every hypothesis holds and the conclusion is not vacuous (the Airy instance is the candidate).
