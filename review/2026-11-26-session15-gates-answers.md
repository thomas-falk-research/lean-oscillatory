<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# Session 15: prior-art gates, falsification and prototypes for the audit's work packages (2026-11-26)

Written by the lead. Inputs: `review/2026-11-26-replacement-audit-answers.md` and the owner's instruction to start
the prior-art gate of the D4-to-cusp candidate and to take on the audit's actionable work packages. Checkers and
the proof agent are of the lead's model family, with fresh contexts; briefs, launch and finish times, and hashes are in
`docs/progress/2026-11-26-session15-log.md`. Their reports stay in the lead's scratch; every finding below is in the
lead's words. No human has read any of this.

## 1. The D4-to-cusp candidates: the prior-art gate (checker A, and the lead)

The three candidates, as briefed:
- **C1:** a quantitative local limit with explicit constants.
- **C2:** an α-uniform global bound `|K_α(t, n)| ≤ C t^{−2/3}(1 + |α| t^{1/3})^{−1/4}`.
- **C3:** the general principle, an envelope over the unfolding of D4.

**Verdicts.**
- **C3 is classical.** Y. Colin de Verdière, *Nombre de points entiers dans une famille homothétique de domaines
  de ℝⁿ*, Ann. Sci. ÉNS 10 (1977) 559–575, Théorème 4 with Remarques 2.3 and 2.4.
  - The setting is the universal unfolding of a simple or parabolic singularity. The bound is
    `|I_τ(x)| ≤ C d(x, W_{p+1})^{−μ_{p+1}} ⋯ d(x, W_n)^{−μ_n} τ^{−k/2 + ε_p}`, and the exponents sum to
    `sup β_j · (ε − ε_p)`.
  - For D4 with p = 2 (the cusp stratum) this gives `|I| ≤ C |x|^{−1/4} τ^{−3/4}`. Remarque 2.4 gives `τ^{−2/3}`
    uniformly.
  - Together they give exactly the envelope `min(t^{−2/3}, |α|^{−1/4} t^{−3/4})`. The constants are not explicit.
  - Read by the checker in full text, pp. 562–565. The lead read the same pages in the checker's OCR text, which is
    badly garbled. The theorem's structure and the two remarks are legible and agree with the checker's reading.
    The exponent 1/4 rests on the checker's reading of the table of `β_j`.
- **C2 without explicit constants follows** from C3, together with Karpushkin's uniform estimates (1984) and
  compactness on the torus.
  - The reduction from this versal three-parameter family to the universal unfolding is the checker's own argument,
    not something read in a source: PLAUSIBLE.
  - **C2 was not found stated for this lattice in the literature searched.**
- **C1 is classical qualitatively**: the expansions of Duistermaat 1974, as quoted by Colin de Verdière p. 563, give
  a relative error of `O(t^{−1/3})` with constants that are not explicit. The limit profile is DLMF's
  hyperbolic-umbilic integral `Ψ^(H)` after a shift, a polynomial identity the checker verified numerically.
- **What remains, and how to word it.** Explicit constants (and a machine-checked proof) for C1 and C2 were not
  found in the literature searched. Wording for any later statement: "a version with explicit constants of the
  classical estimates of Colin de Verdière (1977, Théorème 4) and Karpushkin (1984), for this lattice family; the
  explicit constants were not found in the literature searched."
- **Sources still unread, ranked:**
  1. V. N. Popov, Izv. Math. 72 (2008) 793–816, on uniform combined estimates for `A_k` and `D4±`. Abstract only. It
     is the most likely place for explicit constants, and it must be read before any wording of C1 or C2 is used.
  2. Duistermaat, CPAM 27 (1974), in full.
  3. Karpushkin 1984 and 1988, in full.
  4. Berry–Upstill 1980.

**MAJOR, against the lead's answers of 2026-11-26.** For small α ≠ 0 there are four A3 points, not two:
- two at `(±π/2, ±π/2)` with matching signs;
- two near the anti-diagonal D4 points, displaced to about `k₀ + 2α(1, −1)`.

There is no A4 or D4 point. Checker A found this by Newton's method. The lead confirmed it by a second method: a
mpmath root search on `det H = 0 = D³Ψ[v, v, v]` from a 24 × 24 grid of starts over the whole torus. It found exactly
four points for α ∈ {0.01, −0.01, 0.1}, with the anti-diagonal offsets 0.0200013(±1, ∓1) for |α| = 0.01 and
0.201358(±1, ∓1) for α = 0.1. Section 3 of those answers says that "the only A3 point of the slice `a ≠ 0` is the
origin". That holds in the local model at `(π/2, π/2)` only. It is not true on the torus, because the anti-diagonal
D4 points unfold differently. The answers file is a record and is not edited; this paragraph is the correction. The
envelope is the same at all four points, so C2 is not threatened, but a global proof must treat all four D4
neighbourhoods.

**Consequence for the ranking.** The D4-to-cusp direction is no longer a route to a result that is new beyond its
constants. The previous ranking called it "the best route to a result that is not only a formalization"; on this
evidence it is a formalization with explicit constants of classical mathematics, like most of this library. That
is still of value, and it is the honest description.

## 2. Report D's 38/5: the prior-art gate advanced (checker B)

- **38/5 was not found in the literature searched** (55 logged queries; zbMATH Open, arXiv with LaTeX sources,
  Crossref, OpenAlex citing works, MathOverflow, web).
- The smallest constant in print for the unweighted third-derivative lemma is Rogers's `3 · 32^{1/3} = 9.5244`
  (Proc. Amer. Math. Soc. 133 (2005) 3543–3550, Lemma 5 with n = 3). The checker read the arXiv source and the
  thesis in full; the published version was not read.
- Derived but not printed: splitting at the level of `f″` and using Kershner's sharp second-derivative constant
  `C₂ = 3.3643` gives `3(2C₂²)^{1/3} = 8.4865`.
- No argument that splits through a second-derivative bound can reach 7.6, because that would need
  `C₂ ≤ 2.8512` while `C₂ ≥ 3.3335`. So 38/5 must come from a different argument, which report D's has.
- A side finding: Kershner's printed value of the sharp constant (3.327) disagrees with the recomputed
  3.364318. Rogers's thesis and a footnote of Patel–Yang agree with 3.3643, which matches the earlier finding under
  report A.
- **Unread:**
  - Catalá de la Torre, Amer. Math. Monthly 122 (2015) 138–142 (abstract only, probably the first-derivative case);
  - Arkhipov–Karatsuba–Chubarikov in the original;
  - the published version of Rogers.
- **Human-only checks the owner can make** (Google Scholar and MathSciNet do not admit agents): "Cited by" for Rogers
  2005 and for both Kershner papers; MathSciNet's citation list of MR2163589; the phrase searches `"van der Corput"
  "third derivative" integral constant` and `"van der Corput lemma" "sharp constant" cubic`.

## 3. The SPL-N arithmetic: cost measured (the lead)

The audit's 40-cell exact-rational certificate for `sup |κ| ≤ 360987/500000` was transcribed into Lean definitions
over ℚ and checked with `decide +kernel`, which the guard allows. All 40 cells and the coverage of `[1/2, 4]` are
accepted in about 1.3 s of kernel time. The only axioms are propext, Classical.choice and Quot.sound.

Two negative controls were proved as theorems (each `= false` by the kernel): the bound lowered to 72197399/10^8
fails, and the cover with one cell removed fails.

So the arithmetic does not decide the choice of rational. The analytic bridge does: a series enclosure of κ from the
frozen definitions, an interpolation lemma for vector-valued C² functions, the tail `4/x³`, and `|κ″| ≤ 2/x`.

## 4. Pending at the time of writing

Checker C (numerical falsification of C2, and the envelope of the canonical integral), checker D (audit items R5, R6,
R7) and proof agent E (a one-point certified enclosure, the prototype that `docs/proof-SPL.md` section 5 requires).
Their results are recorded below when they finish.
