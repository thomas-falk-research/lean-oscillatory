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

## 4. The SPL-N prototype that the plan requires (proof agent E; recompiled by the lead)

Done, and in scratch only: `docs/proof-SPL.md` section 5 asked for "a prototype of one certified enclosure of F at
one point" before the rational of SPL-N is chosen. Agent E's file (217 lines, SHA-256
4f160b6ffcd34daef67d97eaf0693b0e4b61267ebc92c81dda2133049f4d2f90) imports `OscInt.Statements.StationaryLeading` and
proves, about the frozen definitions:
- `‖fresnelPrim (13/8) − (A + Bi)‖ ≤ 10^−18` (series of degree 24 with the remainder from `Complex.exp_bound'`);
- the same for `e^{i(13/8)²/2}`;
- `√π` between two rationals `2·10^−19` apart (`Real.pi_gt_d20`, `Real.pi_lt_d20`);
- a general lemma carrying the three enclosures through the formula for `κ₊`;
- `72197/100000 ≤ ‖splKernel (13/8)‖ ≤ 360987/500000` (true value 0.72197396587, margin 3.4e−8).

The lead recompiled it at 5b60142's build (6 s wall clock including imports; agent: about 2.3 s above imports).
`#print axioms` of the six final theorems: propext, Classical.choice, Quot.sound. No forbidden token. Two negative
controls fail as they must: a centre shifted by 1e−17, and an upper bound lowered to 72197/100000. A stress run at
τ = 3.39 (degree 42, radius 10^−15) costs about 1 s.

**Consequence.** The condition of section 5 is met. Point enclosures cost about 45 lines and 1–1.5 s each, so the
choice between 73/100 and the audit's 360987/500000 no longer depends on the arithmetic. It depends on two analytic
pieces that do not exist in the library:
- a second-order interpolation bound for a complex-valued C² function on a cell (agent's estimate 200–400 lines);
- the tail `|κ − L/2| ≤ 4/τ³` (200–400 lines).

The agent's estimate for the whole bridge is 1000–2000 lines. Statement-first rules apply from here: prose, frozen
statement with sanity layer and plants, blind review, and only then the proof. The order claim for SPL-N must
disclose that this one-point prototype existed before the freeze.

## 5. Popov 2008: not read

D. A. Popov, *Remarks on uniform combined estimates of oscillatory integrals with simple singularities*, Izv. Math.
72 (2008) 793–816, DOI 10.1070/IM2008v072n04ABEH002419; Russian original Izv. RAN Ser. Mat. 72:4, 173–196, DOI
10.4213/im1141. The owner asked for it to be read. **It was not read: no route to the text works from this
container.**
- mathnet.ru: the proxy's tunnel closes mid-exchange (`ws_closed_mid_exchange`), and doi.org's redirect times out.
- IOP: the article page is behind a browser challenge (HTTP 403).
- Unpaywall and Semantic Scholar: closed access, no repository copy.
- Crossref: no abstract.
- A lookup of archived copies was refused by the session's permission classifier as an access workaround, and was not
  pursued.

What is known, from secondary sources only:
- the zbMATH review (Softova, zbMATH 1155.42004): asymptotically exact uniform estimates, for a large parameter,
  for singularities `A_k` and `D4±`, by a multidimensional analogue of Vinogradov's estimate, with `D5±` as a
  discussion;
- Akramov–Ikromov, arXiv:2402.04167, introduction, read by the lead: estimates that depend jointly on the large
  parameter and the parameters ("combined estimates") are "a more subtle problem than … uniform estimates (see [16]
  and references in it)".

Second attempt, by the owner's link to the IOP PDF, 2026-11-26: the link returns the article page and not the
PDF. The page says the article is paywalled: "The computer you are using is not registered by an institution with a
subscription to this article". The abstract is readable there, with its mathematics stripped. It adds one fact: the
aim is "asymptotically exact (for [the large parameter] ≫ 1) uniform (with respect to parameters) estimates". An
asymptotically exact uniform estimate over the parameters of a `D4±` unfolding would come close to C1 and C2 with
sharp constants. That raises the weight of this source: it must be read before any wording for C1 or C2.

Whether Popov's constants are explicit, and whether his `D4±` result already contains the envelope with constants,
is **unknown**. Until it is read, the wording of section 1 for C1 and C2 cannot be used. To unblock: the owner
downloads the PDF (the Russian original is normally free on mathnet.ru; the English translation through an
institution) and uploads it to a session.

## 6. Audit items R5, R6, R7 (checker D; R5 spot-checked by the lead)

- **R5, the real-frequency tail. TRUE, and new to this repository.** The bound is
  `|∫_{−π}^{π} e^{i(t cos k + ξk)} dk| ≤ 2π e^{|t| sinh η − |ξ|η} + 2|sin πξ|(1 − e^{−|ξ|η})/|ξ|`.
  - Derivation: the checker re-derived the contour shift, including the signs of the vertical edges and the factor 2.
    The claims at t = 0, at integer ξ and for the leading term `2e^{−it} sin(πξ)/ξ` all hold.
  - Numerics: 22,200 points `(t, ξ)` against two independent evaluations (Jacobi–Anger series at 40 digits, and
    Gauss–Legendre quadrature). Minimum of right side over left side for t > 0: 1.0000000055.
  - The lead's own check (16 points, mpmath quadrature, a few values of η): minimum 1.0000002, reached at
    half-integer ξ far outside the light cone, where the endpoint term is the truth.
  - Relation to the library: at integer ξ it is LC-1 (`OscInt.API.latticeKernel1LightCone`). Off the integers the
    library says only in words that LC-1 fails (`docs/statements.md`, LC-1 paragraph). T0E′ is a different regime;
    neither implies the other.
  - A candidate for a small statement: a real-frequency LC-1 with LC-1 as its integer corollary.
- **R6, the strip bound and the alias bound for matrix symbols. TRUE, largely a duplicate.**
  - Its QWZ case, with the sharper `sinh` form, and the alias bound are already in
    `review/2026-11-10-external-dossier-answers.md` (C5, C6). Its second inequality at d = 2 is T8.3d of
    `review/2026-11-13-external-R3-answers.md`. The signed grid identity is ROADMAP I7.
  - New is only the general finite-hopping form.
  - Three MINOR findings:
    - `D(η)` can be replaced by `Σ‖H_r‖ sinh(η‖r‖₁)`;
    - the factor `e^{dηR}` is lossy by about `e^{η(d−1)R}`;
    - the grid convention must be stated, because on the grid starting at −π with odd N the aliases carry signs.
  - Numerics on QWZ (324,360 cases): the bound exceeds the observed error by a factor of at least 290.
- **R7, the first-order product formula `t²‖[A, B]‖/(2m)`. TRUE and FOLKLORE (Childs et al. 2021, first-order
  case); not in this repository.**
  - Proof re-derived.
  - Numerics: minimum ratio of bound to observed 0.9999966 at an error of 2e−9, which is rounding. A
    double-precision search that reported 1.096 was an artefact: at 50 digits, every case is at most 1.

## 7. Pending at the time of writing

Checker C (numerical falsification of C2, and the envelope of the canonical integral).
