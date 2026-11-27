<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# External handoff: global type classification of the anisotropic triangular lattice phase (2026-11-26/27)

Written by the lead. The owner delivered a handoff from an independent researcher (another model family). It
consists of a derivation (`HANDOFF.md`, 105 lines) and an archive with a SymPy script and its output. Archive
SHA-256 ff2f9ed38b755063ad4b015ca2d6e0c38da1e1027a7ddc6060836869d3a34a97; handling and every hash are in
`docs/progress/2026-11-26-session15-log.md`. The handoff is not committed or reproduced; findings are in the lead's
words. It answers section 7 of `review/2026-11-26-session15-gates-answers.md` (the A5 point found by checker C).

**Who checked.**
- The lead, with SymPy computations of its own.
- Referee F: fresh context, lead's model family, its own scripts and numerics. Brief SHA-256 27ac4de4….
- Checker G: prior art, pending at the time of writing.

No Lean was run on any of it, and no human has read it.

## 1. The claims

For `Ψ_α(x, y) = cos x + cos y + α cos(x + y)`, "type" means the singularity type of `Ψ_α(k) − ∇Ψ_α(k₀)·k` at `k₀`.

- **K1 (classification over the whole torus).**
  - α = 0: the only types are A1, A2 and D4. D4 occurs exactly at the four points `cos x = cos y = 0`.
  - α ≠ 0: the only types are A1, A2, A3 and A5. A3 occurs at the matching-sign points `(±π/2, ±π/2)`.
  - **A5 occurs if and only if `|α| = α* = 1/(2√2)`.** For α > 0 the A5 points are exactly `(θ, −θ)` with
    `cos θ = −2α`, which at α* means `θ = ±3π/4`.
  - There is no A4 and no D-type point for α ≠ 0.
- **K2 (fixed-coupling sharp decay).** For each fixed α, `sup_n |K_α(t, n)| ≍ t^{−2/3}` if
  `α ∈ {0, ±α*}`, and `≍ t^{−3/4}` otherwise. The constants depend on α; nothing uniform in α is claimed.
- **K3 (coefficients).**
  - The reduced quartic of the anti-diagonal cusp is `(8α² − 1)/(32α)` (unit coordinate).
  - At α* the reduced sextic is `−u⁶/(48√2)`. This replaces checker C's fitted value −0.0147.
- **Route of the proof.**
  - Exact polynomial identities in `c = cos s`, `d = cos v`, `l = sin s`, `m = sin v`, with `s = (x+y)/2` and
    `v = (x−y)/2`.
  - An elementary sign argument with a rational certificate, which excludes A4 off the symmetry line with no
    root isolation or cylindrical decomposition.
  - Elimination on the symmetry line.
  - For K2: patches, a parametric implicit-function and Morse reduction, and van der Corput of order m = 2, 3,
    4, 6 for the upper bound. For the lower bound, normal-form asymptotics and a localisation identity that turns
    a localised integral at a non-integer velocity into an ℓ¹ combination of lattice values.

## 2. What was checked, and by whom

**The lead's checks (scripts `lead_check.py` and `lead_sextic.py` in scratch):**
- the second, third and fourth derivatives differentiated by SymPy from the phase itself; the handoff's script
  types them in by hand;
- `det H = 4D` and `H·V = (−2D, 0)`;
- the three identities of the handoff's section 2: residuals exactly 0;
- the sextic by power-series elimination of the transverse variable in the original coordinates `(x, y)`, a
  route different from the handoff's elimination in `s`. The reduced phase is
  `−3√2/4 + 0·u + 0·u² + 0·u³ + 0·u⁴ + 0·u⁵ − (√2/96)u⁶`, and `√2/96 = 1/(48√2)`. The transverse Hessian is `2α*`;
- the sign certificate by a second method, Sturm root counting: `F` has no root on `[1/2, 19/20]`, and `B` has none
  on `[19/20, 1]` (`B(19/20) = −89/500`);
- the handoff's own script passes when run from a copy.

**Referee F (findings in the lead's words):**
- **Case split: SOUND.** It is exhaustive: `D ≠ 0`; `c = 0`; `d = 0`; `c = d = 0`, where `D = −1`; `cd ≠ 0` with
  `l ≠ 0`, which includes `m = 0`; and `cd ≠ 0` with `l = 0`. The case `2P = 1` forces `Q = 1/2` on `D = 0`,
  where `G = −1/2`. The torus identifications leave the predicate unchanged.
- **The reduced-quartic criterion: SOUND.** It was re-derived for a non-unit kernel vector and any transverse W,
  since `H[V, W] = 0` automatically. On `D = 0` it vanishes if and only if `G = 0`.
- **Exclusion of A4: SOUND.**
  - The boundaries `Q = 1`, `1/2` and `19/20` and the case `B = 0` were checked.
  - The resultant of E and G in P is `4Q²(Q − 1)(2Q − 1)F(Q)`, an independent confirmation of the elimination.
  - F's real roots, 0.1106 and 0.9813, lie in the regions excluded by `P > 1` and `B < 0`.
- **The A5 point: SOUND.**
  - The formula for `g′(s)` was re-derived.
  - In the unit coordinate, 40-digit numerics give `g₆ = −0.0147313912747 = −1/(48√2)`.
  - `g₄` matches `(8α² − 1)/(32α)` at seven values of α.
  - At α = 1/2 the point `θ = π` is A3, with `g₄ = 1/16`.
  - NIT: the sixth-root change of variable is of `k(u)/k(0)`.
- **The predicate against direct computation: SOUND.**
  - 322 random points on `det H = 0` for eight values of α (including −0.3 and 2), with 0 mismatches.
  - The off-axis cusps found (four or six, for α from 0.4 to 5) are all A3, and `g₄` matches the predicate's
    formula to 10 digits.
  - None were found for α ≤ α*. This is consistent with cusps bifurcating out of the A5 point, but a random-start
    search is not a count.
  - No A4 anywhere.
- **The route to K2: a correct sketch, not yet a proof of record. GAP, MAJOR (process).**
  - Uniformity in the velocity: SOUND, provided the order of choices is stated: the parameter radius first, then
    the patch shrunk so that `|∇Ψ − ∇Ψ(k₀)| < ρ/2`. This is MINOR; the handoff leaves the order implicit.
  - Transverse Morse with van der Corput: SOUND. The amplitude after the transverse integration has variation
    `O(t^{−1/2})`.
  - The localisation identity: SOUND.
    - `∫ = (2π)² Σ_j χ̂_t(j) K(t, n + j)`; the signs check, and `|δ| ≤ √2/2`.
    - The ℓ¹ bound on `χ̂_t` is uniform, by `(1 − Δ)²`.
    - The tail control in the monomial asymptotics is only asserted (MINOR).
  - No interference problem between stationary points.
  - The weakest step: the uniform C^k bounds of the parametric normal form are asserted, not shown, and the
    standard lemmas (parametric implicit-function and Morse lemmas with uniform bounds, van der Corput with
    amplitude, the monomial asymptotics) are cited, not written out.

## 3. Verdicts

- **K1: PROVEN (on paper; one fresh referee of the lead's family; no finding beyond a NIT; the identities
  re-derived by two independent computations).** Not machine-checked.
- **K3: PROVEN**, on the same basis. The sextic is exact, and the fitted value in section 7 of the gates answers
  is superseded.
- **K2: a correct proof route, not a proof of record** (the MAJOR process gap above). Label until the lemmas are
  written out and refereed: CONJECTURED, with strong support. It is consistent with checker C's decay slopes at
  seven values of α and with the `t^{−2/3}` plateau observed at α* up to t = 262144.
- **Novelty: not found in the literature searched** (checker G, section 5).

## 4. What it changes

- **C2 must be restated, and the handoff says so too.** A uniform estimate across `|α| = α*` is impossible. The
  handoff's section 6 proposes a second crossover near α*, at detuning scale `t^{−1/3}` and with a sextic
  canonical integral, as an unproved conjecture. It is not checked here, except the α-derivative 2 of the
  quartic at α*, which referee F confirmed.
- **A candidate next batch**, in statements that keep explicit constants and parameter-uniform claims separate:
  1. the classification predicate (algebra only: ring identities, trigonometric identities and a sign certificate;
     no cylindrical decomposition);
  2. the anti-diagonal coefficients and the A5 witness;
  3. the fixed-α upper bound, which needs an A5 local lemma that extends the A3 route;
  4. the fixed-α lower bound, through the localisation identity.

  Which batch comes next is the owner's decision. The handoff's priority order is a proposal.

## 5. Prior-art gate (checker G, 2026-11-27)

Checker G: fresh context, brief SHA-256 91415590…. It ran 47 logged queries (zbMATH, arXiv, Crossref, MathOverflow,
OpenAlex), web and alphaXiv searches, greps of 11 arXiv LaTeX sources, and a forward and backward chase of two
levels from Ge–Hua–Jia–Zhou and Bi–Cheng–Hua. Findings in the lead's words:

- **The only published case of this model is the isotropic one**, α = 1: Ge, Hua, Jia, Zhou, Calc. Var. PDE 64
  (2025) art. 176, arXiv:2412.02947v2, read in full.
  - Hessian corank at most 1; every degenerate point A2 or A3 (Lemma 4.3); no A4 in one case (Proposition 6.1); the
    upper bound `C⟨t⟩^{−3/4}` (Theorem 1.3).
  - Its proof is incomplete: one case is "similar, omitted".
  - The labels A2 and A3 are interchanged in one case relative to its own expansion; the expansion agrees with K1.
  - Theorem 1.3 says "sharp", but the checker found no lower-bound argument.
  - **MAJOR (citation hygiene):** this repository must not cite it for sharpness, or for a complete classification
    at α = 1. Our own proof must cover α = 1, and the lower bound at every α.
- **Closest analogues, different models:**
  - Cuenin–Ikromov (discrete Klein–Gordon): only `A_k` with `k ≤ 3` on ℤ²; an A5 point on ℤ³ at an algebraic
    parameter value.
  - Borovyk–Goldberg (Klein–Gordon on ℤ² with two axis couplings): "there is no choice of parameters that generates
    exceptional degeneracy". Diagonal coupling is the only route to an exceptional A5 that the checker found.
  - Cheng, arXiv:2403.07445, Theorem 1.1 (`Δ² − γΔ` on ℤ²): the rate is `t^{−3/4}` except at three values of γ.
    This is the closest structural analogue of K2.
  - The higher-order van Hove literature (Chandrasekaran et al.; Yuan–Isobe–Fu) treats points where the gradient
    vanishes. Every degenerate point of K1 has a nonzero gradient, so it does not cover K1.
- **Verdicts:**
  - K1 for general α, the A5 point at `|α| = 1/(2√2)`, and the absence of A4 and D-types: **not found in the
    literature searched**. At α = 1 it is consistent with Ge et al. At α = 0 it is FOLKLORE.
  - K2 off α ∈ {0, 1}, the two-sided bounds, and the exceptional set `{0, ±1/(2√2)}`: **not found in the literature
    searched**. α = 0: Stefanov–Kevrekidis 2005, cited, not read. α = 1: an upper bound only, Ge et al.
  - K3: not found. The checker also recomputed it by a third independent route: raw coefficients
    `(8α² − 1)/(8α)` for u⁴ and `−1/(192α³)` for u⁶ in its own scaling, the same values in the unit coordinate.
    MINOR: a paper must state the normalisation of the kernel vector.
- **Not read:** Schultz 1998; Stefanov–Kevrekidis 2005; Karpushkin 1983/84; Ge–Lu–Yu 2025; the papers on caustics
  of two-dimensional quantum walks (Baryshnikov–Brady–Bressler–Pemantle); two optics papers on discrete diffraction
  in triangular arrays; a triangular-lattice Green's function paper (2004).
- **Human-only queries for the owner:**
  - Google Scholar: "Cited by" for Ge et al., Borovyk–Goldberg and Cuenin–Ikromov; `"triangular lattice"
    "dispersive estimate"`; `anisotropic triangular lattice Strichartz`; `"next-nearest-neighbor" "discrete
    Schrödinger" decay`.
  - MathSciNet: MSC 35Q41 or 39A12 with "triangular lattice"; papers whose reference lists cite Ge et al.

**Wording available today** (calibrated, not a priority claim): "We could not find the classification for general α,
the exceptional coupling `|α| = 1/(2√2)`, or the fixed-coupling two-sided decay away from α = 0, 1 in the literature;
we searched zbMATH Open, arXiv (including LaTeX sources), Crossref, OpenAlex and MathOverflow on 2026-11-27 and
followed citations from Ge–Hua–Jia–Zhou and Bi–Cheng–Hua. The closest results are Ge–Hua–Jia–Zhou (α = 1, upper bound),
Cuenin–Ikromov and Cheng (other lattice models with exceptional parameters)."

## 6. State

The owner has more research to deliver before implementation starts. Nothing for batch TRI is registered or frozen.
A draft of a registered numeric test was written, found defective on reading before any run (signs for α < 0, a
useless Bessel tail bound, a coarse step), and moved out of the tree unregistered.
