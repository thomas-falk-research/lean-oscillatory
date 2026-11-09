# Decision: the admissible class of dispersion relations, version 1 (2026-11-09)

The owner approved, in chat on 2026-11-09, the lead's recommendation to fix one input class for every tool that takes
a dispersion relation as input: the singularity census (`docs/prereg/2026-11-09-CENSUS-spec.md`), the LeanCert
hypothesis-discharge experiment (`docs/ROADMAP.md`, industry programme item I2) and any later model-to-theorem
pipeline. The owner's stated goal is a library for the whole industry, not for one consumer; the class is chosen for
breadth across application domains and for exactness. Labels as in `docs/lessons.md`.

## The class (version 1)

A phase on the 2-torus `T² = (ℝ/2πℤ)²` is **admissible** if it is `Ψ = G ∘ u`, where

1. `u ∈ ℚ[cos k₁, sin k₁, cos k₂, sin k₂]` is a trigonometric polynomial with **rational coefficients**;
2. `G` is the identity or a real-analytic function on an open interval `J ⊆ ℝ` whose derivative satisfies
   `(G′)² = R` for a rational function `R ∈ ℚ(x)` with no zero or pole in `J` (version 1 admits exactly
   `G ∈ {id, √·, arccos, arcsin, 2·arcsin(√·)}`, with `J = ℝ, (0, ∞), (−1, 1), (−1, 1), (0, 1)`; a new `G` is a
   revision of this record);
3. the **non-smooth set** `NS(Ψ) = {k : u(k) ∉ J}` is where the formula leaves its analytic branch (`u(k) = 0` for
   `√·`, `u(k) = ±1` for `arccos` and `arcsin`, `u(k) ∈ {0, 1}` for `2·arcsin(√·)`). Ψ is real-analytic on
   `T² ∖ NS(Ψ)`; points of `NS(Ψ)` are reported, never classified as smooth points.

A multi-band model enters band by band, each band admissible on its own; a constant band (a flat band) is reported as
flat and not classified.

**Why every condition becomes exact algebra (VALIDATED, `numerics/census/spec_checks.py`, checks A1).** If
`(G′)² = R` then `G″ = (R′/2R) G′` and, inductively, `G⁽ᵐ⁾ = ρₘ G′` with `ρₘ ∈ ℚ(x)`. By Faà di Bruno every
derivative of Ψ of order ≥ 1 is `G′(u)` times a rational function of `u` and its derivatives, so every condition of
the census classification (`det D²Ψ = 0`, the fold quantity, the reduced quartic, the cubic discriminant) is `G′(u)`
to some power times a rational function. Since `G′ ≠ 0` on `J`, each condition is equivalent on `T² ∖ NS(Ψ)` to a
polynomial equation in `(cos kᵢ, sin kᵢ)` with rational coefficients, and, after the half-angle substitution
`tᵢ = tan(kᵢ/2)` (with a second chart at `kᵢ = π`), to a polynomial system over ℚ in two variables.

## What it covers (each formula machine-checked from its physical definition, `numerics/census/spec_checks.py`)

| Domain | Models in the class (examples) |
|---|---|
| Lattice materials, tight binding | square lattice (with next-nearest neighbours; the King's graph), triangular lattice, graphene (in reciprocal-lattice coordinates, where the coefficients are rational), gapped graphene / hBN |
| Two-band topological models | Qi–Wu–Zhang and anisotropic variants: `ω = √|d(k)|²` with `d` trigonometric |
| Discrete-time quantum walks | Grover walk on ℤ² (`cos ω = −(cos k₁ + cos k₂)/2`) and the walks of Watabe et al. (`cos ω = −(p cos k₁ + q cos k₂)`, p + q = 1) |
| Numerical schemes | 5- and 9-point finite-difference Schrödinger and wave symbols; the 2D Yee/FDTD dispersion relation `ω Δt = 2 arcsin(S √((2 − cos k₁ − cos k₂)/2))` |
| Lattice waves and phonons | discrete wave equation (`√(4 − 2cos k₁ − 2cos k₂)`), discrete Klein–Gordon |

## Options considered

- (a) **Trigonometric polynomials only** (`G = id`). Exact and simple, but excludes every two-band model, every
  quantum walk, the discrete wave and Klein–Gordon equations and FDTD: most of the industrial use. Rejected.
- (b) **Arbitrary analytic expressions** (any composition of elementary functions). Broadest, but zero tests become
  undecidable in general (D. Richardson, *Some undecidable problems involving elementary functions of a real
  variable*, J. Symbolic Logic 33, 514–520, DOI 10.2307/2271358), so a classification could only be numerical; the census and any
  certificate would lose exactness. Rejected for version 1.
- (c) **The class above.** Exact (polynomial systems over ℚ), covers all five domains, and is the natural target for
  certificates (Positivstellensatz identities, interval certificates replayed in Lean). Chosen.

## Not covered by version 1 (stated so nobody infers coverage)

- Bands that are roots of characteristic polynomials of degree ≥ 3 not reducible to the form above (general
  three-band and higher models, e.g. kagome or Lieb lattices with all hoppings generic); band crossings inside a
  multi-band model other than the non-smooth set of a `√·` band.
- Dimension other than 2; continuum phases on ℝⁿ (polynomial phases on boxes are admitted only as controls);
  irrational coefficients (a model with irrational coefficients in one basis may have rational ones in another, as
  graphene does in reciprocal-lattice coordinates; finding such a basis is the user's step and is checked by an
  identity); time-dependent or random symbols.
- Physical validity: the class says which mathematical phases the tools accept. Whether a phase describes a material,
  device or scheme is a modelling question outside it.

## Revisit when

A domain with a concrete consumer needs a phase outside the class (first candidates: three-band lattices, 3D lattices),
or the census shows that an excluded model family dominates the unlocked use cases. A revision is a new dated record
that names what it supersedes; tools state which version of the class they accept.
