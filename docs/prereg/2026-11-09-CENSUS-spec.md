# Specification: singularity census of 2D dispersion relations (CENSUS)

Status: DRAFT, 2026-11-09 (session 8). It is frozen by a commit after the spec-fidelity referee (`assets` of the
computation-of-record protocol; report under `review/`) and before either implementation exists. Changes after freezing
and before registration are listed in §8, and both implementations are re-checked against them; none are allowed after
registration (`docs/prereg/2026-11-09-CENSUS-prereg.md`). An implementer reads only this file and the files it names.

Numerics and computer algebra are tooling, never evidence for a Lean theorem (README). The census decides which
theorems OscInt proves next (`docs/ROADMAP.md`, industry programme I1); a model is "covered by OscInt" only when its
classification is discharged in Lean, which this census does not do.

## 0. Notation and conventions

- `T² = (ℝ/2πℤ)²`, points `k = (k₁, k₂)`, represented in `(−π, π]²`. `cᵢ = cos kᵢ`, `sᵢ = sin kᵢ`.
- For a function Ψ real-analytic near `k₀`: `H = D²Ψ(k₀)` (symmetric 2 × 2, entries `p = H₁₁`, `q = H₁₂`, `r = H₂₂`),
  `T = D³Ψ(k₀)`, `Q = D⁴Ψ(k₀)` (symmetric tensors); `T[a, b, c] = Σ Tᵢⱼₖ aᵢ bⱼ cₖ`, likewise `Q[a, b, c, d]`.
- All model coefficients are rational. Exact numbers are written as fractions or closed forms; decimals in this file
  are labelled "≈" and are reference values only (§7).

## 1. Admissible phases

Exactly the class of `docs/decisions/2026-11-09-input-language.md` (version 1): `Ψ = G ∘ u` with `u` a trigonometric
polynomial with rational coefficients and `G ∈ {id, √·, arccos, arcsin, 2·arcsin(√·)}` on its open interval `J`
(`ℝ, (0, ∞), (−1, 1), (−1, 1), (0, 1)`). The **non-smooth set** is `NS(Ψ) = {k ∈ T² : u(k) ∉ J}`. Every derivative
of Ψ of order m ≥ 1 equals `G′(u)` times a rational function of `u` and the derivatives of `u` up to order m
(`(G′)² = R ∈ ℚ(x)`, `G⁽ᵐ⁾ = ρₘ G′`, `ρₘ ∈ ℚ(x)`, ρ₁ = 1, `ρₘ₊₁ = ρₘ′ + ρₘ R′/(2R)`; VALIDATED for m ≤ 6 by
`numerics/census/spec_checks.py`, checks A1).

## 2. Classification of a point (definitions fixed now)

The census classifies **every** point `k₀ ∈ T²` of each phase. At `k₀ ∉ NS(Ψ)` the type is that of the critical point
`k₀` of `φ_{k₀}(k) = Ψ(k) − ∇Ψ(k₀)·k` (the phase of the propagator kernel for the observation direction
`x/t = −∇Ψ(k₀)`); it depends only on `H, T, Q, …` at `k₀`. Types (Arnold's names for the classes of critical points of
functions of two variables; V. I. Arnold, S. M. Gusein-Zade, A. N. Varchenko, *Singularities of Differentiable Maps,
Volume 1*, Birkhäuser Boston, DOI 10.1007/978-0-8176-8340-5, record checked against Crossref 2026-11-09):

**2.1 Non-smooth.** `k₀ ∈ NS(Ψ)`: type **NS**. Not classified further.

**2.2 Rank 2.** `det H ≠ 0`: type **A1** (nondegenerate).

**2.3 Rank 1.** `det H = 0`, `H ≠ 0`. Kernel vectors `v_a = (q, −p)`, `v_b = (r, −q)`: both lie in `ker H` and are
parallel, and they vanish together only if `H = 0` (`H v_a = (0, −det H)`, `H v_b = (det H, 0)`,
`v_a × v_b = det H`; check R2). Let `v` be either one that is nonzero. Then:
- **A2** (fold) iff `T[v, v, v] ≠ 0`. Equivalently: **not** (`T[v_a, v_a, v_a] = 0` and `T[v_b, v_b, v_b] = 0`).
  An implementation must never decide "g3 = 0" from one of the two contractions alone: at points where that kernel
  vector is the zero vector its contraction vanishes trivially (this happened in the development of the check
  script, control K1 at τ = 3/4; §8).
- If `T[v, v, v] = 0`: choose any `w` with `H[w, w] ≠ 0` (every `w ∉ span v` works) and set
  `g4 = Q[v, v, v, v] − 3 T[v, v, w]² / H[w, w]`. It is independent of the choice of `w` when `T[v,v,v] = 0`
  (check R3), scales as `|v|⁴` under `v ↦ λv`, and is 24 times the u⁴ coefficient of the function obtained by
  eliminating the transverse variable (splitting lemma; check R1: `g(u) = T[v,v,v] u³/6 + g4 u⁴/24 + O(u⁵)`).
  **A3** (cusp) iff `g4 ≠ 0`; **A≥4** iff `g4 = 0`.

**2.4 Rank 0.** `H = 0`. The binary cubic `C(κ) = T[κ, κ, κ] = a κ₁³ + b κ₁²κ₂ + c κ₁κ₂² + d κ₂³` with
`a = T₁₁₁, b = 3T₁₁₂, c = 3T₁₂₂, d = T₂₂₂` and discriminant
`Disc = b²c² − 4ac³ − 4b³d − 27a²d² + 18abcd`:
- **D4** iff `Disc ≠ 0` (three distinct linear factors over ℂ);
- **D≥5** iff `C ≠ 0` has exactly two distinct linear factors (a double factor) — the 3-jet class of the series
  D_k, k ≥ 5 (and of non-isolated D∞ points);
- **E/J** iff `C` is the cube of a linear form or `C = 0` — the 3-jet classes of E6, E7, E8, J10 and deeper.
These are 3-jet classes; the census does not determine k in D_k or the E/J subclass.

**2.5 Isolated and non-isolated.** Let `Σ(Ψ)` be the set of points of `T² ∖ NS(Ψ)` of type A3, A≥4, D4, D≥5 or E/J,
i.e. the common zeros off NS of `det H`, `T[v_a, v_a, v_a]` and `T[v_b, v_b, v_b]` (at rank 0 both kernel vectors
vanish). In the half-angle coordinates of §6 it is a semi-algebraic set, so it has finitely many connected components,
each a point, a curve or a two-dimensional set; it is reported that way. A point of `Σ(Ψ)` on a
component of positive dimension has type **NI** (non-isolated) in addition to its pointwise type, and the component is
reported with the pointwise types that occur on it.

**2.6 Flat bands.** A band that is constant on `T²` is reported as FLAT and not classified.

## 3. Corpus (fixed now)

Every phase below is admissible (§1); its formula, its non-smooth set and its gap are machine-checked from the
physical definition by `numerics/census/spec_checks.py` (check names in the table). Two-band models are classified
through the upper band `ω`; `−ω` has the same types. Weights: each **family** has total weight 1, shared equally by its
members, so parameter instances cannot inflate a family (§4.3).

| ID | Family (domain) | Phase Ψ on T² | NS(Ψ) | Check | Source of the model (verification key below) |
|---|---|---|---|---|---|
| M01 | square (L) | `c₁ + c₂` | ∅ | K-SQ | discrete Laplacian symbol: Stefanov–Kevrekidis 2005 [CR][arX] |
| M02 | square (L) | `c₁ + c₂ − (3/5)c₁c₂` (t–t′ model, t′/t = −3/10) | ∅ | M-SQNNN | t–t′ band −2t(cos kₓ + cos k_y) − 4t′cos kₓ cos k_y (+ const.): Irkhin–Katanin–Katsnelson 2002, eq. (2) [CR] (sign of t′ varies between papers) |
| M18 | square (L) | `c₁ + c₂ + 2c₁c₂` (t–t′ at t′ = t: King's graph) | ∅ | M-KING | King's-graph symbol: Wan–Zhang, arXiv:2507.20142 [arX] |
| M03 | triangular (L) | `c₁ + c₂ + cos(k₁ + k₂)` | ∅ | — | triangular lattice as a Cayley graph of ℤ²: Ge–Hua–Jia–Zhou 2025, eq. (1.5) [CR][arX] |
| M04 | triangular (L) | `c₁ + c₂ + (1/2)cos(k₁ + k₂)` | ∅ | — | anisotropic deformation of M03 (no source; mathematical family member) |
| M05 | honeycomb (L) | `√(3 + 2c₁ + 2c₂ + 2cos(k₁ − k₂))` (graphene, reciprocal-lattice coordinates) | `{(2π/3, −2π/3), (−2π/3, 2π/3)}` | M-GRAPHENE, M-GRAPHENE-CN, M-GRAPHENE-NS | Castro Neto et al. 2009, eq. (6) at t′ = 0 [CR] |
| M06 | honeycomb (L) | `√(1/4 + 3 + 2c₁ + 2c₂ + 2cos(k₁ − k₂))` (staggered potential Δ = t/2) | ∅ | M-GRAPHENE, M-hBN | own derivation from the 2 × 2 Hamiltonian with sublattice potential ±Δ (check M-hBN); physical model Semenoff 1984 [CR, abstract only] |
| M07 | QWZ (T) | `√(3 + 2(c₁ + c₂) + 2c₁c₂)` (m = 1) | ∅ (P ≥ 1) | M-QWZ, G-QWZ1 | Asbóth–Oroszlány–Pályi 2016, eq. (6.1) [CR]; original model Qi–Wu–Zhang 2006 [CR][arX] (same `|d|` up to a scale and a k-independent term, see the sweep) |
| M08 | QWZ (T) | `√(11 + 6(c₁ + c₂) + 2c₁c₂)` (m = 3) | ∅ (P ≥ 1) | M-QWZ, G-QWZ3 | as M07 |
| M09 | QWZ (T) | `√(sin²k₁ + (9/25) sin²k₂ + (3 + c₁ + c₂)²)` (d₂ scaled by α = 3/5, m = 3) | ∅ (P ≥ 1) | M-aQWZ, G-aQWZ | anisotropic deformation of M08 (no source; mathematical family member) |
| M10 | Grover walk (W) | `arccos(−(c₁ + c₂)/2)` (dispersive bands; flat bands ±1 reported FLAT) | `{(0, 0), (π, π)}` | M-GROVER | Watabe–Kobayashi–Katori–Konno 2008, eq. (7) at p = 1/2 [CR][arX] |
| M11 | arccos (none) | `arccos(c₁/2 + 3c₂/10)` | ∅ | G-ARCCOS | **no verified physical model** (the verified walk family of Watabe et al. has a + b = 1); kept to re-examine the P1 grid verdict; **weight 0** |
| M12 | FD9 Schrödinger (N) | `(1/6)(20 − 8(c₁ + c₂) − 4c₁c₂)` (9-point Laplacian, h = 1) | ∅ | M-FD9, M-FD9-TT | 9-point stencil: Ji–Tabrizi–Karma 2022, eq. (25) [CR][arX]; up to an affine map the t–t′ family at t′/t = 1/4 |
| M13 | Yee FDTD (N) | `2 arcsin(√(S²(2 − c₁ − c₂)/2))` = `arccos(1 − 2S² + S²(c₁ + c₂))`, S = 1/2 (Δx = Δy, S = cΔt/Δx) | `{(0, 0)}` | M-YEE, M-YEE-ARCCOS, G-YEE | 3D Yee relation in Cheng et al., arXiv:2001.10721, eqs. (2)–(3), and Blinne et al. 2018 [CR], reduced to 2D (own step); Taflove–Hagness not read |
| M14 | Yee FDTD (N) | as M13 with S = 7/10 (2S² = 49/50 < 1, below the 2D limit 1/√2) | `{(0, 0)}` | M-YEE, G-YEE | as M13 |
| M15 | FD9 wave (N) | `√((1/6)(20 − 8(c₁ + c₂) − 4c₁c₂))` | `{(0, 0)}` | M-FD9, M-FD9-NS | semi-discrete wave equation with the stencil of M12 (own construction) |
| M16 | lattice KG / wave (P) | `√(4 − 2c₁ − 2c₂)` (discrete wave equation, monatomic square mass–spring lattice) | `{(0, 0)}` | — | Bi–Cheng–Hua, arXiv:2312.04130 [arX]; Schultz 1998 [CR, not read] |
| M17 | lattice KG / wave (P) | `√(5 − 2c₁ − 2c₂)` (discrete Klein–Gordon, mass 1) | ∅ | K-DKG | Cuenin–Ikromov 2021 [CR][arX]; Borovyk–Goldberg 2017 (λ₁ = λ₂ = 1) [CR][arX] |

Verification key: [CR] bibliographic record checked against Crossref, [arX] arXiv text read, [CR, not read] record
only; all on 2026-11-09 in the logged sweep `review/2026-11-09-CENSUS-prior-art-sweep.md` (full references there and in
`docs/prior_art.md`, "Singularities of lattice dispersion relations").

Domains: L lattice materials, T two-band topological models, W discrete-time quantum walks, N numerical schemes,
P lattice waves and phonons. Families and weights: square {M01, M02, M18}, triangular {M03, M04}, honeycomb
{M05, M06}, QWZ {M07, M08, M09}, Grover {M10}, FD9 Schrödinger {M12}, Yee {M13, M14}, FD9 wave {M15}, lattice KG / wave
{M16, M17}: nine families of weight 1; M11 is classified and reported but has weight 0 and no domain. Not in the corpus,
because it is an affine image of M01 with identical types: the 5-point finite-difference Schrödinger symbol
`4 − 2c₁ − 2c₂`. The NS sets in the table follow from: M05,
`|1 + e^{−ik₁} + e^{−ik₂}| = 0` (check M-GRAPHENE-NS); M10, `|c₁ + c₂| = 2`; M13–M16, `u = 0` only at `cᵢ = 1`
(each term `1 − cᵢ ≥ 0`; for M12 and M15, with `aᵢ = 1 − cᵢ ∈ [0, 2]`,
`20 − 8(c₁ + c₂) − 4c₁c₂ = 12a₁ + 12a₂ − 4a₁a₂ ≥ 4a₁ + 12a₂`, zero only at (0, 0), check M-FD9-NS; for M13–M14 also
`v ≤ 2S² < 1`).

## 4. Output and observables

**4.1 Per model (and per control).** The sets `NS(Ψ)` and `Σ(Ψ)` (§2.5), with, for every isolated point: its type, an
exact description where the method gives one (implementation A: the chart, a defining polynomial system over ℚ and a
rational isolating box in the half-angle coordinates that can be refined on request), and an enclosure (a box in `k`,
outward-rounded decimal endpoints, width ≤ 1e−12 in each coordinate); for every non-isolated component: an exact
description (A: defining polynomials, and at least 16 exact sample points spread along the component, each given like
an isolated point) or covering boxes (B), and the types on it; whether `{det H = 0} ∖ (NS ∪ Σ)` (the fold set) is
empty.

**4.2 Coverage predicate.** A model is **GD-covered** if `Σ(Ψ)` consists of finitely many D4 points and `NS(Ψ) = ∅`
(the hypothesis of OscInt's global theorems GD, GD-F, GD-C, GD-N and their vector versions; every other point is then A1
or A2). Extension families: **F-A3** (finitely many A3 points allowed), **F-A4** (finitely many A≥4 points), **F-D5**
(finitely many D≥5 points), **F-E** (finitely many E/J points), **F-NI** (non-isolated components allowed), **F-NS**
(a nonempty finite NS set allowed). A model is covered by GD ∪ S, for a set S of families, if every object it has
outside GD's hypothesis belongs to a family in S. This is a necessary condition for a decay theorem of the GD form, not
a sufficient one (uniformity in the linear term, amplitude conditions and global assembly are separate theorems).

**4.3 Unlock score.** For a family F: `N(F)` = the total weight (§3) of the corpus models covered by GD ∪ {F} and not
by GD; `D(F)` = the number of domains (L, T, W, N, P) with at least one such model. Also reported for every pair
{F, F′}. The ranking rule that uses these numbers is fixed in the registration (§4 there), not here.

## 5. Controls and known answers (expected outcomes fixed now)

All exact; checks in `numerics/census/spec_checks.py`. Controls K1–K3 are polynomial phases on the box
`B = [−1, 1]²` (not on T²); the census treats them with the same definitions (§2) and reports every point of `B`.

| ID | Phase | Expected (exact) | Check |
|---|---|---|---|
| K-SQ | M01 | `Σ` = the four D4 points `(±π/2, ±π/2)`; no A3, A≥4, D≥5, E/J, NI; fold set nonempty | K-SQ |
| K-QWZ3 | M08 | `Σ` contains the four A3 points `(±a, ±a)`, `a = arccos(−1/3)` (more points may exist; the census decides) | K-QWZ3 |
| K1 | `X²Y + Y²`, `(X, Y) = R((x, y) − r)`, `R = [[3/5, −4/5], [4/5, 3/5]]`, `r = (1/7, −2/9)`, on B | `Σ ∩ B = {r}`, type A3; no rank-0 point | K1 |
| K2 | `X²Y + Y⁴`, `(X, Y) = (x, y) − (−1/5, 1/3)`, on B | `Σ ∩ B = {(−1/5, 1/3)}`, type D≥5 | K2 |
| K3 | `X³ + Y⁴`, `(X, Y) = (x, y) − (2/7, −1/11)`, on B | `(2/7, −1/11)` of type E/J; the segment `{y = −1/11} ∩ B` minus that point of type A3 + NI; no other point of `Σ` | K3 |
| K5 | `√((c₁ + c₂)² + 1/4)` on T² (separable trap) | the two lines `k₁ ± k₂ = π` (mod 2π): A≥4 + NI, except their crossing points `(0, π)` and `(π, 0)`, of type E/J + NI | K5 |

**External known answers (published classifications; read in the sweep, arXiv versions).** These are expectations
from the literature, not exact facts established here; a disagreement is handled by the registration (§4 there).
- X-DKG (M17): A3 exactly at the four points with `cos k₁ = cos k₂ = 0`, no A≥4 (Cuenin–Ikromov 2021, Prop. 9); the
  four points re-derived as A3 by check K-DKG. Borovyk–Goldberg 2017: only folds and cusps for every mass.
- X-TRI (M03): every degenerate point is A2 or A3; no A≥4 (Ge–Hua–Jia–Zhou 2025, Lemma 4.3).
- X-KING (M18): every point is A1, A2 or A3 (Wan–Zhang, arXiv:2507.20142).
- Graphene (M05, Hong–Tadano–Yang 2026) and the lattice wave equation (M16, Schultz 1998; Bi–Cheng–Hua) are prior art
  for the decay rates; the sweep did not extract a complete point classification from them, so they are not known
  answers here.

K2 note: on `B` the degenerate curve is `X² = 6Y³` (`det H = 24Y³ − 4X²` in (X, Y)); it is a fold curve away from the
origin (`T[v_a,v_a,v_a] = −480τ⁸` on `X = √6 τ³, Y = τ²`). K3 note: its other degenerate line `{x = 2/7}` is a fold line.

## 6. Methods, independence, output schema, budgets

**Implementation A (exact algebra).** Substitute `tᵢ = tan(kᵢ/2)` (`cᵢ = (1 − tᵢ²)/(1 + tᵢ²)`, `sᵢ = 2tᵢ/(1 + tᵢ²)`)
in four charts (`kᵢ` or `kᵢ − π` in `(−π, π)`) so that every point of T² is covered; form the polynomial conditions of
§2 over ℚ by clearing the factors `G′(u)` (nonzero off NS) and the positive denominators `(1 + tᵢ²)`; solve exactly:
the rank-0 set `{p = q = r = 0}`; the systems `{det H = 0, T[v_a, v_a, v_a] = 0, v_a ≠ 0}` and
`{det H = 0, T[v_b, v_b, v_b] = 0, v_b ≠ 0}` (their union with the rank-0 set is `Σ` minus NS); positive-dimensional
components must be detected (e.g. a nonconstant common factor, or a Gröbner basis of positive dimension), not missed.
Real solutions are isolated with certified isolating boxes (rational endpoints); every type decision (`g4 ≠ 0`,
`Disc ≠ 0`, factor structure of C) is exact (exact arithmetic in the algebraic numbers, or an interval evaluation at a
precision where 0 is excluded, falling back to an exact zero test). Allowed tools: an exact Gröbner/real-root solver
(e.g. msolve, Singular, SageMath) and SymPy for forming the conditions; versions pinned in the registration.

**Implementation B (rigorous interval branch and bound in `k`).** Cover T² (and B for K1–K3) by dyadic boxes; evaluate
`det H`, `T[v_a,v_a,v_a]`, `T[v_b,v_b,v_b]`, `|v_a|²`, `|v_b|²`, `g4` and the entries of H with outward-rounded ball or
interval arithmetic whose elementary functions are rigorous (e.g. Arb, MPFI, IntervalArithmetic.jl with correctly
rounded functions), from the closed-form derivatives of §1 (Faà di Bruno) or interval Taylor arithmetic. Box labels:
- EXCLUDED: `0 ∉` enclosure of `det H`, or `0 ∉` enclosure of `T[v_a,v_a,v_a]`, or `0 ∉` enclosure of
  `T[v_b,v_b,v_b]` (then the box contains no point of Σ);
- A3-PROVEN: a Krawczyk test (R. Krawczyk, Computing 4 (1969) 187–201, DOI 10.1007/BF02234767) or an interval
  Newton test proves that `F = (det H, T[v, v, v])`, with `v ∈ {v_a, v_b}` and
  `0 ∉` enclosure of `|v|²` on the box, has exactly one zero in the box, and `0 ∉` enclosure of `g4` there;
- NS-ADJACENT: the box meets the closed ball of radius 2⁻¹⁰ (max norm) around a point of `NS(Ψ)` (§3);
- UNRESOLVED: none of the above at the minimum box width.
Rank-0 points, A≥4 points and non-isolated components cannot be proved by interval tests (they are solutions of
overdetermined systems); B reports them only as UNRESOLVED boxes.

**Independence.** A and B are written by different agents (or people), B from this specification alone without
reading A, and they must not share code for forming derivatives or deciding types. Libraries both depend on
(e.g. GMP, FLINT) are listed as common-mode assumptions in the registration; if both deciding computations rest on the
same library, the registration says so and the "two independent implementations" label is not used for the affected
claims.

**Output schema (JSON, one file per implementation).** Top level: `spec_sha256` (of this file at the frozen commit),
`git_commit`, `dirty` (bool), `versions` (object), `platform` (string), `models` (object keyed by ID), and `complete:
true` written last. Per model: `ns_points` (list of boxes), `points` (list of `{type, box, exact?}` with `type` in
`A3, A4+, D4, D5+, EJ`), `components` (list of `{types, boxes, exact?, samples?}`, `samples` required from A),
`fold_set_empty` (bool), `unresolved` (list of
boxes; B only), `excluded_boxes`, `a3_boxes`, `ns_adjacent_boxes` (B only; dyadic endpoints as exact decimal strings),
`budget_used` (integers), `status` (`DONE` or `BUDGET_EXHAUSTED` with a reason). Boxes are `[[lo1, hi1], [lo2, hi2]]`
with decimal strings, lower ends rounded down and upper ends rounded up.

**Budgets (deterministic, never wall clock).** A: per model, a cap on the total degree of the polynomial systems it may
form (fixed at registration from the development runs) and on solver memory; exceeding it gives `BUDGET_EXHAUSTED`.
B: at most 2²⁴ boxes per model and minimum box width 2⁻⁴⁰; exceeding gives `BUDGET_EXHAUSTED`.

## 7. Reference values (non-rigorous unless stated; for the implementations' first cross-checks)

- `a = arccos(−1/3) ≈ 1.910633236249018556327714`; at `(a, a)` for M08: `cos a = −1/3`, `sin a = 2√2/3` (exact);
  with `v = (1, −1)`, `w = (1, 1)`, which are `∂k/∂u` and `∂k/∂s` in the coordinates `k = (a + s + u, a + s − u)`:
  `H[w, w] = ω_ss = 32/(195√65) ≈ 0.0203544180`, `T[v, v, w] = ω_suu = 12√130/65 ≈ 2.1049392463`,
  `Q[v, v, v, v] = ω_uuuu = 18/√65 ≈ 2.2326252226`, and `g4 = −5247/√65 ≈ −650.810252390` (exact values, check
  K-QWZ3).
- M01 at `(π/2, π/2)`: `H = 0`, `C(κ) = κ₁³ + κ₂³`, `Disc = −27`.
- K1 at r: `g4 = −24576/625` with `v` from the kernel formula (exact, check K1).

## 7a. Prior art and what the census can add

Per-model classifications of every torus point, for this exact problem (the critical points of `Ψ − ∇Ψ(k₀)·k`),
already exist for discrete Klein–Gordon (all masses), the lattice wave equation, the triangular lattice, the King's
graph and graphene (references in the table of §3 and in `docs/prior_art.md`). The logged sweep found no census across
several models and none for the t–t′ model at general t′/t, the 9-point stencil, Yee/FDTD, Qi–Wu–Zhang, gapped graphene
or 2D quantum walks: PLAUSIBLE-not-novel for those (search limits in the sweep: Google Scholar unreachable, Crossref
search largely rate-limited). The census is a decision instrument for OscInt and an exact, two-method re-derivation;
it claims no novelty for the models with published classifications.

**Out of scope of this census (stated so nobody infers coverage):** classification uniformly over parameter intervals
(the t–t′ family over t′/t, the Yee family over S, the arccos family over (a, b)); this needs a parametric method
(e.g. cylindrical algebraic decomposition) and is a candidate follow-up registration.

## 8. Changes before registration
- 2026-11-09 — draft. During the development of `numerics/census/spec_checks.py` (before this file was committed), the
  check script decided "g3 = 0" from one kernel vector on two controls and failed (K1 at τ = 3/4, K3 on `x = 2/7`),
  because that vector was the zero vector there; the rule of §2.3 (both contractions) was written into this
  specification because of it. The script's first run is not committed; its fixed version is.
- 2026-11-09 — after the logged prior-art sweep (before freezing): sources filled in for every model; M18 (King's
  graph) added to the square family as an external known answer; M11 given weight 0 (no verified physical model; the
  repository's `docs/applications.md` attribution of this family to split-step walks is unverified); external known
  answers X-DKG, X-TRI, X-KING added to §5; checks M-GRAPHENE-CN, M-hBN, M-KING, M-FD9-TT, M-YEE-ARCCOS and K-DKG added
  to `numerics/census/spec_checks.py`; §7a added.
