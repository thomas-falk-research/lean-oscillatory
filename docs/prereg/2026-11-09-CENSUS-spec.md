# Specification: singularity census of 2D dispersion relations (CENSUS)

Status: FROZEN 2026-11-10 by the commit that sets this word (recorded in `docs/prereg/LEDGER.md`). Drafted 2026-11-09
(session 8), revised 2026-11-10 after the spec-fidelity referee (findings and what was done
in `review/2026-11-10-CENSUS-spec-answers.md`, in the lead's words, lessons 46; changes in §8). Because that referee
reported a blocker, a second fresh referee checked the repairs (no blocker; its findings are repaired, same answers file,
second part). The file is frozen by a commit before either implementation exists. Changes after freezing
and before registration are listed in §8, and both implementations are re-checked against them; none are allowed after
registration (`docs/prereg/2026-11-09-CENSUS-prereg.md`). An implementer reads only this file and the files it names.

Numerics and computer algebra are tooling, never evidence for a Lean theorem (README). The census decides which
theorems OscInt proves next (`docs/ROADMAP.md`, industry programme I1); a model is "covered by OscInt" only when its
classification is discharged in Lean, which this census does not do.

## 0. Notation and conventions

- `T² = (ℝ/2πℤ)²`, points `k = (k₁, k₂)`, represented in `(−π, π]²`. `cᵢ = cos kᵢ`, `sᵢ = sin kᵢ`.
- For a function Ψ real-analytic near `k₀`: `H = D²Ψ(k₀)` (symmetric 2 × 2, entries `p = H₁₁`, `q = H₁₂`, `r = H₂₂`),
  `T = D³Ψ(k₀)`, `Q = D⁴Ψ(k₀)` (symmetric tensors); `T[a, b, c] = Σ Tᵢⱼₖ aᵢ bⱼ cₖ`, likewise `Q[a, b, c, d]`.
- Kernel convention (as Lean's `latticeKernel`, `OscInt/Statements/Global.lean`): `K(t, x) = ∫ e^{i(tΨ(k) + x·k)} dk`,
  so the stationary points for the observation direction `x/t` are the `k` with `∇Ψ(k) = −x/t`.
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
  Because `g4` depends on the length of `v`, every reported value and every threshold uses the **normalised invariant
  `ĝ4 = g4/|v|⁴`** (Euclidean norm), which is the same for `v_a`, `v_b` and any other nonzero kernel vector. Where a
  fixed choice is needed (B's enclosures), `v = v_a` if `v_a ≠ 0` and `v = v_b` otherwise, and `w = (−v₂, v₁)`.
  `ĝ4` is invariant under rescaling `v` but scales like Ψ (`Ψ ↦ αΨ` gives `ĝ4 ↦ αĝ4`). (At K1,
  `g4` is −24576/625 with `v_a`, −7776/625 with `v_b`, and `ĝ4 = −6`.)
  **A3** (cusp) iff `ĝ4 ≠ 0`; **A≥4** iff `ĝ4 = 0`.

**2.4 Rank 0.** `H = 0`. The binary cubic `C(κ) = T[κ, κ, κ] = a κ₁³ + b κ₁²κ₂ + c κ₁κ₂² + d κ₂³` with
`a = T₁₁₁, b = 3T₁₁₂, c = 3T₁₂₂, d = T₂₂₂` and discriminant
`Disc = b²c² − 4ac³ − 4b³d − 27a²d² + 18abcd`:
- **D4** iff `Disc ≠ 0` (three distinct linear factors over ℂ);
- **D≥5** iff `C ≠ 0` has exactly two distinct linear factors (a double factor) — the 3-jet class of the series
  D_k, k ≥ 5 (and of non-isolated D∞ points);
- **E/J** iff `C ≠ 0` is the cube of a linear form — the 3-jet class of E6, E7, E8, J10 and the deeper E and J series;
- **X** iff `C = 0` (`H = 0` and `T = 0`) — the zero 3-jet: X9 and every deeper class with zero 3-jet.
`C` (nonzero) is a cube iff its Hessian covariant vanishes: `b² − 3ac = bc − 9ad = c² − 3bd = 0`.
These are 3-jet classes; the census does not determine k in D_k or the subclass of E/J or X. `Disc` is homogeneous of
degree 4 in `(a, b, c, d)`; thresholds use the scale-free `D̂ = Disc / max(|a|, |b|, |c|, |d|)⁴`.

**2.5 Isolated and non-isolated.** Let `Σ(Ψ)` be the set of points of `T² ∖ NS(Ψ)` of type A3, A≥4, D4, D≥5, E/J or X,
i.e. the common zeros off NS of `det H`, `T[v_a, v_a, v_a]` and `T[v_b, v_b, v_b]` (at rank 0 both kernel vectors
vanish). In the half-angle coordinates of §6 it is a semi-algebraic set, so it has finitely many connected components,
each a point, a curve or a two-dimensional set; it is reported that way. A point of `Σ(Ψ)` on a
component of positive dimension has type **NI** in addition to its pointwise type. NI says only that the point lies on
a positive-dimensional component of Σ; it does not say that `k₀` is a non-isolated critical point of `φ_{k₀}` (each
point of K3's A3 segment is an isolated critical point). On a component of dimension 1 the type is constant on each
open arc between finitely many **special points**: crossings, ends, and the points where the type changes. Only points
of Σ count, and only ends inside the domain: an end on the boundary of the box B (controls K1–K3) is not a special
point, and a curve of Σ running into NS has no end there (its limit point is in NS, not in Σ, and is reported with
NS). A component may have no special points (a closed curve of constant type). The component is reported with the
types that occur on it, its special points with their types, and sample points with their types (§4.1). A component of dimension 2 is reported with the types that occur on it.

**2.6 Flat bands.** A band that is constant on `T²` is reported as FLAT and not classified. (The corpus records
single dispersive bands; M10's flat bands ±1 are named in its record and not classified.)

## 3. Corpus (fixed now)

Every phase below is admissible (§1). Where the table names a check, the formula and the non-smooth set are
machine-checked from the physical definition by `numerics/census/spec_checks.py`; M03, M04 and M16 have no such check
(their formulas are the cited symbols as printed), and the NS sets of M10 and M16 are derived by hand below the table.
**The authoritative input is `numerics/census/corpus.json`** (one record per model and control: `G`, and `u` as a
polynomial with rational coefficients in `c₁, s₁, c₂, s₂`, or in `x, y` on the box); check CORPUS proves that every
record equals the formula in this file identically. Implementations read that file and never transcribe this table;
each computes `NS(Ψ) = {u ∉ J}` itself. Two-band models are classified
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
| M07 | QWZ (T) | `√(3 + 2(c₁ + c₂) + 2c₁c₂)` (m = 1) | ∅ (P ≥ 1) | M-QWZ, G-QWZ1 | Asbóth–Oroszlány–Pályi 2016, eq. (6.1) [CR]; original model Qi–Wu–Zhang 2006 [CR][arX] (same `\|d\|` up to a scale and a k-independent term, see the sweep) |
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
only; all on 2026-11-09 in the logged prior-art sweep. Full references are in `docs/prior_art.md` ("Singularities of
lattice dispersion relations"); the sweep report was removed from the tree on 2026-11-10 (lessons 46) and is readable
with `git show 58a86d0:review/2026-11-09-CENSUS-prior-art-sweep.md`.

**Held-out set H (sealed; added 2026-11-10, before registration).** The corpus above was chosen by the project. To
test whether a ranking computed on it generalises, a set H of 5 further models is fixed before the run, and used
only after the corpus results are committed.
- *Who chooses (owner decision 2026-11-10): the lead.* This is weaker than an outside selector: the lead knows the
  registration's expected ranking (§1 there) and could, even unintentionally, pick models that confirm it. Three
  mitigations, fixed now:
  1. *A pool, not a choice.* Before any implementation exists, the lead assembles a pool of at least 12 models by the
     inclusion rule below, which is fixed in this file before the pool is assembled. The pool is sealed (below), and
     its commitment is entered in the registration.
  2. *A draw nobody chooses.* H is the 5 models drawn from the pool by the deterministic procedure below, seeded with
     one round of drand's default mainnet chain (chain hash
     `8990e7a9aaed2ffed73dbd7092123d6f289930540d7651336225dc172e51b2ce`, 30-second rounds). The registration names the
     round number. The registration commit is stamped (RFC 3161 and OpenTimestamps, as `make stamp` does), and the round's
     time must be at least 48 hours after the RFC 3161 time of that stamp; otherwise H is void. At the reveal, the round's signature is verified against the chain's public key, and its
     randomness is recomputed as SHA-256 of the signature.
  3. *Custody.* The salt, the pool and H are handed to the owner, not kept in the repository or in a session
     container. Implementers never see the pool or H before the reveal.
- *Inclusion rule (fixed now, before the pool is assembled).*
  1. Sources: peer-reviewed papers or arXiv preprints, whose text the selector has read, that print the dispersion
     relation of a two-dimensional model in one of the five domains.
  2. Parameters: the first numerical values the source gives for that relation's parameters, in the order they appear
     (body text, tables and captions alike), as exact rationals; where it gives none, every free parameter is 1, then
     1/2 if that makes the phase constant or inadmissible; if both fail, the source contributes no model. Coordinates:
     for a lattice with primitive vectors a₁, a₂, the phase is written in `kᵢ = k·aᵢ` (2π-periodic in each); a relation
     that cannot be written so with rational coefficients is not admissible. Band: the highest dispersive band (for a
     ± pair, the + band), as in the corpus. Domain: W if it is a discrete-time quantum walk; else N if it is the symbol
     of a numerical scheme; else T if the source calls the model topological; else P if it is a phonon, lattice-wave or
     Klein–Gordon relation; else L.
  3. The phase so obtained must be admissible (§1) and not constant. Excluded: corpus models, controls, and images of
     either under `k ↦ Ak + b` (A ∈ GL₂(ℤ), b ∈ T²) combined with `Ψ ↦ αΨ + β` (α ≠ 0); of two pool candidates
     related this way, only the first found enters.
  4. Quota: at most one model per source and at most three per domain, taken in the order the sources are examined.
     The selector stops when every domain has three or after 60 sources have been examined, whichever is first. If the
     pool has fewer than 12 models or covers fewer than four domains, the held-out step is abandoned and reported as
     such in the registration.
  5. Record: each pool entry gives the source (DOI or arXiv identifier, equation number) and the parameter values;
     the sealed record also lists every examined source with the rule that excluded it. The search queries are not
     recorded (lessons 46). The order in which sources are examined remains the selector's choice; the sealed pool and
     the random draw are what limit it.
- *Pool format.* A JSON array, sorted by `id` (unique), of objects `{id, domain, source, parameters, G, u,
  domain_type}`, all values strings (rationals written `p/q`, so that RFC 8785 never rounds a number), with `G`, `u`
  and `domain_type` in the grammar of `numerics/census/corpus.json`. Every entry is checked against that grammar and
  against admissibility by `numerics/census/validate_pool.py`, committed before the pool is sealed, so that no entry
  can fail to parse later.
- *Draw procedure (fixed now).*
  1. For each pool entry, its key is `SHA-256(R ‖ 0x00 ‖ UTF-8(id))`, where `R` is the 32 raw bytes of the round's
     randomness (hex-decoded) and `‖` is byte concatenation. The original rank of an entry is its position when the
     pool is sorted by key, compared as 32-byte big-endian integers, ascending; equal keys are ordered by `id`.
  2. H is the 5 entries of original rank 1 to 5.
  3. While H covers fewer than three domains: among H's members whose domain has at least two members in H, remove the
     one with the largest original rank; add the pool entry with the smallest original rank whose domain H lacks.
- *Sealing.* The selector publishes only `SHA-256(salt ‖ JCS(pool))`, where `JCS` is the JSON Canonicalization Scheme
  (RFC 8785) as UTF-8 bytes and `salt` is 16 bytes from the operating system's cryptographic random source (published
  later as hex). That hash is entered in the registration before it is registered. H itself is not committed: it does not
  exist until the drand round, and it is a fixed function of the pool, the round and the draw procedure. Implementers
  never see the pool or H before the reveal.
- *Reveal.* After step 6 of the registered run is committed, the owner publishes the salt and the pool from the
  custody copy (not the selector), and H is recomputed from the verified drand round. A pool hash mismatch, or an
  unverifiable round, voids H; a voided H is a reported outcome (registration C7, "voided", with its cause), never
  an omitted one.
- *Run.* H is classified by the registered code, unchanged, from a clean checkout of the registered commit; the pool
  and H stay outside the tree, and the SHA-256 of their files is recorded with the result. A model of H that the
  implementations reject anyway is reported as a selector error and dropped from H; the C7 check (registration §3)
  needs at least 3 models of H.

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

**4.1 Per model (and per control).** Whether the phase is FLAT (§2.6). The set `NS(Ψ)`, computed by the implementation
from `u` and `J`: its isolated points and its components of positive dimension. The set `Σ(Ψ)` (§2.5), with, for every
isolated point: its type, an
exact description where the method gives one (implementation A: the chart, a defining polynomial system over ℚ and a
rational isolating box in the half-angle coordinates that can be refined on request), and an enclosure (a box in `k`,
outward-rounded decimal endpoints, width ≤ 1e−12 in each coordinate); for every non-isolated component: an exact
description (A: defining polynomials; for a component of dimension 1 its special points (§2.5) and at least 16 sample
points spread along it, each with its type and given like an isolated point) or covering boxes (B), and the types on
it; whether `{det H = 0} ∖ (NS ∪ Σ)` (the fold set) is
empty.

**4.2 Coverage predicate.** A model is **GD-covered** if `Σ(Ψ)` consists of finitely many D4 points and `NS(Ψ) = ∅`
(the hypothesis of OscInt's global theorem GD and its vector version; every other point is then A1 or A2; GD-F, GD-C
and GD-N have further hypotheses, so for them the predicate is necessary, not sufficient). Extension families: **F-A3**
(finitely many A3 points allowed), **F-A4** (finitely many A≥4 points), **F-D5** (finitely many D≥5 points), **F-E**
(finitely many E/J points), **F-X** (finitely many X points), **F-NI** (positive-dimensional components allowed), **F-NS**
(a nonempty finite NS set allowed). A model is covered by GD ∪ S, for a set S of families, if every object it has
outside GD's hypothesis belongs to a family in S. Objects are counted this way: every point on a positive-dimensional
component of Σ, special points included, is covered by F-NI alone; F-A3, F-A4, F-D5, F-E and F-X count only isolated
points of Σ; F-NS counts NS. (So M07, if its only Σ is the component of §7, is covered by GD ∪ {F-NI}.) This is a necessary condition for a decay theorem of the GD form, not
a sufficient one (uniformity in the linear term, amplitude conditions and global assembly are separate theorems).

**4.3 Unlock score.** For a family F: `N(F)` = the total weight (§3) of the corpus models covered by GD ∪ {F} and not
by GD; `D(F)` = the number of domains (L, T, W, N, P) with at least one such model. Also reported for every pair
{F, F′}. The ranking rule that uses these numbers is fixed in the registration (§4 there), not here.

## 5. Controls and known answers (expected outcomes fixed now)

All exact; checks in `numerics/census/spec_checks.py`. Controls K1–K3 are polynomial phases on the box
`B = [−1, 1]²` (not on T²); the census treats them with the same definitions (§2) and reports every point of `B`.

| ID | Phase | Expected (exact) | Check |
|---|---|---|---|
| K-SQ | M01 | `Σ` = the four D4 points `(±π/2, ±π/2)`; no A3, A≥4, D≥5, E/J, X, NI; fold set nonempty | K-SQ |
| K-QWZ3 | M08 | `Σ` contains the four A3 points `(±a, ±a)`, `a = arccos(−1/3)` (more points may exist; the census decides) | K-QWZ3 |
| K-QWZm | `√(m² + 2 + 2m(c₁ + c₂) + 2c₁c₂)` for each m ∈ {201/100, 5/2, 4, 10} (control, weight 0, not in the corpus; IDs `K-QWZm[201/100]`, `K-QWZm[5/2]`, `K-QWZm[4]`, `K-QWZm[10]`) | at each m, `Σ` contains the four A3 points `(±a_m, ±a_m)`, `a_m = arccos(−1/m)`, all stable (`T[v, v, w] ≠ 0`), with `ĝ4` as in §7 (more points may exist; the census decides, and this control asserts nothing about them) | K-QWZm |
| K1 | `X²Y + Y²`, `(X, Y) = R((x, y) − r)`, `R = [[3/5, −4/5], [4/5, 3/5]]`, `r = (1/7, −2/9)`, on B | `Σ ∩ B = {r}`, type A3; no rank-0 point | K1 |
| K2 | `X²Y + Y⁴`, `(X, Y) = (x, y) − (−1/5, 1/3)`, on B | `Σ ∩ B = {(−1/5, 1/3)}`, type D≥5 | K2 |
| K3 | `X³ + Y⁴`, `(X, Y) = (x, y) − (2/7, −1/11)`, on B | `Σ ∩ B` is one component, the segment `{y = −1/11} ∩ B` (dimension 1, NI), of type A3 except one special point, `(2/7, −1/11)`, of type E/J; no isolated point | K3 |
| K5 | `√((c₁ + c₂)² + 1/4)` on T² (separable trap) | `Σ` is one component, the union of the lines `k₁ + k₂ = π` and `k₁ − k₂ = π` (mod 2π) (dimension 1, NI), of type A≥4 except two special points, the crossings `(0, π)` and `(π, 0)`, of type X; no isolated point | K5 |

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
The denominators of the `ρₘ` of §1 (powers of `u`, `1 − u²` or `u(1 − u)`, nonzero on `J`) are cleared in the same
way. Real solutions are isolated with certified isolating boxes (rational endpoints); a point found in more than one
chart is reported once (the charts overlap). Every type decision (`ĝ4 ≠ 0`,
`Disc ≠ 0`, factor structure of C) is exact (exact arithmetic in the algebraic numbers, or an interval evaluation at a
precision where 0 is excluded, falling back to an exact zero test). Allowed tools: an exact Gröbner/real-root solver
(e.g. msolve, Singular, SageMath) and SymPy for forming the conditions; versions pinned in the registration.

**Implementation B (rigorous interval branch and bound in `k`).** Evaluate `u`, `det H`, `T[v_a,v_a,v_a]`,
`T[v_b,v_b,v_b]`, `|v_a|²`, `|v_b|²`, `ĝ4` and the entries of H with outward-rounded ball or interval arithmetic whose
elementary functions are rigorous (e.g. Arb, MPFI, IntervalArithmetic.jl with correctly rounded functions), from the
closed-form derivatives of §1 (Faà di Bruno) or interval Taylor arithmetic. The root box is the dyadic square
`[−4, 4]²` for phases on T² (it contains a fundamental domain; a point of T² may lie in several boxes, which is
harmless) and `[−1, 1]²` for K1–K3. Boxes are processed breadth-first (a first-in, first-out queue; a box is split into
four equal children, queued in the order (lower `k₁`, lower `k₂`), (upper `k₁`, lower `k₂`), (lower `k₁`, upper `k₂`),
(upper `k₁`, upper `k₂`)). A box is processed when it is taken from the queue and tested, whether it is then labelled
or split; the budget counts processed boxes. Each box gets the first label whose test it
passes, in this order:
1. NS: the enclosure of `u` on the box is disjoint from `J` (every point of the box is in NS);
2. NS-ADJACENT: the enclosure of `u` is not contained in `J`, and the box has width at most 2⁻¹² (a wider box with this
   property is split, not labelled);
3. EXCLUDED: the enclosure of `u` lies in `J`, and `0 ∉` enclosure of `det H`, or `0 ∉` enclosure of
   `T[v_a,v_a,v_a]`, or `0 ∉` enclosure of `T[v_b,v_b,v_b]` (then the box contains no point of Σ);
4. A3-PROVEN: the enclosure of `u` lies in `J`; a Krawczyk test (R. Krawczyk, Computing 4 (1969) 187–201,
   DOI 10.1007/BF02234767) or an interval Newton test proves that `F = (det H, T[v, v, v])`, with `v ∈ {v_a, v_b}` and
   `0 ∉` enclosure of `|v|²` on the box, has exactly one zero in the box; and `0 ∉` enclosure of `ĝ4` there;
5. otherwise the box is split if its width exceeds 2⁻⁴⁰, and labelled UNRESOLVED if not.
When the budget is reached, every box still in the queue is labelled UNRESOLVED and the status is `BUDGET_EXHAUSTED`.
The labelled boxes therefore always cover the root box exactly. Rank-0 points, A≥4 points and positive-dimensional
components cannot be proved by interval tests (they are solutions of overdetermined systems); B reports them only as
UNRESOLVED boxes, and a model with a component of Σ will normally exhaust B's budget. The two-implementation statement
(registration §4) is made outside the union of B's NS, NS-ADJACENT and UNRESOLVED boxes, not outside a fixed
neighbourhood of NS.
- *Enclosure interface.* B provides `numerics/census/impl_b/enclose.py MODEL_ID BOX`, which prints as JSON the
  enclosures of `u`, `det H`, `T[v_a,v_a,v_a]`, `T[v_b,v_b,v_b]`, `|v_a|²`, `|v_b|²` and `ĝ4` on `BOX` (decimal-string
  endpoints, rounded outward), computed by the same code that labels boxes; `ĝ4` with the fixed `v` and `w` of §2.3,
  as the function `Q[v⁴]/|v|⁴ − 3 T[v,v,w]²/(|v|⁴ H[w,w])` (defined where its denominators are nonzero). The spec-only evaluator uses it for
  registration C5(b).

**Independence.** A and B are written by different agents (or people), B from this specification alone without
reading A, and they must not share code for forming derivatives or deciding types. Libraries both depend on
(e.g. GMP, FLINT) are listed as common-mode assumptions in the registration; if both deciding computations rest on the
same library, the registration says so and the "two independent implementations" label is not used for the affected
claims.

**Output schema (JSON, one file per implementation).** Top level: `spec_sha256` (of this file at the registered
commit), `git_commit`, `dirty` (bool), `versions` (object), `platform` (string), `models` (object keyed by the IDs of
`numerics/census/corpus.json`), and `complete: true` written last. Per model: `flat` (bool); `ns_points` (list of
`{box, exact}`); `ns_components` (list of `{dim, boxes, exact, samples}`, `samples` at least 16 exact points from A); `points` (list of `{type, box, exact}` with `type`
in `A3, A4+, D4, D5+, EJ, X`); `components` (list of `{dim, types, special_points, samples, boxes, exact}`, where
`special_points` and `samples` are lists of `{type, box, exact}`); `fold_set_empty` (bool); B only: `ns_boxes`,
`ns_adjacent_boxes`, `excluded_boxes`, `a3_boxes`, `unresolved` (lists of boxes, dyadic endpoints as exact decimal
strings); `budget_used` (integers); `status` (`DONE` or `BUDGET_EXHAUSTED` with a reason). `exact` is required from A
and absent from B; A's components carry `special_points` (possibly empty) and at least 16 `samples`. Fields that
interval branch and bound cannot decide are `null` in B's output: `flat`, `ns_points`, `ns_components`, `points`,
`components` and `fold_set_empty` (B's evidence is its labelled boxes). B's box lists are long (up to about 2²⁴ per
model); the file may be stored gzip-compressed as `b.json.gz`. Boxes are `[[lo1, hi1], [lo2, hi2]]` with decimal strings, lower ends rounded down and upper
ends rounded up.

**Budgets (deterministic, never wall clock).** A: per model, a cap on the total degree of the polynomial systems it may
form (fixed at registration from the development runs) and on solver memory; exceeding it gives `BUDGET_EXHAUSTED`.
B: at most 2²⁴ boxes processed per model and minimum box width 2⁻⁴⁰; reaching the box cap gives `BUDGET_EXHAUSTED`, with
the unprocessed boxes labelled UNRESOLVED (above).

## 7. Reference values (non-rigorous unless stated; for the implementations' first cross-checks)

- `a = arccos(−1/3) ≈ 1.910633236249018556327714`; at `(a, a)` for M08: `cos a = −1/3`, `sin a = 2√2/3` (exact);
  with `v = (1, −1)`, `w = (1, 1)`, which are `∂k/∂u` and `∂k/∂s` in the coordinates `k = (a + s + u, a + s − u)`:
  `H[w, w] = ω_ss = 32/(195√65) ≈ 0.0203544180`, `T[v, v, w] = ω_suu = 12√130/65 ≈ 2.1049392463`,
  `Q[v, v, v, v] = ω_uuuu = 18/√65 ≈ 2.2326252226`, and `g4 = −5247/√65 ≈ −650.810252390`; since `|v|⁴ = 4`,
  **`ĝ4 = −5247/(4√65) ≈ −162.702563097`** (exact values, check K-QWZ3).
- K-QWZm, every m > 2 (exact, symbolic m: `numerics/review/dossier_checks.py` X1; at the four masses: check K-QWZm):
  `D = m⁴ − 2m² + 2`; at `(a_m, a_m)` with `v = (1, −1)`, `w = (1, 1)`: `H[w, w] = 4(m² − 1)/(m D^{3/2})`,
  `T[v, v, w] = 2m√(m² − 1)/√D`, `Q[v, v, v, v] = 6m/√D`, `g4 = −3m(m⁶ − 2m⁴ + 2m² − 2)/√D < 0` (`m⁶ − 2m⁴ + 2m² − 2 > 0`
  for m > 2), so **`ĝ4 = −3m(m⁶ − 2m⁴ + 2m² − 2)/(4√D)`**, and `∇Ψ = −v_m(1, 1)`, `v_m = (m² − 1)^{3/2}/(m√D) ∈ (0, 1)`. By evenness, `∇Ψ(±a_m, ±a_m) = (∓v_m, ∓v_m)`.
  In this specification's convention (§2: observation direction `x/t = −∇Ψ(k₀)`) the cusp rays are therefore
  `x/t = (±v_m, ±v_m)`, with the same signs as the point. The dossier's convention (`e^{i(x·k − tω)}`, `x/t = ∇ω`)
  has the opposite sign; an implementation compares against the convention of §2. Decimals (not rigorous; check
  K-QWZm output): `g4 ≈ −74.198, −247.71, −2884.8, −297014.5`, `ĝ4 ≈ −18.549458, −61.927895, −721.19911, −74253.636` and `v_m ≈ 0.82402, 0.90033, 0.96610, 0.99494` for
  m = 201/100, 5/2, 4, 10. At m = 201/100, `a_m ≈ 2.09153` lies within 3e−3 of 2π/3 and `H[w, w] ≈ 0.18457`.
- M01 at `(π/2, π/2)`: `H = 0`, `C(κ) = κ₁³ + κ₂³`, `Disc = D̂ = −27`.
- K1 at r: `g4 = −24576/625` with `v = v_a`, and `ĝ4 = −6` (exact, check K1).
- M07 (QWZ m = 1; informational, check M07-LINES): `u = 1 + 2(1 + c₁)(1 + c₂)`, so `Ψ ≡ 1` on the lines `k₁ = π`
  and `k₂ = π`. On `k₁ = π`, `k₂ ≠ π`: `H = diag(1 + c₂, 0)`, `T[v, v, v] = 0` and `ĝ4 = 0` (type A≥4); at `(π, π)`:
  `H = 0`, `T = 0` (type X). The two lines therefore lie in one component of Σ, of type A≥4 + NI, with `(π, π)` of type X. The second spec
  referee's exact elimination (not committed; disclosed in the registration's §1) found no other point of Σ for M07;
  the census decides.

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
- 2026-11-10 — before registration, owner decision (after the external dossier, A1, and its
  answers file): control K-QWZm added to §5 (the QWZ family at m ∈ {201/100, 5/2, 4, 10}, four stable A3 points each,
  closed-form `g4`), its reference values to §7, and check K-QWZm to `numerics/census/spec_checks.py`. Nothing had been
  run under the registration; no implementation exists. The control asserts only the four points per mass, not that
  they are the only degenerate points.
- 2026-11-10 — before registration, owner decision (after the external audit, `review/2026-11-10-external-audit-answers.md`,
  memo Gate 3): the sealed held-out set H added to §3. The corpus, the controls and every definition are unchanged.
- 2026-11-10 — before registration, owner decision: the lead selects the held-out set H, with the three
  mitigations of §3 (sealed pool, drand-seeded draw, owner custody). The weaker independence is disclosed there.
- 2026-11-10 — after the spec-fidelity referee (answers `review/2026-11-10-CENSUS-spec-answers.md`), before freezing:
  - §6 B: box labels tested in a fixed order, NS and NS-ADJACENT first; NS-ADJACENT only for boxes of width ≤ 2⁻¹²;
    EXCLUDED and A3-PROVEN only where the enclosure of `u` lies in `J`; root box `[−4, 4]²` on T²; breadth-first
    processing, and unprocessed boxes UNRESOLVED when the budget is reached; an enclosure interface for the evaluator.
  - §2.3, §7: the normalised invariant `ĝ4 = g4/|v|⁴` replaces `g4` in every value and threshold (`g4` depends on the
    length of `v`). §2.4: the scale-free `D̂`; the old class E/J split into E/J (triple factor) and X (zero cubic).
  - §2.5: NI defined; special points of one-dimensional components. §5: K3 and K5 stated as components with special
    points (K3's E/J point lies on its segment, so it is E/J + NI; K5's crossings are X). K-QWZm IDs fixed.
  - §3: `numerics/census/corpus.json` made the authoritative input (check CORPUS); NS computed by each
    implementation; the inclusion rule, chain, byte encoding, canonical JSON (RFC 8785), stamp requirement and
    original-rank rule of the held-out draw fixed; H has 5 models. The sweep reference points into history.
  - §0 kernel convention as a formula; §4.1 and §6 schema: `flat`, `ns_components`, `special_points`, typed `samples`,
    `exact` required from A, `ns_boxes`; `spec_sha256` of the registered commit; A merges points found in two charts
    and clears the denominators of the `ρₘ`.
  - §7: `ĝ4` values for M08, K-QWZm and K1; the M07 lines (check M07-LINES). `numerics/census/spec_checks.py`: the
    binary-cubic classifier fixed for cubics with roots at both 0 and infinity (no earlier check was affected; check
    R4), checks CORPUS and M07-LINES added. No implementation exists; nothing has been run under the registration.
- 2026-11-10 — after the second spec referee (no blocker; answers, second part, in the same file), before freezing:
  special points and A's NS objects added to the cross-checks (registration C3, C5); "ends" defined (not on ∂B, none
  at NS); B's undecidable fields `null`; coverage of components fixed (F-NI alone); `ĝ4`'s scaling stated and the C5(a)
  threshold made relative; C5(a) checks every type; lifts in C3(c); the held-out inclusion rule made mechanical (60
  sources, parameters, coordinates, band, domain order, `validate_pool.py`), pool values as strings, the owner reveals,
  a voided H is reported, the 48-hour rule tied to the stamp; B's child order, "processed", fixed `v` and `w`,
  compressed output; K-SQ lists X; the M07 component wording; CORPUS checks every field.
