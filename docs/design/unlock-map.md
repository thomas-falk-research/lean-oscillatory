<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

# The unlock map (session 13, 2026-11-16)

> **Status on 2026-11-19 (this box was added then; the text below it is the record of 2026-11-16 and is not edited).**
> Since the map was written, five batches that it names or leads to were frozen and proved: 21 statements, none of
> them in release v0.6.0. The status of each is in `docs/STATUS.md`.
> - Section 7, item 2, with node N1: batch PA (PA-C, PA-T, LC-1).
> - Section 7, item 3: batch KL (KL-D, KL-C, KL-F). The prior-art check P1 of section 5 is answered in
>   `docs/prior_art.md` (batch KL).
> - Section 7, item 6, nodes N2 and N3: batch FR (FR-K, FR-U, FR-S, FR-P; FC-K, FC-U, FC-P).
> - Section 5, row O1: batch VC2 (VC2-S, VC2-A, VC2-N, VC2-K). The first-derivative test with its sharp constant 2
>   (section 7, item 7) is not stated.
> - Section 4, row F1, and the Hadamard-walk row of section 3.2: batch HW (HW-R, HW-K, HW-D, HW-L).
> - Section 7, item 4, in experimental and unpublished form: `docs/contract/certificate-v0.md`,
>   `python/oscint_cert/`, `rust/oscint-cert/`. Item 5: the protocol `docs/prereg/2026-11-16-CTQW-chain.md` is
>   registered and has not been run.
>
> So the following parts of the text below no longer describe the repository: the count 65 in the heading of
> section 1.1 (now 86); fact 2 under that table (no statement about a ring or a chain); "none exists" in section 1.3
> for N1, N2 and N3; "no certificate schema yet" and the list of missing engineering nodes in section 1.2; the rung
> L3 of chains K7 to K10 in section 2.2; "no proof assistant has it" in section 2.2 and row F5 (PA-T is proved here;
> what the prior-art sweep found is in `docs/prior_art.md`); "(not done)" in row F1; "being checked" and "not
> searched yet" for P1; the two ASSUMED(L4, N3) marks in section 6; the counts in rows E5 and E6.
> Still open from section 7: item 1 (the owner's part), item 5 (the run), the sharp constant of item 7 for k = 1,
> and items 8, 9 and 10.

A graph from what OscInt can do to who could use it, ranked by value per unit of effort. It is written section by
section and committed as each section is finished; a section that says "pending" has not been written yet.

**Reading rules.**
- Evidence labels: PROVEN (machine-checked here, or a derivation short enough to be checked line by line and marked
  "on paper"), VALIDATED (tested, with the method named), CONJECTURED, FOLKLORE, PLAUSIBLE.
- Source labels: CITED-READ (opened and read in this session, full text or abstract as stated), STANDARD-TEXT (a
  textbook cited by section, from memory), SECONDARY (a third-party page).
- Verification ladder: L0 typed code, L1 property tests, L2 certified (interval or exact) computation, L3 deductive
  proof on paper, L4 machine-checked proof, L5 hardware. Each gap is marked ASSUMED(rung needed, reason, owner).
- A domain entry counts in the ranking only with a concrete quantity a practitioner computes and a source that was
  read or a standard text cited by section. Other entries are PLAUSIBLE and stay out of the ranking.
- Nothing in this file is a status claim. The status of every statement is in `docs/STATUS.md`.
- Every agent that searched or reviewed for this file is an instance of the same model family as the lead.

## 1. Nodes: what exists

### 1.1 Machine-checked statements (65, all at L4; `stamps/statements.json`)

| Group | Statements | What a user gets | Explicit constant? |
|---|---|---|---|
| G1 one variable | S1.1–S1.3, S1.k | `\|∫_a^b e^{iφ}ψ\| ≤ c_k μ^{−1/k}(\|ψ(b)\| + ∫\|ψ′\|)` when `\|φ^{(k)}\| ≥ μ`; for k ≥ 2 uniform in an added linear term | yes: 3, 8, 18, `5·2^{k−1} − 2` |
| G2 two variables, local | S2.1, S2.2, S3, S4.1, S4.1′, S5.1, S5.1′ | decay `m^{−N}`, `m^{−1}`, `m^{−5/6}`, `t^{−2/3}`, `t^{−3/4}` at non-stationary, nondegenerate, fold, D4 and A3 points, uniform in the linear term | no (existential) |
| G3 D4 asymptotics | S4.2, S4.3, S4.4, F2, S4.2U, S4.2O | `t^{2/3}∫e^{itφ}A → c_C A(0)` with `c_C = Γ(1/3)²/(√3\|Disc\|^{1/6})` or `Γ(1/3)²/Disc^{1/6}`, uniformly over compact amplitude families and bounded offsets | the limit constant is exact; no rate of convergence |
| G4 front ends and conversions | F1, C1–C10, C7′, FE-… (22 statements) | the same theorems in Mathlib idioms, for one phase or a compact family, smooth only near the support | no |
| G5 global decay | GD-C, GD, GD-F, GD-N, SH, T1 and the four vector-valued forms | a local classification of every point of the support gives a global bound, for all linear terms; sharpness from a nonzero limit; torus unfolding | no |
| G6 lattice kernels | T0E, T0E′, T6, T6L, T6F, T6E, T6E′, TdF, TdE′ | `\|∫_{−π}^{π} e^{i(t cos k + ξk)}dk\| ≤ (8(1+√7)/3) t^{−1/3}` for every real ξ and t > 0; products in every dimension | yes: `C* = 8(1+√7)/3 ≈ 9.72`, within a factor 1.97 of the best |
| G7 lattice Schrödinger group | LS-E, LS-K, LS-D, LS-D′ | on ℓ²(ℤ^d): solutions exist, every solution is the kernel convolution, and `‖u(t)‖_∞ ≤ min{1, (C*/2π)^d (2\|t\|)^{−d/3}}‖f‖₁` | yes: `C*/2π ≈ 1.5473` |

Three facts about this list decide most of what follows.
1. **Only G1, G6 and G7 carry explicit constants.** Everything two-dimensional beyond the separable lattice is
   existential, so it can certify a rate but cannot be evaluated for a device. PROVEN (read from the statements).
2. **G7 is a statement about an infinite lattice.** Every device is finite. No statement in the list says anything
   about a ring or a chain of N sites. PROVEN (read from `OscInt/Statements/LatticeGroup.lean`).
3. **S1.k is uniform in the linear term.** That is exactly the supremum over the site index in a dispersive
   estimate, so one theorem already covers every one-dimensional dispersion relation whose derivatives can be bounded
   below piecewise (chain K1 below). PROVEN (read from `OscInt/Statements/Cusp.lean`).

### 1.2 Engineering capabilities

| Node | What it is | State |
|---|---|---|
| E1 trust chain | guard, axiom audit, statement commitments, comparator against frozen challenges, six-kernel replay, RFC 3161 and OpenTimestamps stamps (`tools/src/bin/`, `make verify-all`) | working; a full replay takes about three hours on four cores |
| E2 downstream checker | `tools/oscint_check.py`: checks that a consumer got the reviewed statements | working; detects drift, not tampering |
| E3 machine-readable index | `docs/api.json` (format `oscint-api/1`), generated from the statement list | working; no certificate schema yet |
| E4 numerics crate | `numerics/` (Rust, no dependencies): floating-point classifiers and quadrature used for pre-registered checks | tooling only; no interval arithmetic, no JSON output |
| E5 consumer examples | 14 files under `examples/consumer/` compiled by `make quick` | working |
| E6 pre-registration ledger | `docs/prereg/LEDGER.md`, six registrations, failures kept | working |
| E7 review process | blind statement review, route referee, post-proof and adversarial reviews, referee calibration (`docs/calibration.md`) | working; every reviewer is an AI of one model family |

Missing engineering nodes, each proposed in section 8: a certified evaluator (L2) for the quantities the statements
bound; a certificate format and a checker that alone may say CERTIFIED; a command-line tool, a Python package and a
Rust crate behind one contract; hypothesis checkers that return PASS, FAIL or UNRESOLVED.

### 1.3 Proposed nodes (none exists; each is argued in sections 2 and 8)

| Node | One-line content | Kind | New as mathematics? |
|---|---|---|---|
| N1 light cone | `\|∫_{−π}^{π} e^{i(t cos k + nk)}dk\| ≤ 2π e^{\|t\| sinh η − \|n\|η}` for every integer n, real t and η ≥ 0 (a contour shift over one period) | statement batch | classical (Kapteyn-type bound for Bessel functions); machine-checked form not found yet (sweep pending) |
| N2 periodisation | the Schrödinger group on a ring of N sites is the lattice group summed over the cosets of Nℤ, with the remainder bounded by N1 | statement batch | classical (aliasing, method of images) |
| N3 reflection | the group on an open chain of M identical sites is the odd part of the ring of 2(M+1) sites | statement batch | classical |
| N4 ballistic identity | for a single-site datum on ℤ, `Σ n²\|u(t,n)\|² = 2t²` exactly | statement batch | classical (Parseval) |
| N5 partition bound | S1.k summed over a partition: a certified decay bound for any one-dimensional dispersion relation from finitely many derivative lower bounds | statement batch (small) | corollary of S1.k |
| N6 sharp lattice constant | `sup_{n∈ℤ, t>0} t^{1/3}\|J_n(t)\| = 0.7857…` (Landau 2000), machine-checked | open formalisation | proved informally; multi-session |
| N7 general hopping | LS-E, LS-K for any finite-range translation-invariant Hamiltonian on ℤ^d | statement batch (large) | classical |
| N8 certified evaluator | exact-rational and ball-arithmetic enclosures of the kernels, the constants and finite-device propagators | tool (L2) | not mathematics |
| N9 contract and checker | certificate schema plus the one checker that may say CERTIFIED | tool | not mathematics |
| N10 quantum-walk protocol | a pre-registered test of the lattice group on a chain or ring of qubits | experiment | the physics is known; the trust chain is new |
| N11 waveguide protocol | the same for a coupled waveguide array, for a partner laboratory | experiment | as N10 |

## 2. Edges and chains

An edge reads "A unlocks B, by this mechanism". A chain is a sequence of existing results that, assembled, gives
something that is not in the repository or, as far as the sweeps of section 3 found, anywhere in machine-checked
form. Every chain below was checked, not assumed: the column "Check" names the reading of the frozen Lean text or the
certified computation that supports it. The computations are `numerics/review/unlock_chain_checks.py` (record
`numerics/results-unlock-chain-checks-2026-11-16.txt`, 12 of 12, with five negative controls that fail as required).

### 2.1 Chains made only of existing statements

| Chain | Assembly | Gives | Check | Rung |
|---|---|---|---|---|
| K0 device kernel | LS-K at d = 1 with a single-site datum, TdF at d = 1 | the amplitude at site n and time t is `(2π)^{−1} e^{−2it} I(2t, n)`, `I` the frozen integral `latticeKernel1` | statements read; the integral enclosed by rigorous quadrature and, separately, by an exact-rational series (check K2: 30 points, enclosure radius below 1e-25) | L4 for the identity, L2 for each value |
| K1 probability envelope | LS-D at d = 1 | every single-site probability is at most `min{1, (C*/2π)² (2t)^{−2/3}}`, `(C*/2π)² = 2.394…` | statement read; check K1 (77 points; the largest ratio of kernel to bound is 0.508) | L4 |
| K2 units | the substitution `ψ_n(z) = e^{−iβz} u_n(κz)` | a uniform array with coupling κ obeys K0 and K1 with `t = κz` | one line on paper; a sign change of κ is the gauge `(−1)^n` | L3 |
| K3 two-dimensional square array | LS-K, LS-D at d = 2 | peak probability at most `(C*/2π)⁴ (2κz)^{−4/3}` for nearest-neighbour coupling only | statement read. It does **not** apply to arrays with diagonal coupling (the 49 × 49 lattice of Tang et al. has them) | L4 |
| K4 sharp two-dimensional rate | T6L with SH | the rate `t^{−2/3}` of the square lattice is attained on the diagonal | already a consumer example (`examples/consumer/ConsumerLattice.lean`) | L4 |
| K5 any one-dimensional dispersion relation | S1.k on each piece of a partition, summed | `\|∫ e^{i(tω(k) + ξk)}ψ\| ≤ Σ_i c_{k_i}(tμ_i)^{−1/k_i}(…)` for every real ξ, from derivative lower bounds `\|ω^{(k_i)}\| ≥ μ_i`, `k_i ≥ 2` | S1.k read (uniform in the linear term, k ≥ 2); check K7: for ω = cos and five pieces the sum is exactly the T0E formula | L3 (a finite sum of L4 statements; the sum itself is node N5) |
| K6 Bessel bound | T0E′ at integer ξ with the identification `I(t, n) = 2π iⁿ J_n(t)` | `\|J_n(t)\| ≤ 1.5473 t^{−1/3}` for every integer n and t > 0 | the identification is a paper step (DLMF 10.9.2), validated by check K2 | L3 |

**The strongest case against chains K0–K6.** K1, K3 and K6 are weaker than what is in print: Landau's constant
0.7857 replaces 1.5473 at lattice sites (`docs/prior_art.md`, disclosure of 2026-11-16), so a careful author would
cite Landau, not OscInt, for the number. K5's constants are those of Stein's textbook proof and are useful only at
large t (for ω = cos it beats the trivial bound from t ≈ 518). What the chains add is the machine check, the
uniformity in real ξ, and the fact that they are statements about solutions and not only about kernels.

### 2.2 Chains that need one new node

| Chain | New node | Assembly | Gives | Check | Rung today |
|---|---|---|---|---|---|
| K7 light cone | N1 | a contour shift of the kernel integrand over one period | `\|I(t, n)\| ≤ 2π e^{\|t\| sinh η − \|n\| η}` for every η ≥ 0: superexponential smallness outside the cone `\|n\| > \|t\|`, with the sharp cone velocity | check K3 (462 points) | L3 on paper, L2 validated |
| K8 ring | N1, N2 | the ring propagator is the lattice kernel summed over a coset; N1 bounds everything but the nearest term | on a ring of N sites every OscInt lattice statement holds up to an explicit error that is superexponentially small until the walk wraps around | check K4: matrix exponential, Fourier sum and coset sum agree at 93 entries | L3, L2 validated |
| K9 open chain | N2, N3 | odd reflection embeds the chain of M identical sites into the ring of 2(M + 1) sites | the same for the device that laboratories actually build | check K5 (333 entries); the control with free ends fails as it must | L3, L2 validated |
| K10 trapezoidal rule | N2 read backwards | the N-point trapezoidal sum of the kernel integrand is the ring propagator, so its error is the coset sum without its main term | a certified evaluator of the lattice kernel by a plain sum of N terms, with a proved error bound: the trapezoidal-rule theorem of Trefethen and Weideman for this integrand | same computation as K4 | L3, L2 validated |
| K11 array sizing | N1 | sum the light-cone bound over the sites beyond the edge | a guaranteed bound on the probability that has left an array of N guides at length z: the number a designer now gets from simulation | section 6, row A | L3 |
| K12 ballistic law | N4 | Parseval for the derivative of the symbol | `Σ n² p_n(t) = 2t²` exactly: the quantity plotted as "ballistic spreading" in walk experiments | check K6; the diffusive control fails as it must | L3, L2 validated |

K7–K10 are one mechanism seen four times: **the Fourier coefficients of a periodic function analytic in a strip decay
exponentially, and sampling at N points folds them onto each other.** The general statements are (a) `|c_k| ≤
M e^{−a|k|}` for a 2π-periodic function bounded by M in the strip `|Im θ| < a`, and (b) the trapezoidal-rule error
bound `|I_N − I| ≤ 4πM/(e^{aN} − 1)` (Trefethen and Weideman, SIAM Review 56 (2014), Theorem 3.2, read by both sweep
agents). N1 is (a) for the integrand `e^{it cos θ}`, with `M = e^{|t| sinh a}`; K10 is (b) for it. Proving (a) and (b)
once, in general, and reading off the lattice statements as corollaries is the elegant route, and (b) is a theorem
that numerical analysts cite constantly and that no proof assistant has (section 5).

### 2.3 Edges to consumers

| From | To | Mechanism |
|---|---|---|
| G6, G7, N1–N3 | a qubit chain or ring; a waveguide array (section 6) | the device's equation is the lattice equation; N2 and N3 make the statement about N sites |
| N1, K10, the general statements (a), (b) | certified numerics, FFT users (section 3.9) | a proved aliasing bound for a sampled Fourier integral |
| G1 (S1.k), N5 | any one-dimensional dispersion relation: next-nearest-neighbour arrays, long-range chains, numerical schemes | derivative lower bounds on pieces are decidable by interval arithmetic, so the hypothesis can be certified by a program |
| N8, N9 | every row above | a bound is usable only once it is evaluated: the certificate carries the statement's commitment, exact inputs and an enclosure |
| G2, G5 | two-dimensional non-separable lattices | blocked: no explicit constants, and no classified non-separable model (`docs/design/vector-amplitudes.md` §6) |
| G3 (S4.2U, S4.2O) | a downstream project (two-dimensional split-step quantum walks) | the D4 limit along sites with bounded offset |
| an explicit sum version of S1.k (not a node yet) | explicit analytic number theory (section 3.10) | that field's constants come from exponential-sum lemmas, one of which was wrong in print for years (section 4, F8) |

## 3. Domain sweep

Two fresh-context agents read the literature on 2026-11-16 (230 searches and page reads between them; their briefs
are not committed, their SHA-256 are in the session log). An entry is listed only with a quantity someone computes
and a source that was opened; the label says how much was read. The lead re-read only the sources marked †. "Covers"
means a statement in section 1.1 applies as it stands.

### 3.1 Photonics and caustic optics

| Quantity computed | Integral and singularity | OscInt today | Missing | Who would use it | Source |
|---|---|---|---|---|---|
| output intensity of a uniform waveguide array, `n_q = J_{q−k}(2Cz)²` | the lattice kernel; fold at the two ballistic lobes | K0–K2 cover the infinite array | finite arrays (N2, N3); the sharp constant (N6) | designers sizing an array (K11); benchmark references | Bromberg et al., arXiv:0807.3938, CITED-READ full text |
| two-photon correlation matrix after length z | products of two lattice kernels | values by K0 | a certified evaluator (N8) | experiments claiming a violation by many standard deviations need the ideal value far below their statistical error | Peruzzo et al., arXiv:1006.4764, CITED-READ full text |
| pattern and variance of a 49 × 49 two-dimensional walk | a two-dimensional kernel with diagonal couplings | not covered (K3 needs nearest-neighbour coupling only) | a classified non-separable symbol with constants | the same groups | Tang et al., arXiv:1704.08242, CITED-READ full text |
| field of an Airy beam near its caustic | cubic phase; fold | S3 gives the uniform rate, no constant | explicit constants; the Airy leading term with a remainder | beam designers who invert a caustic into a phase mask | Efremidis et al., arXiv:1904.02933, CITED-READ §2, §4 |
| canonical diffraction integrals (Pearcey, umbilics) | cusp, swallowtail, umbilics | S5.1′, S4.1′, S4.4 give uniform rates and the D4 constant | sup-norm bounds in the handbook's notation, with constants | numerical libraries needing reference values; the handbook prints leading-order uniform approximations with no remainder bound | DLMF chapter 36 (version 1.2.8), CITED-READ |
| comb lines of a modulated ring resonator (synthetic frequency dimension) | the lattice kernel along frequency | K0–K1 | as the first row | comb-bandwidth estimates are tail bounds on `J_m` (K11) | Yuan et al., arXiv:1807.11468, CITED-READ §II; the explicit Bessel form is STANDARD-TEXT |

### 3.2 Quantum hardware, walks and semiclassics

| Quantity computed | Integral and singularity | OscInt today | Missing | Who would use it | Source |
|---|---|---|---|---|---|
| site populations of one excitation on a transmon chain | the finite-chain kernel | K0 for the infinite chain | N2, N3; a certified reference (N8) | benchmarking: a closed, certified reference removes "simulation error" from the budget | Karamlou et al., arXiv:2107.05035, CITED-READ full text |
| populations and front velocity on a 62-qubit array | a two-dimensional propagator | K3 if the couplings are nearest-neighbour only (not checked) | N2 in two dimensions | the same | Gong et al., arXiv:2102.02573, CITED-READ full text |
| amplitude of the Hadamard walk on the line | fold at `n/t = ±1/√2`: "two peaks of width O(t^{1/3})" where the wave function "goes as t^{−1/3}" | S1.k gives a bound once the walk's dispersion relation is entered (K5) | the statement itself; the Airy leading term | algorithm papers that quote the rate | Nayak and Vishwanath, arXiv:quant-ph/0010117, CITED-READ full text; Sunada and Tate, arXiv:1108.1878, CITED-READ §1, §3 (Airy asymptotics, implicit constants) |
| magnetisation front of the XX chain; convergence to the Airy kernel | sums of `J_m(t)²`; fold | K6 | the sharp constant (N6); the Airy leading term with a remainder | proofs of trace-class convergence need a uniform `t^{−1/3}` bound with constants to dominate remainders | Hunyadi et al., arXiv:cond-mat/0312250; Eisler and Rácz, arXiv:1211.2321; both CITED-READ full text |
| light cone of the free-fermion chain | the lattice kernel outside the cone | nothing | N1 | the sharp cone velocity is supported in a current review by asymptotics, the rigorous bound there has velocity `2e` times the hopping instead of 2 | Chen, Lucas and Yin, arXiv:2303.07386, CITED-READ §3.1 |
| Trotter error of a digital simulation | none (commutator bounds) | nothing, and not needed | — | with a certified exact amplitude the Trotter part of an error budget is computed exactly (section 6) | Childs et al., arXiv:1912.08854, CITED-READ abstract |

### 3.3 Electrical engineering and radar

| Quantity computed | Integral and singularity | OscInt today | Missing | Who would use it | Source |
|---|---|---|---|---|---|
| spectrum of a linear-FM pulse | quadratic phase on a window: a stationary point that collides with an endpoint at the band edges | S1.2 bounds it; no leading term | the stationary-phase value with an explicit remainder in `1/√(TΔF)` | waveform designers; the rule "time-bandwidth product above 100" is a rule of thumb | "Chirp spectrum", Wikipedia, citing Cook and Bernfeld (1967) p. 49: SECONDARY |
| two-dimensional spectrum of a SAR point target | stationary phase in azimuth | S2.2-type bounds | the leading term with remainder (`docs/design/leading-term.md`) | processor designers at low time-bandwidth product; today checked by simulation | Tolman, MSc thesis, Brigham Young University, ch. 6, CITED-READ |
| edge-diffraction coefficient near a shadow boundary | a saddle point near a pole (Fresnel transition); not valid at caustics | not covered | endpoint and pole coalescence | antenna and radar-cross-section codes; validity thresholds are empirical | Kouyoumjian and Pathak, NASA CR-2401 (1974), CITED-READ (poor scan) |

The realistic deliverable for this community is a table of explicit constants, not a formal proof: it validates by
simulation. PLAUSIBLE (the sweep agent's reading, which the lead shares).

### 3.4 Plasma and fusion

| Quantity computed | Integral and singularity | OscInt today | Missing | Who would use it | Source |
|---|---|---|---|---|---|
| wave field at a cutoff (radio-frequency heating, reflectometry) | Airy integral; fold | S3 (rate) | constants; the Airy leading term | ray- and beam-tracing codes that need the amplitude at the cutoff | Lopez and Dodin, arXiv:2112.07399, CITED-READ abstract |
| gyroaverage factor `J₀(k⊥ρ)` and truncated Bessel sums | Bessel integral | K6 | N1 for the truncation of sums over harmonics | gyrokinetic code verification | DLMF 10.9.1, CITED-READ; the use is STANDARD-TEXT |
| phase mixing of free streaming | a Fourier transform, no stationary point | demonstrated (`examples/consumer/ConsumerPhaseMixing.lean`) | self-consistent fields | — | Mouhot and Villani, arXiv:0904.2760, CITED-READ abstract |

### 3.5 Gravitation

| Quantity computed | Integral and singularity | OscInt today | Missing | Who would use it | Source |
|---|---|---|---|---|---|
| wave-optics lensing amplification `F(w, y)` | a two-dimensional Fermat-potential integral; fold and cusp at caustics | S3, S5.1′ give `\|F\|` bounds uniform in the source position, without constants, for compactly supported amplitudes | the conditionally convergent integral over the whole plane; constants | waveform modellers near caustics | Ezquiaga et al., arXiv:2503.22648; Serra and Bulashenko, arXiv:2504.10128; both CITED-READ abstract |
| Fourier transform of an inspiral chirp | one nondegenerate stationary point and two endpoints | S1.2-type bound | the stationary-phase value with an explicit remainder for phases `(t_c − t)^{5/8}` | template-bank authors who quote "the error is negligible" | Droz et al., arXiv:gr-qc/9901076, CITED-READ full text |
| quasinormal modes by WKB | two close turning points | not covered | not an oscillatory-integral estimate of this kind | — | Konoplya et al., arXiv:1904.10333, CITED-READ abstract |

### 3.6 Accelerators

| Quantity computed | Integral and singularity | OscInt today | Missing | Who would use it | Source |
|---|---|---|---|---|---|
| bending-magnet spectrum | cubic phase without a real stationary point; exact closed forms in `K_{2/3}`, `K_{5/3}` | not needed | — | low interest: closed forms exist | Kim, X-Ray Data Booklet §2.1, CITED-READ |
| undulator harmonics | Bessel sums truncated ad hoc | K6 | N1 for a certified truncation | undulator-spectrum codes | the same page, CITED-READ; the JJ formula is STANDARD-TEXT |
| coherent synchrotron radiation wake | Airy functions; the asymptotic wake fails at short range | S3 (rate) | constants | tracking codes that replace the wake by its asymptotic form | Ryne et al., arXiv:1202.2409, CITED-READ abstract |

### 3.7 Artificial intelligence and machine learning

Demand is close to nil. Random Fourier features, the spectral bias of ReLU networks, Fourier-feature mappings and
Fourier neural operators involve Fourier integrals but no stationary-phase structure (Rahimi and Recht 2007;
arXiv:1806.08734; arXiv:2006.10739; arXiv:2010.08895; all CITED-READ at least in the relevant section). The one
overlap is the aliasing error of a truncated Fourier layer, which is K10's subject. This domain stays out of the
ranking.

### 3.8 Combinatorics and probability

| Quantity computed | Integral and singularity | OscInt today | Missing | Who would use it | Source |
|---|---|---|---|---|---|
| amplitudes of two-dimensional quantum walks | a torus integral; zero curvature on the boundary of the feasible region (fold and worse) | G2, G5 give uniform bounds across the boundary once a model is classified | a classified model; constants | this is the two-dimensional analogue of OscInt's fold and cusp bounds | Baryshnikov et al., arXiv:0810.5495, CITED-READ abstract |
| local limit theorems with explicit error | Laplace-type integral of a characteristic function | not covered (real exponent, not oscillatory) | — | — | Giuliano and Weber, arXiv:1412.3980, CITED-READ abstract |
| coefficient asymptotics by the saddle-point method | nondegenerate and coalescing saddles | not covered (complex contours) | — | effective analytic combinatorics | Flajolet and Sedgewick, ch. VIII: STANDARD-TEXT |

### 3.9 Computing: oscillatory quadrature and aliasing

| Quantity computed | Integral and singularity | OscInt today | Missing | Who would use it | Source |
|---|---|---|---|---|---|
| trapezoidal rule or DFT of a periodic analytic integrand | none; aliasing only | nothing | the general statements (a), (b) of section 2.2 | everyone who samples a Fourier integral: the theorem `\|I_N − I\| ≤ 4πM/(e^{aN} − 1)` has the best possible constant and is not formalised | Trefethen and Weideman, SIAM Review 56 (2014) 385–458, Theorem 3.2, CITED-READ (theorem statements) |
| highly oscillatory quadrature near coalescing saddles | fold, cusp, swallowtail | G2 gives the analytic statement behind "uniform accuracy" | certified reference values for the canonical integrals | authors of steepest-descent quadrature, who show accuracy "by a series of numerical experiments" | Gibbs, Hewett and Huybrechs, arXiv:2307.07261, CITED-READ §1, §4, §5 |
| rigorous quadrature in ball arithmetic | any analytic integrand at fixed parameters | complementary: Arb certifies a number at given parameters, a proof certifies a statement uniform in the parameters | N8 uses both | computer-assisted proofs need both halves | Johansson, arXiv:1802.07942, CITED-READ full text |
| non-uniform FFT to a tolerance | aliasing sum of a kernel's transform, bounded by steepest descent | nothing | — | small audience; the library designs for typical errors because the rigorous bound is pessimistic | Barnett et al., arXiv:1808.06736, CITED-READ §1, §4 |

### 3.10 Number theory

| Quantity computed | Integral or sum and singularity | OscInt today | Missing | Who would use it | Source |
|---|---|---|---|---|---|
| explicit bounds for `ζ(1/2 + it)` | exponential sums by Weyl differencing, derivative tests and the Kusmin–Landau inequality | S1.k is the integral version only | the sum versions: Kusmin–Landau, the second- and third-derivative tests with the constants in use | explicit analytic number theory: every zero-free region and prime-counting bound downstream. The record is `0.611 t^{1/6} log t` | Revers, arXiv:2602.05614, CITED-READ; Hiary, Patel and Yang, arXiv:2207.02366, CITED-READ abstract |
| explicit k-th derivative test for sums | iterated differencing | — | the same | "the difficulty with bounding the implied constants of the kth derivative test" is named as the main obstacle | Yang, arXiv:2301.03165, CITED-READ |
| truncated Poisson summation (the B-process) with explicit error | integrals with a nondegenerate stationary point | S1.2 is the integral ingredient | the stationary-phase value with explicit remainder | the same community | Dhiman et al., arXiv:2609.00537, CITED-READ abstract |

This is the one community where explicit van der Corput constants are already a research product and where an error
in one lemma propagated through a decade of papers (section 4, F8).

## 4. FOLKLORE register

Claims that practitioners rely on, with what OscInt can do about each. "Can prove" means a route exists from the
existing statements; it is not a result.

| # | Claim, as used | Source that states or uses it | What is actually established there | OscInt: prove, refute or bound |
|---|---|---|---|---|
| F1 | the peak probability of a one-dimensional quantum walk decays like `t^{−2/3}` | Nayak and Vishwanath (CITED-READ): amplitude "goes as t^{−1/3}", appendices "sketch proofs" | asymptotics with unspecified remainders; Sunada and Tate prove Airy asymptotics with implicit constants | **PROVEN as an upper bound** for the continuous-time walk on ℤ (LS-D, explicit constant); for the Hadamard walk a bound follows from K5 once its dispersion relation is entered (not done); the matching lower bound needs a fold leading term (not available in one dimension) |
| F2 | `\|J_ν(x)\| ≤ 0.6749 ν^{−1/3}` and `≤ 0.7857 x^{−1/3}`, best possible | Landau, J. London Math. Soc. 61 (2000), abstract page read; his survey read in full | a theorem; by the survey the proof uses five computed table values and says "we do not show X_ν > x_ν for all ν" | **can bound** (K6, factor 1.97 weaker); the sharp statement is node N6, with those five comparisons certified by interval arithmetic |
| F3 | stationary phase is valid for a chirp when the time-bandwidth product exceeds about 100 | Wikipedia citing Cook and Bernfeld (SECONDARY) | a rule of thumb; for a rectangular window the error is an endpoint term of relative size about `(TΔF)^{−1/2}` (PLAUSIBLE) | **can bound** with S1.2 and an explicit leading-term remainder (the remainder is not available yet) |
| F4 | the stationary-phase transform of an inspiral waveform is accurate ("We prove…") | Droz et al. (CITED-READ full text) | a next-order term with unquantified remainder and numerical overlaps; no inequality | **can bound**, as F3 |
| F5 | the trapezoidal rule converges exponentially for periodic analytic integrands | Trefethen and Weideman, Theorem 3.2 (CITED-READ) | **a theorem with the best possible constant; not folklore.** The folklore is the usual citation "error `O(e^{−aN})`" without M or the constant | **can prove** the theorem itself (section 2.2); no proof assistant has it |
| F6 | the Lieb–Robinson velocity of the free-fermion chain is twice the hopping, and the propagator is superexponentially small outside the cone | Chen, Lucas and Yin (CITED-READ §3.1) | their rigorous bound has velocity `2e` times the hopping; the sharp cone is "confirmed" from Bessel asymptotics | **can prove**: N1 is an inequality with the sharp cone. It is classical (Kapteyn's inequality; Siegel's bound, DLMF 10.14.5), so the claim is true and known; what is missing is its use, and a machine check |
| F7 | WKB quasinormal frequencies are accurate to N digits | Konoplya et al. (CITED-READ abstract): "no mathematically strict criterium for evaluation of an error" | none | out of reach: not an estimate of OscInt's kind |
| F8 | explicit van der Corput constants in the literature are reliable | Revers; Hiary, Patel and Yang (CITED-READ) | **REFUTED in print:** a lemma of Cheng and Graham had `1/π` where `2/π` is correct; Hiary's 0.63 becomes about 0.77 and a 2015 bound of Platt and Trudgian is affected | **can prove** the Kusmin–Landau inequality with its sharp constant `cot(πλ/2)`; whether it is already formalised is being checked (section 5, P1) |
| F9 | the discrete Klein–Gordon kernel on ℤ^d decays like `t^{−d/3}` | Stefanov and Kevrekidis (CITED-READ full text): a numerical fit gave 0.675 in two dimensions | the true two-dimensional rate is 3/4 (Borovyk and Goldberg; Cuenin and Ikromov) | **REFUTED in print** as a sharp rate; S5.1′ is the local ingredient of the correct one |

## 5. Open problems and formalisation targets

"Verified open" means: the cited paper says so, and the sweep found no later resolution. That is weaker than a
citation crawl; zbMATH was not queried.

| # | Problem | Status found | Why it matters | Partial result worth having | Feasibility |
|---|---|---|---|---|---|
| O1 | the sharp constant in van der Corput's lemma for k = 2 | **not open (corrected 2026-11-16, same day):** the sharp value is classical, "van der Corput's constant" 3.3643175781…, determined by R. Kershner (Amer. J. Math. 57 (1935) and 60 (1938); zbMATH 0012.34801, 0019.10902; S. Finch, *Mathematical Constants*, pp. 245–246; OEIS A143305). Rogers (arXiv:math/0311013, read by the lead in LaTeX source) proves `3^{3/4}·2 ≈ 4.56` and reports the same number 3.3643 only as suggested by numerical experiments, without citing Kershner. The first version of this row said "verified open" on Rogers's word; a logged search by the lead refuted that within the hour (`docs/prior_art.md`, section of 2026-11-16 on the second-derivative constant). Kershner's papers and Finch's pages were not read | every constant downstream of S1.2 (8 here) inherits it | machine-check the classical sharp theorem: S1.2's 8 would improve by a factor 2.38; and the sharp k = 1 constant 2 | medium: a proof by a change of variable to the phase exists on paper (lead, unrefereed); the formal change of variables and the Fresnel maximum are the work |
| O2 | the best constant for the lattice Schrödinger estimate on ℤ^d | **not open**: Landau's 0.7857 at lattice sites; Korotyaev and Møller use it | LS-D is a factor 1.97 per dimension off | formalise Landau (N6); the large-time constant 0.6749; the constant over all real ξ (not found in print: PLAUSIBLE-not-known) | medium to low; multi-session |
| O3 | explicit constants for discrete Klein–Gordon and wave kernels in dimension ≥ 2 | verified: every theorem is "there exists C"; Cuenin and Ikromov's three-dimensional proof has a step "it can be checked numerically" | the largest set of already-classified models needs exactly A2 and A3 bounds | an explicit `t^{−3/4}` constant in two dimensions | medium to low: needs explicit constants in G2, which do not exist (`docs/constants.md`) |
| O4 | dispersive decay on other planar lattices | triangular `t^{−3/4}`, honeycomb `t^{−2/3}` are proved without constants; other tilings stated as open by Ge et al. (arXiv:2412.02947, CITED-READ) | photonic graphene and kagome lattices | a machine-checked rate for one non-separable model | medium: needs the classification discharged in Lean |
| O5 | stability of oscillatory estimates under perturbation beyond two variables | verified open in general (Ikromov and Toshpulatov, arXiv:2602.18163, CITED-READ) | lattice results in dimension ≥ 3 use Karpushkin's theorem as a black box | uniform A4, A5 bounds | low |
| O6 | sup-norm bounds with constants for the Pearcey and swallowtail integrals | not found posed in print (PLAUSIBLE-open, absence of evidence) | lensing near cusps; S5.1′ already implies a Pearcey bound without a constant | S5.1′ restated in the handbook's notation | high for the restatement, low for a constant |

Formalisation prior art that bears on the choice of work (sweep B, part 4; nothing was built or audited):

| # | Target | Found formalised? |
|---|---|---|
| P1 | the Kusmin–Landau inequality | not searched yet: a targeted check is running (session log, sweep C) |
| P2 | exponential convergence of the trapezoidal rule; decay of the Fourier coefficients of a function analytic in a strip; the aliasing identity | none found; Mathlib has only the `O(N^{−2})` trapezoidal error and Poisson summation on the real line |
| P3 | a light-cone bound for the free lattice with the sharp velocity | none found; two Lean developments of the general Lieb–Robinson bound exist |
| P4 | lattice dispersive estimates; uniform fold, cusp, umbilic bounds; k-th derivative van der Corput with constants | none found outside this repository and the van der Corput port it derives from |
| P5 | Bessel's integral, Jacobi–Anger, the generating function | yes, outside Mathlib: `bjbraams/lean-DLMF` |

## 6. Hardware and lab register

Every predicted value is an enclosure from `numerics/review/unlock_register_values.py` (record
`numerics/results-unlock-register-values-2026-11-16.txt`; ball arithmetic). Device facts are from sweep A, with its
labels. Error-model numbers are assumptions, marked as such; no hardware has been run and none will be without the
owner's approval.

**The plain finding first.** No device found can test an OscInt *bound*: the machine-checked envelope is far above
what any clean device shows, and laboratory precision is at the percent level. What a device can test is the
*kernel*: site populations with certified enclosures. The physics of that test has been confirmed since 2008; a run
would benchmark the device against a certified reference and exercise the trust chain end to end. It would not be a
discovery.

| # | Device and quantity | Machine-checked statement tested | Predicted value (certified) | Noise and error budget | Can the device resolve it? | Access and cost |
|---|---|---|---|---|---|---|
| A | coupled waveguide array, 21 or 89 guides, centre input; output intensity per guide at the published lengths, Bessel argument `x = 2κz` of 4.64, 7.8 and 11.0 | LS-K for the profile, LS-D for the envelope, both through K2; for 21 guides also ASSUMED(L4, the chain statement N3 is not proved, lead) | peak `J_n²`: 0.170896 at `\|n\| = 3`, 0.121299 at `\|n\| = 6`, 0.0953917 at `\|n\| = 9`. LS-D envelope: 0.8606, 0.6087, 0.4841. Envelope with Landau's constant: 0.2219, 0.1570, 0.1248. Probability beyond a 21-guide array in the infinite-lattice model: 5.8e-8, 1.0e-3, 0.1209 | published similarity to theory 0.90–0.98 (Peruzzo et al.; Meinecke et al., CITED-READ), about 10% chip coupling | the profile: yes, at a few percent. The LS-D envelope: no, it is 5 times above the peak. The envelope with Landau's constant: nearly (1.3 times above). At `x = 11.0` with 21 guides the infinite-lattice formula is wrong by 12% of the probability, so the finite chain must be used | no open route found; a partner laboratory. Cost unknown |
| B | gate-based superconducting processor, an open chain of 9 qubits, one excitation at the centre, Trotterised exchange coupling; populations at `t = 1` and `t = 2` (units of the inverse hopping) and the second moment | LS-K through ASSUMED(L4, N3, lead), validated at L2 by check K5 | `t = 1`: centre 0.050127, neighbours 0.33261, next 0.12451; second moment 1.99939. `t = 2`: centre 0.15742, neighbours 0.0044817, ends 0.10904; second moment 7.68269 (the infinite line gives 8; the largest population difference from the infinite line is 0.0300) | Trotter error, exact in this sector: second order with step 1/4 gives at most 0.00698 (`t = 1`, 9 bond layers) and 0.00338 (`t = 2`, 17 bond layers); first order with the same step gives 0.0704. Hardware: median two-qubit error 1.2e-3 to 2.8e-3 on the public IBM list (CITED-READ, live values of 2026-11-16); 17 layers of 4 bonds at 2 two-qubit gates per bond (ASSUMED decomposition) is 136 gates, so an unmitigated circuit fidelity near `e^{−136·0.003} ≈ 0.66` (ASSUMED error model); shot noise at 4000 shots is about 0.01 per population | the profile: yes, PLAUSIBLY at 2–5% per population after post-selection on one excitation; published IBM-hardware chain experiments are only 4–5 sites, so this is not demonstrated. The chain-against-infinite-line difference at `t = 2` (0.03): borderline. Any bound: no | IBM Open Plan: free, 10 minutes per 28 days (CITED-READ), enough for a pilot of a few dozen circuits. EuroHPC Quantum Access Pilot, Euro-Q-Exa: 1 to 10 QPU hours, cut-off 1 December 2026 (`docs/funding/00-call-findings.md`); its calibration data has not been read |
| C | programmable photonic interferometer of 12 modes (Quandela Ascella), `U = e^{−iHt}` entered as a matrix, one photon; output distribution with `t` a software parameter | as B | as B with 12 sites (not computed yet) | unitary fidelity 99.7 ± 0.08%, total efficiency about 8% (Maring et al., arXiv:2306.00874, CITED-READ) | yes for the profile; the front reaches the boundary at `2t ≈ 6` | the vendor's cloud (price NOT FOUND) or, PLAUSIBLY, the photonic system of the EuroHPC pilot (minimum request 10 QPU hours; whether it accepts a user unitary is NOT VERIFIED) |
| D | analogue transmon arrays (7-site chain, 62-qubit array) | as B | — | published fidelity above 96% for the first 200 ns on 7 sites (Karamlou et al., CITED-READ) | yes, and it has been done | not user-accessible: **not feasible** without a partner |
| E | NTT coherent Ising machine and similar optical optimisers | none | — | — | no: an Ising optimiser is not a programmable linear interferometer for amplitudes (PLAUSIBLE), and access is for research collaborators (page of 2020, CITED-READ) | **not feasible** |
| F | two-dimensional waveguide lattices with diagonal coupling (49 × 49) | none: K3 needs nearest-neighbour coupling only | — | — | — | **not feasible today**: no OscInt statement applies |

What would change the finding: the sharp constant (N6) brings the envelope within a factor 1.3 of the peak at
published lengths, and disorder raises the peak (localisation), so with N6 and N3 the envelope becomes a usable
certified test that a device is *not* localised. With the present constant it is not. CONJECTURED (the argument about
disorder is physical reasoning, not computed here).

## 7. Ranking by value per unit of effort

Value is scored against the owner's four criteria: (1) new or newly machine-checked mathematics, (2) verified
predictions that experiments test, (3) tools people use, (4) funding and partners. Effort is in sessions of this kind,
including the three-hour replay for a statement batch. The ranking is the lead's judgement; the reasons are in the
last column so that it can be overruled.

| Rank | Item | Value | Effort | Why here |
|---|---|---|---|---|
| 1 | application drafts for the 1 December cut-off | (4); hardware access for (2) | under 1 | the only item with a deadline; each section is complete on its own |
| 2 | the general periodic-analytic statements: Fourier-coefficient decay in a strip, and the trapezoidal-rule theorem with the constant 4π; the lattice light cone N1 as a corollary | (1): a theorem cited across numerical analysis, in no proof assistant; unlocks K7–K11 and the soundness of the certified evaluator | 1 | one mechanism behind four chains; short classical proofs; a general theorem instead of four special ones |
| 3 | the Kusmin–Landau inequality with the sharp constant, in difference form | (1): the lemma whose wrong constant propagated for a decade (F8) | under 1, if the prior-art check P1 finds it is not already formalised | small, self-contained, and the one community that already publishes explicit constants |
| 4 | certified evaluator, certificate format and the one checker (N8, N9), then the command-line tool and packages | (3); makes every explicit statement evaluable; the experiment protocol needs it | 1 | no stamp or replay needed; value on its own |
| 5 | the quantum-walk protocol for a 9-qubit chain (N10): registered, simulated two ways, ready to run | (2), (4) | under 1 after item 4 | row B above; honest about being a benchmark |
| 6 | ring and open-chain statements (N2, N3) | (1), and turns the ASSUMED bridge of rows A–C into a machine-checked one | 1 to 2 | needs item 2 first |
| 7 | Rogers's constants: sharp 2 for k = 1 and 4.56 for k = 2 | (1); improves every constant derived from S1.1 and S1.2 | 1 | short proofs; a constant, not a new capability |
| 8 | the ballistic identity N4; the partition bound N5 | (1), (2), small | under 1 each | cheap, but nobody is blocked on them |
| 9 | Landau's theorem (N6) | (1); halves LS-D's constant per dimension and makes row A's envelope usable | 3 or more | high value, real difficulty: Sturm-type monotonicity and five certified comparisons |
| 10 | general finite-range hopping (N7); an explicit two-dimensional constant (O3); a non-separable model (O4) | (1), (2) | 3 or more each | large; the two-dimensional items wait on explicit constants for G2 |
| — | radar and waveform remainders (F3, F4), Pearcey restatement (O6) | (1), small audience for formal proofs | 1 each | need the leading-term work first |
| — | machine learning; quasinormal modes; coherent Ising machines | none found | — | out of the ranking (sections 3.7, 4, 6) |

## 8. Plan for session 13

In this order, so that a stop at any point leaves finished pieces:
1. This map (done with this section) and its one-page summary in chat.
2. Statement batch for item 2, and for item 3 if P1 allows: statements, sanity layer with planted controls,
   challenge and comparator files, stamp, blind pre-proof reviews. While the referees run the tree is frozen, so the
   application sections (item 1) are written in scratch during those windows and committed when the referees end.
3. Application sections committed one by one (`docs/funding/`).
4. Route documents and blueprints with the assemblies compiled first; route referee; proof parts by proof agents;
   integration; post-proof reviews; one isolated replay for both batches.
5. During the replay (no Lean process allowed, tree frozen): item 4, the evaluator, certificate format and checker,
   written in scratch and committed when the replay ends; then item 5.
6. Items 6 onward are for later sessions unless time remains.

Registered before starting, for the two batches: **time box** one session; **stop rule** a BLOCKER from a blind
referee that cannot be answered by a new statement the same day, or a part that does not elaborate after two proof
agents; **partial result worth keeping** a frozen, reviewed statement with a compiled assembly (as batch LS was in
v0.5.0), or the Fourier-coefficient bound alone without the trapezoidal theorem.

**The strongest case against this plan.** Items 2 and 3 are classical mathematics; the claim can only be
"machine-checked", and a reader may ask why a library about oscillatory integrals proves a quadrature theorem and an
exponential-sum inequality. The answer given here is that they are the two places found where practitioners rely on
exactly this kind of estimate and where a check is missing or the literature was wrong; if the owner prefers depth in
the existing subject, items 7 and 9 are the alternatives. The hardware item cannot produce a surprise. And the
application may be ineligible (an unaffiliated individual), which only the owner can settle.
