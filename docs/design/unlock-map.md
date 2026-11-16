# The unlock map (session 13, 2026-11-16)

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

Sections 2 onward: pending.
