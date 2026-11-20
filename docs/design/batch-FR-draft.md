<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->
# Batch FR (finite ring, open chain): DRAFT statements, not frozen

Status: a design draft by the lead, session 13 (2026-11-16). Nothing here is a statement of OscInt yet: there is no
statement file in the tree, no pin, no stamp, no review, and nothing here is counted in `docs/STATUS.md`. The draft
is committed so that the work survives a lost session. It may change before any freeze. No proof of any of these
exists, in the tree or in scratch, and none may be written before the batch is frozen, reviewed and the answers
stamped (rule 1).

What it is for. Nodes N2 and N3 of `docs/design/unlock-map.md`: the step from the infinite lattice of batches LE to
LS and PA to the devices that exist (a ring of N sites; an open chain of M sites). With these statements the
reference values of the registered protocol `docs/prereg/2026-11-16-CTQW-chain.md` would rest on a machine-checked
identification of the chain's propagator instead of a matrix exponential computed in ball arithmetic, and the
distance between the chain and the infinite line would have a proved bound.

Evidence so far (tooling, not proof): `numerics/review/fr_statement_checks.py`, results
`numerics/results-fr-statement-checks-2026-11-16.txt`: 12 of 12 checks pass, in ball arithmetic, by two methods that
share no formula (the kernels as defined; the matrix exponential of the graph Laplacian), with five controls that
fail as they must. One control did its job on the draft itself: the first form of FR-P had e^{|r|η} where cosh(rη)
now stands; the control "without the factor 2" did not fail on it, which showed that form was a factor 2 from
sharp. The sharpened form holds at 1764 parameter points with a largest ratio of the two sides of 1.000000, and the
control now fails. The Lean text below compiles against the pinned Mathlib (lead, in scratch, 2026-11-16).

Dependencies, if frozen as drafted: FR-S and FR-P follow on paper from the Fourier-series and alias parts of batch
PA and from LC-1 (batch PA is not proved at the time of writing); FR-K is a finite calculation; FR-U and FC-U are
uniqueness for a finite linear system (conservation of the ℓ² norm); FC-K follows from FR-K and two symmetries of
the ring kernel; FC-P from FR-P and LC-1.

Numbers a device user would quote (certified enclosures from the same run; x = y is the centre site):

| Chain | Time | Distance of the chain kernel from the line kernel | FC-P bound (best η on a grid) |
|---|---|---|---|
| M = 9 | 1 | 5.03077e-7 | 3.98518e-6 |
| M = 9 | 2 | 3.90081e-4 | 3.01372e-3 |
| M = 5 | 1 | 2.40486e-3 | 1.46622e-2 |
| M = 5 | 2 | 9.81877e-2 | 5.46858e-1 |

Open before a freeze: the sanity layer and planted controls (data: N = 1, where the ring kernel is 1; N = 2; the
chain of one site, whose kernel is e^{−2it}); the challenge file and comparator; a second prior-art pass (below);
whether FR-U and FC-U should be stated on `ZMod N` and `Fin M` as well; a statement for populations.

## The statements as they would enter docs/statements.md

### Batch FR: the Schrödinger group on a ring of N sites and on an open chain of M sites (session 13, 2026-11-16)

Order. As batches PA and KL: statements (a Lean file FiniteRing under OscInt/Statements, not in the tree yet), sanity theorems with planted controls,
challenge and comparator, frozen and stamped before the blind pre-proof reviews; no Lean proof of these statements
exists, in the repository or in scratch, before the reviews are answered and stamped.

Why. Every lattice statement of OscInt so far is about the infinite lattice ℤ^d. A device is finite: a ring of N
coupled sites, or, far more often, an open chain of M sites (a waveguide array, a line of qubits). Two classical
facts connect them, and `docs/design/unlock-map.md` (nodes N2, N3; chains K8, K9) names them as the missing link
between the proved estimates and a prediction a laboratory can test: the propagator on a ring is the propagator on
the line summed over the images r + Nℤ (periodisation), and the propagator on an open chain with identical sites
is the odd part of the propagator on a ring of 2(M + 1) sites (reflection). With the light-cone bound LC-1 of batch
PA the images are small until the wave reaches a wall, with an explicit bound. The mathematics is classical (method
of images; discrete sine transform); the claim, if proved, is "machine-checked", not new mathematics. Formalisation
prior art: to be searched before the freeze and recorded in `docs/prior_art.md`.

Notation. The equation is i u′ + Δu = 0 with (Δu)(x) = u(x + 1) + u(x − 1) − 2u(x), as in batch LS with d = 1.
- **Line.** G(t, n) = (2π)^{−1} e^{−2it} I(2t, n) for n ∈ ℤ (Lean `lineKernel t n`), with I the 1D lattice kernel of batch
  LE. By LS-K and TdF with d = 1 it is the kernel of the group on ℓ²(ℤ); on paper G(t, n) = e^{−2it} i^n J_n(2t).
- **Ring of N ≥ 1 sites.** A function on the ring is a function on ℤ of period N.
  R_N(t, r) = N^{−1} Σ_{j=0}^{N−1} e^{i(2t(cos k_j − 1) + r k_j)}, k_j = 2πj/N (Lean `ringKernel N t r`).
- **Open chain of M sites.** The sites are 1, …, M; the walls are 0 and M + 1, where u = 0 (every site, including the
  two end sites, has the diagonal term −2: "identical sites").
  C_M(t; x, y) = R_{2(M+1)}(t, x − y) − R_{2(M+1)}(t, x + y) (Lean `chainKernel M t x y`).

**FR-K (the ring kernel).** For every N ≥ 1, real t and integer r: s ↦ R_N(s, r) has derivative
i (R_N(t, r + 1) + R_N(t, r − 1) − 2 R_N(t, r)) at t; R_N(0, r) is 1 if N divides r and 0 otherwise;
R_N(t, r + N) = R_N(t, r).

**FR-U (it is the propagator of the ring).** For every N ≥ 1 and every u : ℝ → ℤ → ℂ with u(t, x + N) = u(t, x) and
∂_t u(t, x) = i (u(t, x + 1) + u(t, x − 1) − 2u(t, x)) for all t and x: u(t, x) = Σ_{y=0}^{N−1} R_N(t, x − y) u(0, y).

**FR-S (method of images).** For every N ≥ 1, real t and integer r, the series Σ_{m ∈ ℤ} G(t, r + mN) converges
unconditionally and its sum is R_N(t, r).

**FR-P (finite-size error of the ring).** For every N ≥ 1, real t, integer r and η > 0:
|R_N(t, r) − G(t, r)| ≤ 2 e^{2|t| sinh η} cosh(rη) / (e^{ηN} − 1).

**FC-K (the chain kernel).** For every M, real t, integers x, y with 1 ≤ y ≤ M: s ↦ C_M(s; x, y) has derivative
i (C_M(t; x + 1, y) + C_M(t; x − 1, y) − 2 C_M(t; x, y)) at t; C_M(t; 0, y) = 0 and C_M(t; M + 1, y) = 0; and for
1 ≤ x ≤ M, C_M(0; x, y) is 1 if x = y and 0 otherwise.

**FC-U (it is the propagator of the chain).** For every M and every u : ℝ → ℤ → ℂ with u(t, 0) = u(t, M + 1) = 0 for
all t and ∂_t u(t, x) = i (u(t, x + 1) + u(t, x − 1) − 2u(t, x)) for all t and 1 ≤ x ≤ M:
u(t, x) = Σ_{y=1}^{M} C_M(t; x, y) u(0, y) for all t and 1 ≤ x ≤ M.

**FC-P (finite-size error of the chain).** For every M, real t, η > 0 and sites 1 ≤ x, y ≤ M:
|C_M(t; x, y) − G(t, x − y)| ≤ e^{2|t| sinh η} ( e^{−(x+y)η} + 2 (cosh((x − y)η) + cosh((x + y)η)) / (e^{2(M+1)η} − 1) ).

Modelling choices and omissions.
1. One dimension only. Rings and boxes in ℤ^d factorise (TdF), but that is not stated here.
2. A function on the ring is a periodic function on ℤ, not a function on `ZMod N`; a function on the chain is a
   function on ℤ of which only the values at 0, …, M + 1 are constrained. This keeps the statements free of
   coercions between `ZMod N`, `Fin N` and ℤ; the price is that FR-U and FC-U quantify over u : ℝ → ℤ → ℂ.
3. Time derivatives are taken site by site. For finitely many sites this is the derivative of the vector.
4. N = 1 and N = 2 are included. For N = 1 the "ring" is one site with Δ = 0 and R_1 = 1. For N = 2 the two
   neighbours of a site coincide, so Δu(x) = 2(u(x + 1) − u(x)): a double bond, which is what the formula gives and
   not what a two-site device with one bond does (that device is the open chain with M = 2).
5. M = 0 is included and vacuous in FC-K and FC-P (no y with 1 ≤ y ≤ 0); in FC-U it says nothing.
6. The chain has Dirichlet walls and the same diagonal −2 at every site. A chain whose end sites have diagonal −1
   (free ends, the graph Laplacian of a path) is the EVEN reflection and is not covered; its kernel is
   R_{2M}(t, x − y) + R_{2M}(t, x + y − 1). In the physical normalisation H = −κ Σ (|x⟩⟨x+1| + h.c.) with identical
   on-site energies, the diagonal is a constant and only changes a global phase: that device is this chain.
7. FR-P and FC-P have a free parameter η > 0, as LC-1. They say nothing useful once the wave has reached a wall
   (roughly 2|t| ≥ distance to the nearest image). FR-P is sharp as a supremum: at t = 0, r = N the left side is 1 and the
   right side is (e^{Nη} + e^{−Nη})/(e^{Nη} − 1), which tends to 1 as η → ∞; no constant smaller than 2 is true (a
   control with constant 1 fails). A first draft had e^{|r|η} in place of cosh(rη); a planted control ("without the factor 2") did not fail
   on it, which showed that draft was not sharp, and the statement was sharpened before the freeze.
8. FC-P keeps three images: the wall at 0 (the term e^{−(x+y)η}), and through the ring bound the wall at M + 1 and all
   further ones. It is not sharp (largest observed ratio of the two sides 0.36).
9. Populations: the probability at site x for a unit datum at y is |C_M(t; x, y)|². The statements bound amplitudes;
   ||a|² − |b|²| ≤ |a − b| (|a| + |b|) ≤ 2|a − b| for amplitudes of modulus at most 1 turns FC-P into a bound for
   populations. That step is not stated in this batch.
10. Numerical truth checks by the lead before the freeze, in ball arithmetic, by two methods that share no formula
   (the kernels as defined against the matrix exponential of the graph Laplacian): results file under `numerics/`.
   These are tooling, not evidence.

## The Lean text of the draft (compiles; not in the library)

```lean
import OscInt.Statements.PeriodicAnalytic

/-!
# Batch FR: the Schrödinger group on a ring of `N` sites and on an open chain of `M` sites (statements only)

Mathematics: `docs/statements.md`, "Batch FR". Written, stamped and blind-reviewed before any Lean proof of these
statements exists (`CONTRIBUTING.md`; `docs/lessons.md`, rule 1).

The equation is `i u′ + Δu = 0` with `(Δu)(x) = u(x + 1) + u(x − 1) − 2u(x)`, as in batch LS, on three graphs: the
line `ℤ` (kernel `lineKernel`, batch LS in one dimension), the ring `ℤ/N` (functions on `ℤ` of period `N`; kernel
`ringKernel`) and the open chain of the sites `1, …, M` with the Dirichlet condition `u(0) = u(M + 1) = 0`
(kernel `chainKernel`).
* FR-K `RingKernelStatement`: the ring kernel solves the equation in the site variable, is the unit datum at time 0
  and has period `N`.
* FR-U `RingUniqueStatement`: every solution of period `N` is the kernel sum of its datum over one period.
* FR-S `RingCosetSumStatement`: the ring kernel is the line kernel summed over a coset of `Nℤ` (method of images).
* FR-P `RingFiniteSizeStatement`: `|R_N(t, r) − G(t, r)| ≤ 2 e^{2|t| sinh η} cosh(rη) / (e^{ηN} − 1)` for every `η > 0`.
* FC-K `ChainKernelStatement`: the chain kernel solves the equation, vanishes at the two walls and is the unit datum.
* FC-U `ChainUniqueStatement`: every solution on the chain is the kernel sum of its datum.
* FC-P `ChainFiniteSizeStatement`: the chain kernel is the line kernel up to the two nearest images:
  `|C_M(t; x, y) − G(t, x − y)| ≤ e^{2|t| sinh η} (e^{−(x+y)η} + 2 (cosh((x−y)η) + cosh((x+y)η)) / (e^{2(M+1)η} − 1))`.

Modelling choices: sites are integers; a function on the ring is a function on `ℤ` of period `N`; a function on the
chain is a function on `ℤ` constrained at `0, …, M + 1` only; time derivatives are taken site by site
(`HasDerivAt` of `s ↦ u s x`), which for finitely many sites is the derivative of the vector.
-/

namespace OscInt.Statements

/-- The kernel of `i u′ + Δu = 0` on the line `ℤ`: `G(t, n) = (2π)^{−1} e^{−2it} I(2t, n)`. -/
noncomputable def lineKernel (t : ℝ) (n : ℤ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * Complex.exp (↑(-(2 * t)) * Complex.I) * latticeKernel1 (2 * t) (n : ℝ)

/-- The kernel on the ring of `N` sites: `R_N(t, r) = N^{−1} Σ_{j<N} e^{i(2t(cos k_j − 1) + r k_j)}`, `k_j = 2πj/N`. -/
noncomputable def ringKernel (N : ℕ) (t : ℝ) (r : ℤ) : ℂ :=
  ((N : ℝ) : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
    Complex.exp (↑(2 * t * (Real.cos (2 * Real.pi * (j : ℝ) / (N : ℝ)) - 1) +
      (r : ℝ) * (2 * Real.pi * (j : ℝ) / (N : ℝ))) * Complex.I)

/-- The kernel on the open chain of the sites `1, …, M`: the odd reflection of the ring of `2(M + 1)` sites,
`C_M(t; x, y) = R_{2(M+1)}(t, x − y) − R_{2(M+1)}(t, x + y)`. -/
noncomputable def chainKernel (M : ℕ) (t : ℝ) (x y : ℤ) : ℂ :=
  ringKernel (2 * (M + 1)) t (x - y) - ringKernel (2 * (M + 1)) t (x + y)

/-- **FR-K** The ring kernel solves `i ∂_t R + ΔR = 0` in the site variable, equals the unit datum of the ring at
`t = 0` (1 on `Nℤ`, 0 elsewhere) and has period `N`. -/
def RingKernelStatement : Prop :=
  ∀ (N : ℕ) (t : ℝ) (r : ℤ), 0 < N →
    HasDerivAt (fun s : ℝ => ringKernel N s r)
      (Complex.I * (ringKernel N t (r + 1) + ringKernel N t (r - 1) - 2 * ringKernel N t r)) t ∧
    ringKernel N 0 r = (if (N : ℤ) ∣ r then 1 else 0) ∧
    ringKernel N t (r + (N : ℤ)) = ringKernel N t r

theorem statement_pin_RingKernel : RingKernelStatement = RingKernelStatement := rfl

/-- **FR-U** Every solution of period `N` of `i u′ + Δu = 0` is the kernel sum of its datum over one period:
`u(t, x) = Σ_{y<N} R_N(t, x − y) u(0, y)`. -/
def RingUniqueStatement : Prop :=
  ∀ (N : ℕ) (u : ℝ → ℤ → ℂ), 0 < N → (∀ (t : ℝ) (x : ℤ), u t (x + (N : ℤ)) = u t x) →
    (∀ (t : ℝ) (x : ℤ), HasDerivAt (fun s : ℝ => u s x) (Complex.I * (u t (x + 1) + u t (x - 1) - 2 * u t x)) t) →
    ∀ (t : ℝ) (x : ℤ), u t x = ∑ y ∈ Finset.range N, ringKernel N t (x - (y : ℤ)) * u 0 (y : ℤ)

theorem statement_pin_RingUnique : RingUniqueStatement = RingUniqueStatement := rfl

/-- **FR-S** Method of images: the ring kernel is the line kernel summed over the coset `r + Nℤ`. -/
def RingCosetSumStatement : Prop :=
  ∀ (N : ℕ) (t : ℝ) (r : ℤ), 0 < N →
    HasSum (fun m : ℤ => lineKernel t (r + m * (N : ℤ))) (ringKernel N t r)

theorem statement_pin_RingCosetSum : RingCosetSumStatement = RingCosetSumStatement := rfl

/-- **FR-P** Finite-size error of the ring: `|R_N(t, r) − G(t, r)| ≤ 2 e^{2|t| sinh η} cosh(rη) / (e^{ηN} − 1)` for every
`η > 0`. -/
def RingFiniteSizeStatement : Prop :=
  ∀ (N : ℕ) (t η : ℝ) (r : ℤ), 0 < N → 0 < η →
    ‖ringKernel N t r - lineKernel t r‖ ≤
      2 * Real.exp (2 * |t| * Real.sinh η) * Real.cosh ((r : ℝ) * η) / (Real.exp (η * (N : ℝ)) - 1)

theorem statement_pin_RingFiniteSize : RingFiniteSizeStatement = RingFiniteSizeStatement := rfl

/-- **FC-K** The chain kernel solves the equation in the site variable, vanishes at the walls `x = 0` and
`x = M + 1`, and is the unit datum at `t = 0` on the sites `1, …, M`. -/
def ChainKernelStatement : Prop :=
  ∀ (M : ℕ) (t : ℝ) (x y : ℤ), 1 ≤ y → y ≤ (M : ℤ) →
    HasDerivAt (fun s : ℝ => chainKernel M s x y)
      (Complex.I * (chainKernel M t (x + 1) y + chainKernel M t (x - 1) y - 2 * chainKernel M t x y)) t ∧
    chainKernel M t 0 y = 0 ∧ chainKernel M t ((M : ℤ) + 1) y = 0 ∧
    (1 ≤ x → x ≤ (M : ℤ) → chainKernel M 0 x y = (if x = y then 1 else 0))

theorem statement_pin_ChainKernel : ChainKernelStatement = ChainKernelStatement := rfl

/-- **FC-U** Every solution of `i u′ + Δu = 0` on the open chain `1, …, M` with `u = 0` at the walls `0` and `M + 1`
is the kernel sum of its datum: `u(t, x) = Σ_{y=1}^{M} C_M(t; x, y) u(0, y)`. -/
def ChainUniqueStatement : Prop :=
  ∀ (M : ℕ) (u : ℝ → ℤ → ℂ), (∀ t : ℝ, u t 0 = 0 ∧ u t ((M : ℤ) + 1) = 0) →
    (∀ (t : ℝ) (x : ℤ), 1 ≤ x → x ≤ (M : ℤ) →
      HasDerivAt (fun s : ℝ => u s x) (Complex.I * (u t (x + 1) + u t (x - 1) - 2 * u t x)) t) →
    ∀ (t : ℝ) (x : ℤ), 1 ≤ x → x ≤ (M : ℤ) →
      u t x = ∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), chainKernel M t x y * u 0 y

theorem statement_pin_ChainUnique : ChainUniqueStatement = ChainUniqueStatement := rfl

/-- **FC-P** Finite-size error of the open chain: for sites `1 ≤ x, y ≤ M` and every `η > 0`,
`|C_M(t; x, y) − G(t, x − y)| ≤ e^{2|t| sinh η} (e^{−(x+y)η} + 2 (cosh((x−y)η) + cosh((x+y)η)) / (e^{2(M+1)η} − 1))`. -/
def ChainFiniteSizeStatement : Prop :=
  ∀ (M : ℕ) (t η : ℝ) (x y : ℤ), 0 < η → 1 ≤ x → x ≤ (M : ℤ) → 1 ≤ y → y ≤ (M : ℤ) →
    ‖chainKernel M t x y - lineKernel t (x - y)‖ ≤
      Real.exp (2 * |t| * Real.sinh η) *
        (Real.exp (-(((x + y : ℤ) : ℝ) * η)) +
          2 * (Real.cosh (((x - y : ℤ) : ℝ) * η) + Real.cosh (((x + y : ℤ) : ℝ) * η)) /
            (Real.exp (2 * ((M : ℝ) + 1) * η) - 1))

theorem statement_pin_ChainFiniteSize : ChainFiniteSizeStatement = ChainFiniteSizeStatement := rfl

end OscInt.Statements
```

## Prior art, first pass

Batch FR prior-art sweep, first pass (2026-11-16, lead, two standard web searches; results pages only, no repository
or paper opened):
- Query 1: Lean 4 / Mathlib formalisation of the continuous-time quantum walk on a cycle, propagator, Bessel, method
  of images, periodisation. Closest hit: github.com/emberian/graphplay (Lean 4; equitable-partition quotients of
  quantum walks, perfect state transfer, continuous-time search on K_n; per the search summary no cycle graph, Bessel
  function or images). Also inQWIRE/LeanQuantum (quantum information; not graph walks).
- Query 2: Lean / Isabelle / Coq, discrete Schrödinger equation on a finite chain with Dirichlet ends, sine transform,
  reflection. No formalisation found; analytic papers only (arXiv:2008.03698, arXiv:2608.05338, arXiv:2411.14397).
- Mathlib itself has the discrete Fourier transform on ZMod N (Mathlib/Analysis/Fourier/ZMod.lean): to be read
  before the freeze; the ring kernel is a DFT of the symbol, so FR-K may be close to existing lemmas.
Label: PLAUSIBLE-not-formalised (absence of a hit in two searches is not evidence of novelty). To do before the
freeze: open graphplay's file list; search the Isabelle AFP and Lean Zulip for "circulant", "quantum walk".
