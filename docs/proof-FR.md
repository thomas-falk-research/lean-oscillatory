# Proof route for batch FR (FR-K, FR-U, FR-S, FR-P, FC-K, FC-U, FC-P)

Written by the lead on paper at 2026-11-16T20:46Z, after the statements commit 0748dde and while its stamp was being
made, before the blind pre-proof reviews; kept outside the repository until the review answers were stamped
(`stamps/20261116T225756Z-5792039264f0`, 22:58:03Z; rule 1). An outline of the same dependencies is older than the
freeze (`docs/design/batch-FR-draft.md`, committed in 0302925), and the derivations of FR-P and FC-P below were
worked out by the lead while drafting the statements. Statements: `docs/statements.md`, Batch FR; Lean text
`OscInt/Statements/FiniteRing.lean`. The mathematics is classical. Status of this page: a route on paper, to be
read by a route referee before the parts are proved; not a proof record. Changes after the stamp of the answers
(2026-11-16, when the blueprint was written): the datum step of F-unique became a blueprint proposition of its own
(`RingDatumFacts`), and F-line is an assembly lemma, not a blueprint proposition. Referee B's remark that FR-P is
nearly attained along r = ±N was checked against F-images: its majorant sums to exactly the right side.

Notation: N ≥ 1; θ_j = 2πj/N; λ_j = 2(cos θ_j − 1); the mode m_j(t, r) = e^{i(tλ_j + rθ_j)}, so that
R_N(t, r) = N^{−1} Σ_{j<N} m_j(t, r). G(t, n) = (2π)^{−1} e^{−2it} I(2t, n) is the line kernel. E = e^{2|t| sinh η}.

## Part F-kernel (FR-K)
(a) ∂_t m_j = iλ_j m_j, and m_j(t, r+1) + m_j(t, r−1) − 2m_j(t, r) = (e^{iθ_j} + e^{−iθ_j} − 2) m_j(t, r) = λ_j m_j(t, r).
Summing over j: ∂_t R = i (R(r+1) + R(r−1) − 2R(r)). A finite sum; no interchange of limits.
(b) R_N(0, r) = N^{−1} Σ_{j<N} e^{irθ_j}: each term is 1 if N | r; the sum is 0 if N ∤ r (roots of unity; the two
lemmas `alias_exp_mul_eq_one` and `alias_sum_exp_eq_zero` of `OscInt/Front/PeriodicAnalyticAlias.lean` are exactly
these, in the shape `exp (↑(k * (2π j / N)) * I)`).
(c) m_j(t, r + N) = m_j(t, r) e^{iNθ_j} = m_j(t, r) e^{2πij} = m_j(t, r).

## Part F-even (the ring kernel is even in r)
θ_{N−j} = 2π − θ_j for 1 ≤ j ≤ N − 1, so cos θ_{N−j} = cos θ_j and e^{irθ_{N−j}} = e^{−irθ_j} (r an integer). Hence
m_{N−j}(t, r) = m_j(t, −r), and m_0(t, −r) = m_0(t, r) = 1. Re-indexing j ↦ N − j on 1, …, N − 1 gives
R_N(t, −r) = R_N(t, r).

## Part F-coset (FR-S)
Fix t and r and put v(z) = e^{i(2t(cos z − 1) + rz)}, entire and 2π-periodic (r is an integer). On the strip
|Im z| < 1, |v(z)| = e^{−2t sin x sinh y − ry} ≤ e^{2|t| sinh 1 + |r|} (z = x + iy), so v is periodic-analytic there.
Its Fourier integrals: ∫_0^{2π} v(θ) e^{−ikθ} dθ = e^{−2it} ∫_0^{2π} e^{i(2t cos θ + (r − k)θ)} dθ = e^{−2it} I(2t, r − k)
(the last by periodicity of the integrand, as in `kernelIntegrand_latticeKernel1_eq`), so the normalised
coefficient is c_k = G(t, r − k). By PA-C the coefficients satisfy the bound that `fourierSeriesFacts` asks for, so
for every real x, Σ_k c_k e^{ikx} = v(x) (HasSum). At the N points θ_j, `alias_hasSum_multiples` gives
Σ_m N c_{mN} = Σ_{j<N} v(θ_j) (HasSum over m ∈ ℤ). Since v(θ_j) = m_j(t, r): Σ_m G(t, r − mN) = R_N(t, r), and the
substitution m ↦ −m gives FR-S.

## Part F-line (the line kernel outside the light cone)
‖G(t, n)‖ = (2π)^{−1} ‖I(2t, n)‖ ≤ e^{2|t| sinh η − |n| η} for every η ≥ 0, by LC-1 at time 2t (|2t| = 2|t|).

## Part F-images (a statement about series, no kernel in it)
Let g : ℤ → ℂ with ‖g(n)‖ ≤ A e^{−|n| η} for all n, A ≥ 0, η > 0, N ≥ 1, and suppose Σ_m g(r + mN) = S (HasSum).
Then ‖S − g(r)‖ ≤ 2A cosh(rη) / (e^{ηN} − 1).
Proof. S − g(r) is the sum over m ≠ 0. For m ≥ 1, |r + mN| ≥ r + mN, so ‖g(r + mN)‖ ≤ A e^{−rη} q^m with q = e^{−ηN};
for m ≤ −1, |r + mN| ≥ −r + |m|N, so ‖g(r + mN)‖ ≤ A e^{rη} q^{|m|}. The majorant sums to
A (e^{−rη} + e^{rη}) q/(1 − q) = 2A cosh(rη)/(e^{ηN} − 1). (No assumption on the size of r: |x| ≥ ±x is all that is used.)

## Part F-size (FR-P): F-coset, F-line with A = E, F-images with g = G(t, ·). ∎

## Part F-unique (FR-U)
Let w(t, x) = u(t, x) − Σ_{y<N} R_N(t, x − y) u(0, y). Then: w has period N in x (u has, and R has by FR-K(c)); w
solves the equation site by site (linear; FR-K(a) at r = x − y); and w(0, x) = u(0, x) − Σ_{y<N} [N | x − y] u(0, y)
= u(0, x) − u(0, y_x) = 0, where y_x is the residue of x in [0, N) and u(0, ·) has period N (so u(0, x + kN) = u(0, x)
for every integer k, by induction on |k|).
Energy. Let e(t) = Σ_{x<N} |w(t, x)|². Then e′(t) = Σ_{x<N} 2 Re( conj(w_x) · i (w_{x+1} + w_{x−1} − 2w_x) ). By
periodicity Σ_{x<N} conj(w_x) w_{x−1} = Σ_{x<N} conj(w_{x+1}) w_x, the complex conjugate of Σ_{x<N} conj(w_x) w_{x+1}; so
Σ_x conj(w_x)(w_{x+1} + w_{x−1} − 2w_x) is real and e′ = 0. A function with zero derivative everywhere is constant:
e(t) = e(0) = 0, so w(t, x) = 0 for 0 ≤ x < N and then for all x by periodicity.

## Part C-kernel (FC-K), with N = 2(M + 1)
(a) the equation: FR-K(a) at r = x − y and at r = x + y. (b) the wall x = 0: R(−y) − R(y) = 0 by F-even. (c) the wall
x = M + 1: M + 1 + y = −(M + 1 − y) + N, so R(M + 1 + y) = R(−(M + 1 − y)) = R(M + 1 − y) by FR-K(c) and F-even.
(d) t = 0 and 1 ≤ x, y ≤ M: N | x − y iff x = y (|x − y| < N), and N ∤ x + y (0 < x + y < N), so by FR-K(b) the value
is [x = y].

## Part C-unique (FC-U)
w(t, x) = u(t, x) − Σ_{y=1}^{M} C_M(t; x, y) u(0, y) for 0 ≤ x ≤ M + 1. It vanishes at x = 0 and x = M + 1 (hypothesis
on u; FC-K(b), (c)), solves the equation at 1 ≤ x ≤ M (FC-K(a) holds at every x), and w(0, x) = 0 for 1 ≤ x ≤ M
(FC-K(d)). Energy e(t) = Σ_{x=1}^{M} |w(t, x)|²: Σ_{x=1}^{M} conj(w_x) w_{x+1} = Σ_{x=1}^{M−1} conj(w_x) w_{x+1} (w_{M+1} = 0) and
Σ_{x=1}^{M} conj(w_x) w_{x−1} = Σ_{x=1}^{M−1} conj(w_{x+1}) w_x (w_0 = 0) are complex conjugates, so e′ = 0 and e = 0.

## Part C-size (FC-P)
C − G(x − y) = [R(x − y) − G(x − y)] − [R(x + y) − G(x + y)] − G(x + y). FR-P at r = x − y and r = x + y with N = 2(M + 1),
and F-line for G(x + y) with x + y > 0: the three terms are at most 2E cosh((x − y)η)/(e^{Nη} − 1),
2E cosh((x + y)η)/(e^{Nη} − 1) and E e^{−(x+y)η}.

## Blueprint and assembly (written after the review answers were stamped)
`Blueprint/FiniteRing.lean` (definitions only): `RingEvenFacts` (F-even), `ImageSumFacts` (F-images),
`RingDatumFacts` (the datum step of F-unique: Σ_{y<N} [N | x − y] f(y) = f(x) for f of period N), `RingEnergyFacts`
and `ChainEnergyFacts` (the two zero-solution statements). FR-K and FR-S are proved directly as parts.
Assembly by the lead, `OscInt/Front/FiniteRingAssembly.lean`, compiled before any part
(`lineKernel_norm_le`, `ringFiniteSize_of`, `ringUnique_of`, `chainKernel_of`, `chainUnique_of`,
`chainFiniteSize_of`): F-line from LC-1; FR-P from FR-S, F-line, F-images; FR-U from FR-K, the datum identity and
the ring energy fact; FC-K from FR-K and F-even; FC-U from FC-K and the chain energy fact; FC-P from FR-P and F-line.

Parts (one agent each, one Lean file each):
| Part | Proves | Uses |
|---|---|---|
| FR1 | `RingKernelStatement` (F-kernel), `RingEvenFacts` (F-even) | finite sums of exponentials; `alias_exp_mul_eq_one`, `alias_sum_exp_eq_zero` of `OscInt/Front/PeriodicAnalyticAlias.lean` |
| FR2 | `RingCosetSumStatement` (F-coset) | `OscInt.API.fourierCoeffStrip`, `fourierSeriesFacts`, `alias_hasSum_multiples`, the periodicity of the kernel integrand |
| FR3 | `ImageSumFacts` (F-images) | geometric series over ℤ ∖ {0} |
| FR4 | `RingDatumFacts`, `RingEnergyFacts` (F-unique) | residues modulo N; derivative of a finite sum of squared moduli |
| FR5 | `ChainEnergyFacts` (C-unique) | the same on the sites 1, …, M with the two walls |

## Risks
- F-coset: matching the shapes of `fourierSeriesFacts` and `alias_hasSum_multiples` (coefficients written as
  integrals; the coefficient at index k is G(t, r − k), so a reflection of the summation index is needed).
- The two energy arguments: derivative of a finite sum of squared moduli; index shifts in sums over a period and
  over 1, …, M; "zero derivative implies constant" on all of ℝ.
- F-even: the re-indexing j ↦ N − j on a `Finset.range`.
