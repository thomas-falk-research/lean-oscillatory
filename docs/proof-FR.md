<!--
SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>

SPDX-License-Identifier: CC-BY-4.0
-->

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

## Revision after the route referee (2026-11-16)

The route referee read the route as committed in 6ef8939 (verdict: sound after corrections; no BLOCKER, no MAJOR;
`review/2026-11-16-FR-route-answers.md`). The text above is the reviewed text and is left as it was; these items
override it.
1. Part F-coset, the modulus of v: the display should read |v(z)| = e^{2t sin x sinh y − ry} (the route has the wrong
   sign in front of 2t). The bound e^{2|t| sinh 1 + |r|} is unaffected. An error of the lead.
2. Part F-coset is proved without computing that modulus: v(z) = e^{−2it} · e^{i(2t) cos z} · e^{irz}, with the bound of
   the middle factor from the library (`kernelIntegrand_norm_le`) and |e^{irz}| = e^{−r Im z} ≤ e^{|r|}. The constant is
   then e^{|2t| sinh 1} · e^{|r|}; it does not appear in the statement.
3. Part F-even at N = 0: both sides are 0 in Lean ((0 : ℂ)⁻¹ = 0 and an empty sum); the route's re-indexing covers N ≥ 1.
4. Feasibility notes taken over: F-images needs a majorant with the constants A e^{−rη} and A e^{rη} on the two sides
   (two geometric series); the energy arguments use the complex form Σ conj(w_x) w_x.
5. Header: the sentence about referee B's remark and F-images says nothing and is withdrawn. What is true: for the
   extremal sequence g(n) = A e^{−|n|η} the bound of F-images is an equality whenever |r| ≤ N, which is consistent with
   FR-P being nearly attained along r = ±N.

## Parts as integrated (2026-11-16)

Five proof agents (AI agents of the same model family as the lead), one per part, were launched together after the
route referee had reported (the SHA-256 of each brief is in the session log). Each worked in the lead's scratch
from the blueprint, this route, the referee's notes and its brief, and wrote one Lean file; none wrote in the
repository. The lead recompiled each file with its final theorems ascribed to the blueprint proposition or frozen
statement, printed the axioms (all: propext, Classical.choice, Quot.sound), compiled all five files with the
assembly and the seven final theorems as one scratch file, and copied the files in unchanged.

| Part | File | Lines | SHA-256 of the file as delivered | Deviations from the route (agent's report, in the lead's words) |
|---|---|---|---|---|
| FR1 `RingKernelStatement`, `RingEvenFacts` | `OscInt/Front/FiniteRingKernel.lean` | 175 | 305673387aed7fba69423eacdf67dd8c39de79d9bd6cf07559c747b782ed19d4 | the equation is proved for every N; evenness re-indexes the whole range j ↦ N − j with "mode N = mode 0" instead of keeping j = 0 apart; the period uses the integer-multiple-of-2πi lemma directly |
| FR2 `RingCosetSumStatement` | `OscInt/Front/FiniteRingCoset.lean` | 140 | 52000d9ad8be686071bf250235e1c333afc83cd3e0bc94bbbd6cf90e0c7bdbf2 | none in substance; the referee's cheaper path (revision, item 2); one new definition, the function v |
| FR3 `ImageSumFacts` | `OscInt/Front/FiniteRingImages.lean` | 128 | f63461c3723c503d3ef508e37f30e00151d410b0df92b14993d0859be168ccab | none |
| FR4 `RingDatumFacts`, `RingEnergyFacts` | `OscInt/Front/FiniteRingEnergy.lean` | 154 | 93378c571f697861d25b2d33c5123777a5a8bd76886d75ecc977a5fd49492e3d | complex energy; the derivative of each term is written as i (F(x) − F(x + 1)) and summed with one shift lemma, instead of matching two sums as complex conjugates |
| FR5 `ChainEnergyFacts` | `OscInt/Front/FiniteRingChainEnergy.lean` | 124 | 861b0acb46177c368b1e1185cb1951e7b56b75779270baf42c74d40e9e9126bc | complex energy over the sites k + 1, k < M; the derivative of each term is i (J(x) − J(x − 1)) with the current J(x) = conj(w_x) w_{x+1} − conj(w_{x+1}) w_x, which telescopes to the two walls |

Agents' slips against their briefs, as they reported them: two proof agents (FR3, FR4) each ran one read-only
`git status` inside the repository; nothing was written there (the lead's `git status` after each report: clean).
Four agents left no report file (the harness refused it for three, who returned the report as text; the fourth,
FR3, named a report file that does not exist, and its final message is its whole report); only FR4 wrote one.

Final theorems: `OscInt/Front/FiniteRingFinal.lean`.
Checks by the lead at integration (2026-11-17, `docs/replay/2026-11-17-FR-integration-checks.txt`): `lake build`
completed; `StatementTypes.lean` asserts the seven types (78 lines TYPE-OK); `leanchecker` on each of the eleven FR
modules (statements, two sanity layers, blueprint, assembly, five parts, final): exit code 0; the axioms of the seven
final theorems are in the audit of `make quick`. Not yet done at this point: the post-proof reviews and the isolated
replay.
