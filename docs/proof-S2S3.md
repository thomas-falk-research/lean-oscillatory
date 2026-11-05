# On-paper proof of S2.1, S2.2, S3 (route for the blueprint)

Status: written by the lead (2026-11-05), not yet refereed. Every step names the Lean lemma or blueprint part that
will carry it. Notation as in `docs/statements.md` S2/S3. "Family" means a family of class Cⁿ over a compact space.
Constants C may change from line to line and depend only on the data fixed before A, M, σ, p, m.

## 0. Reductions

(R1) Linear term as family parameter. For S2.2 and S3 put T = Λ × K′ (Λ a point for S2.2) and Q_τ(k) = Ψ_σ(k) + p·k
for τ = (σ, p). T is compact, Q is a family of class C⁴ (adding a linear function changes the first derivative by p
and nothing else, so joint continuity persists), and Hessians and third derivatives of Q_τ equal those of Ψ_σ.
The hypotheses become: for every (τ, k) ∈ T × K, (i) ∇Q_τ(k) ≠ 0, or (ii) ∇Q_τ(k) = 0 and det D²Q_τ(k) ≠ 0, or
(iii) [S3 only] ∇Q_τ(k) = 0 and D²Q_τ(k) has rank one with D³Q_τ(k)[v,v,v] ≠ 0 on its kernel.
(For S3 the hypothesis is FoldOrNondeg at every point, which covers (ii) and (iii) at critical points; at
non-critical points (i) holds.) It suffices to show I(mQ_τ, A) = O(M m^{-r}) uniformly in τ ∈ T, r = 1 (S2.2),
r = 5/6 (S3). [Part F1: family algebra.]

(R2) Localisation. Suppose every (τ₀, k₀) ∈ T × K has a neighbourhood U × B(k₀, δ) (U open in T, δ > 0) and a
constant C such that |I(mQ_τ, B)| ≤ C M′ m^{-r} for all τ ∈ U and all B with amplitude bound (2, B̄(k₀, δ), M′).
Then the global bound holds. Proof: finitely many U_i × B(k_i, δ_i/2) cover T × K (compactness). For each subset S
of the index set whose balls B(k_i, δ_i/2), i ∈ S, cover K, fix a smooth partition of unity (χ_i^S)_{i∈S} on a
neighbourhood of K, subordinate to B(k_i, δ_i) (exists: smooth bumps, finite cover). There are finitely many S.
Given τ, let S(τ) = {i : τ ∈ U_i}; the balls with i ∈ S(τ) cover K (every (τ, k) lies in some U_i × B(k_i, δ_i/2)).
Write A = Σ_{i∈S(τ)} χ_i^{S(τ)} A; each term has amplitude bound (2, B̄(k_i, δ_i), C_S M) by the Leibniz rule
(derivatives of χ up to order 2 are bounded, finitely many χ's). Sum the local bounds. [Part F2: localisation.]

## 1. Local estimates

Fix (τ₀, k₀) ∈ T × K. Write Q = Q_τ. Every local step below uses the hypothesis only at the single point
(τ₀, k₀) and obtains everything it needs on a neighbourhood U × B(k₀, δ) by joint continuity; points of that
neighbourhood may lie outside K (referee B, S2/S3 pre-proof review), and no hypothesis is used there.

(L1) Non-critical point, ∇Q_{τ₀}(k₀) ≠ 0. Choose a unit coordinate direction e (e₁ or e₂) with ∂_eQ_{τ₀}(k₀) ≠ 0.
By joint continuity there are U, δ with |∂_eQ_τ| ≥ c > 0 on U × B̄(k₀, 2δ). For B supported in B̄(k₀, δ):
e^{imQ}B = (1/(im)) ∂_e(e^{imQ}) B/∂_eQ, and integration by parts in the direction e (Mathlib
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, all functions compactly supported and C¹) gives
|I| ≤ (1/m) ∫ |∂_e(B/∂_eQ)| ≤ C M′/m, with C from sup over U × B̄ of |∂_eQ|^{-1}, |∂²_eQ| (compactness: shrink U to a
compact neighbourhood or use continuity at τ₀ to get bounds on U). Rate 1. [Part L1; also S2.1 with N = 1.]

(L2) Critical point, normal form. Suppose ∇Q_{τ₀}(k₀) = 0 and D²Q_{τ₀}(k₀) ≠ 0. Choose a linear isomorphism L of
ℝ² with L e₂ = w where D²Q_{τ₀}(k₀)[w, w] ≠ 0, and L e₁ = v where: in case (ii) v is any vector with
D²Q(k₀)[v, w] = 0 (so the reduced Hessian below is det D²Q / D²Q[w,w] ≠ 0); in case (iii) v spans the kernel (then
D²Q[v, w] = 0 automatically and D²Q[w, w] ≠ 0 since w ∉ kernel). Replace Q by Q∘(k₀ + L·) and A by A∘(k₀ + L·)
times |det L| (change of variables; amplitude bounds change by constants depending on L only). In the new
coordinates k = (x, y), at the origin and τ = τ₀:
  ∂_yQ = 0, ∂_x Q = 0, ∂²_yQ ≠ 0, ∂_x∂_yQ = 0, and (ii) ∂²_xQ ≠ 0, or (iii) ∂²_xQ = 0, ∂³_xQ ≠ 0.
[Part L2: linear change of variables for oscInt2 and amplitude bounds; choice of L.]

(L3) Implicit critical point. By the implicit function theorem with parameter (τ, x) applied to F(τ, x, y) =
∂_yQ_τ(x, y) (C³ in (x, y), F_y ≠ 0 at (τ₀, 0, 0), all x,y-derivatives jointly continuous in τ): there are U, a, b,
μ > 0 and a function y*(τ, x) on U × [−a, a] with values in (−b, b) such that
  (a) |∂²_yQ_τ| ≥ μ on U × [−2a, 2a] × [−2b, 2b];
  (b) ∂_yQ_τ(x, y) = 0 for (x, y) ∈ [−a, a] × [−b, b] iff y = y*(τ, x);
  (c) x ↦ y*(τ, x) is C³ on (−2a, 2a) with derivatives up to order 3 jointly continuous in (τ, x).
Uniqueness in (b) is by strict monotonicity of y ↦ ∂_yQ (from (a)). Existence and continuity: the fixed point of
the contraction y ↦ y − ∂_yQ_τ(x, y)/∂²_yQ_{τ₀}(0, 0) on [−b, b] (Banach fixed point with a parameter, continuous
in the parameter: `ContractingWith.fixedPoint`, `fixedPoint_lipschitz_in_map`); differentiability in x: from the
classical implicit function theorem at each (τ, x) (`ImplicitFunctionData` / `implicitFunctionOfBivariate`) and
uniqueness; derivative formulas y*′ = −∂_x∂_yQ/∂²_yQ (evaluated at (x, y*)), and differentiating again.
[Part L3: implicit critical point with a topological parameter.]

(L4) Reduced phase. g_τ(x) = Q_τ(x, y*(τ, x)). Then g′ = ∂_xQ(x, y*) (since ∂_yQ(x, y*) = 0), g″ = ∂²_xQ +
∂_x∂_yQ · y*′ = (∂²_xQ ∂²_yQ − (∂_x∂_yQ)²)/∂²_yQ at (x, y*), g‴ = ∂_x of that. At (τ₀, 0): y*′ = 0, so
g″ = ∂²_xQ(0) and g‴ = ∂³_xQ(0) (the other terms carry y*′(0) = 0 or ∂_x∂_yQ(0) = 0). Hence in case (ii)
|g″| ≥ ν > 0 and in case (iii) |g‴| ≥ ν > 0 on U × [−a, a] after shrinking (joint continuity). [Part L4.]

(L5) Hadamard factorisation. For (x, y) ∈ [−a, a] × [−b, b]:
  ∂_yQ(x, y) = (y − y*) h(x, y),  h = ∫₀¹ ∂²_yQ(x, y* + s(y − y*)) ds,
  Q(x, y) − g(x) = (y − y*)² H(x, y),  H = ∫₀¹ (1 − s) ∂²_yQ(x, y* + s(y − y*)) ds.
Both h and H are C² in (x, y) (Q ∈ C⁴, y* ∈ C³; differentiation under the integral over s ∈ [0, 1]), with
|h| ≥ μ, |H| ≥ μ/2, and derivatives up to order 2 bounded uniformly in τ ∈ U. [Part L5: Taylor/Hadamard with a
parameter, regularity of parametric integrals.]

(L6) The estimate. Let B be supported in R = [−a, a] × [−b, b] with amplitude bound (2, R, M′). Decompose
B(x, y) = B(x, y*) + (y − y*) E(x, y), E = ∫₀¹ ∂_yB(x, y* + s(y − y*)) ds (C¹, |E|, |∂E| ≤ C M′). Fix a smooth
cutoff θ(y) equal to 1 on [−b, b], supported in [−2b, 2b]. The identity B(x, y) = B(x, y*) + (y − y*)E(x, y) holds for
all y (fundamental theorem of calculus on the segment; B is C² on ℝ²), and B = θB because supp B ⊆ R, so
B = θ(y)B(x, y*) + θ(y)(y − y*)E(x, y). The factors h, K below are taken on [−a, a] × [−2b, 2b], where the segment
from y* ∈ (−b, b) to y stays in [−2b, 2b] and (L3)(a) gives |h| ≥ μ.
 (L6a) Second term: (y − y*) e^{imQ} = ∂_y(e^{imQ})/(im h). Integrating by parts in y (for each x; or in the
 direction e₂ on ℝ²): |∫∫ e^{imQ} θ (y − y*) E| = (1/m)|∫∫ e^{imQ} ∂_y(θE/h)| ≤ C M′/m.
 (L6b) First term: J_τ(x) = ∫ e^{im(Q(x,y) − g(x))} θ(y) dy, so the term is ∫ e^{img(x)} B(x, y*(x)) J(x) dx with
 b(x) = B(x, y*(x)) supported in [−a, a], C¹, |b|, |b′| ≤ C M′.
   (i) |J(x)| ≤ 8 (mμ)^{-1/2} · (1 + ∫|θ′|) by S1.2 in y (|∂²_y(Q − g)| = |∂²_yQ| ≥ μ on [−2b, 2b]).
   (ii) J′(x) = ∫ e^{im(Q−g)} im ∂_x(Q − g) θ dy. Since ∂_x(Q − g) = ∂_xQ(x, y) − ∂_xQ(x, y*) = (y − y*)K(x, y)
   with K = ∫₀¹ ∂_y∂_xQ(x, y* + s(y − y*)) ds ∈ C², and ∂_y(Q − g) = (y − y*) h, we get
   im (y − y*) e^{im(Q−g)} = ∂_y(e^{im(Q−g)})/h, so J′(x) = ∫ ∂_y(e^{im(Q−g)}) K θ/h dy
   = −∫ e^{im(Q−g)} ∂_y(Kθ/h) dy, and by S1.2 in y with amplitude ∂_y(Kθ/h) (C¹ in y):
   |J′(x)| ≤ C (mμ)^{-1/2}.
   (iii) By S1.2 (case ii) or S1.3 (case iii) in x with phase m g_τ and amplitude bJ on [−a, a]:
   |∫ e^{img} b J dx| ≤ c_j (mν)^{-1/j} (|b(a)J(a)| + ∫ |(bJ)′|) ≤ C M′ m^{-1/j} m^{-1/2},
   j = 2 (case ii) or 3 (case iii). (b(±a) = 0: B is continuous and vanishes outside R, hence on ∂R.)
 Total: C M′ (m^{-1} + m^{-1/2 - 1/j}) = O(M′ m^{-1}) in case (ii), O(M′ m^{-5/6}) in case (iii) (m ≥ 1).
 [Part L6: the analytic core; uses S1.2, S1.3, 1D integration by parts, Fubini on rectangles.]

## 2. S2.1 (non-stationary, order N)

(N1) Compactification of the linear term. Let G = sup{|∇Ψ_σ(k)| : σ ∈ Λ, k ∈ K} and R = 2G + 2c + 1. For |p| ≤ R
use the compact family over T = {(σ, p) ∈ Λ × B̄(0, R) : |∇Ψ_σ(k) + p| ≥ c for all k ∈ K} (closed in a compact
set, so compact) as in (R1). For |p| > R write p = |p| u, |u| = 1, s = 1/|p| ∈ (0, 1/R):
m(Ψ_σ + p·k) = (m/s)(sΨ_σ + u·k), with m/s ≥ m and the family (σ, s, u) ↦ sΨ_σ + u·(·) over the compact
Λ × [0, 1/R] × S¹ of class C^{N+1}, with |∇| ≥ 1 − sG ≥ 1/2 on K. A bound C M (m/s)^{-N} ≤ C M m^{-N} follows.
(N2) Compact non-stationary family, order N, by induction. Let Φ_τ (τ ∈ T compact) be of class C^{N+1} with
|∇Φ_τ| ≥ c on a compact neighbourhood K₁ of K (exists by joint continuity of ∇Φ). With w_τ = ∇Φ_τ/|∇Φ_τ|²
(C^N on a neighbourhood of K₁, derivatives jointly continuous in (τ, k) [Part F1: family algebra closed under
composition with smooth maps on open sets]), e^{imΦ} = (1/(im)) w·∇e^{imΦ}, so I(mΦ, A) = (i/m) I(mΦ, div(wA)).
div(w_τ A) is C^{N-1}, supported in K, with derivative bounds C M (Leibniz, sup over T × K₁ of derivatives of w).
Induct (N − 1 → N), base N = 0: |I| ≤ ∫|A| ≤ |K| M. [Part N.]

## 3. Assembly

S2.1 from (N1), (N2). S2.2 from (R1), (R2), (L1), (L2)–(L6) case (ii) (S2.2's hypothesis gives (i) or (ii) at
every point of K for every τ ∈ T). S3 from (R1), (R2), (L1), (L2)–(L6) cases (ii) and (iii).

## Known weak points (to be checked by the referee before encoding)

- (L6b)(iii) needs bJ to satisfy the amplitude hypothesis of S1 (ψ continuous on [−a, a], derivative on the open
  interval, derivative integrable): J is C¹ in x by differentiation under the integral (θ compactly supported,
  integrand C¹ in x with bounded derivative).
- (L3) The implicit function theorem with a merely topological parameter τ: Mathlib's IFT needs a normed-space
  parameter; the contraction route gives continuity in τ; differentiability in x uses the classical IFT at fixed
  τ. Derivatives of y* in x must be jointly continuous in (τ, x): from the explicit formulas.
- (R2) Partitions of unity on ℝ² subordinate to finite ball covers: Mathlib (`SmoothPartitionOfUnity` on a normed
  space as a manifold, or `exists_contDiff_support_eq_eq_one_iff`) with explicit derivative bounds by compactness.
