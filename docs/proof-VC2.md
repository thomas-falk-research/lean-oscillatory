# Proof route for batch VC2 (VC2-S, VC2-A, VC2-N, VC2-K)

Written by the lead. History, disclosed: a proof on paper in the phase variable existed and was read by a step
referee before the statements were frozen (session log, 2026-11-16); the lead rewrote it in the variable x, without
an inverse function, on 2026-11-16 (file in the lead's scratch, last written 2026-11-16T21:40:51Z), also before the review
answers were stamped (`stamps/20261117T010311Z-a93c4e1e44f7`, 2026-11-17 01:03:18Z). The present page is that route
recast for the blueprint `Blueprint/SecondDerivSharp.lean`, written on 2026-11-17 after that stamp; in this form
(propositions V-root, V-head, V-tail, V-side with a general rate λ, and proofs by monotone comparison in place of
the fundamental theorem of calculus) it has not been refereed before. The theorem is classical (the sharp constant
is van der Corput's; `docs/prior_art.md`, batch VC2); nothing here is claimed as new. Status of this page: a route
on paper, to be read by a route referee; not a proof record.

Notation. A *side* is the blueprint's `Vdc2Side f f' c d λ`: c ≤ d, λ > 0, f continuous on [c, d], f′ its derivative
on (c, d), f′(y) − f′(x) ≥ λ(y − x) for c < x ≤ y < d, and f′ > 0 on (c, d). On a side f is strictly increasing on
[c, d] (continuous, positive derivative inside), and every [p, q] ⊆ [c, d] with p ≤ q is again a side
(`Vdc2Side.mono` in the assembly). A(w) = 2 ∫_0^{√(2w)} sin(w − u²/2) du is `vdc2Profile`.

One tool is used four times, in place of the fundamental theorem of calculus (no integrability of f′ is needed):
(M) if H is continuous on [p, q] and has a derivative ≥ 0 at every point of (p, q), then H(p) ≤ H(q)
(`monotoneOn_of_deriv_nonneg` on the convex set [p, q]). The primitives x ↦ ∫_p^x h, for h continuous on [p, q], are
continuous on [p, q] with derivative h(x) inside (as in `OscInt/VanDerCorput/Amplitude.lean`, `primitive_hasDerivOn`).

## V1. The turning point (`Vdc2TurningPointFacts`)
Let a ≤ b, λ > 0 and f′(y) − f′(x) ≥ λ(y − x) for a < x ≤ y < b. Put Z = {x ∈ (a, b) : f′(x) ≤ 0} and x₀ = sup Z, or
x₀ = a if Z is empty; x₀ ∈ [a, b]. If a < x < x₀, some z ∈ Z has x < z, and f′(x) ≤ f′(z) − λ(z − x) < 0. If x₀ < x < b,
then x ∉ Z, so f′(x) > 0. (If a = b both intervals are empty.)

## V2. The speed dominates the root of the phase (`Vdc2RootFacts`)
On a side, for c < x < d: 2λ(f(x) − f(c)) ≤ f′(x)².
Proof. Fix x, put h = f′(x) > 0 and G(y) = f(y) + h(x − y) − λ(x − y)²/2 on [c, x]. G is continuous on [c, x] and for
c < y < x: G′(y) = f′(y) − h + λ(x − y) ≤ 0, because f′(x) − f′(y) ≥ λ(x − y). By (M) for −G: G(x) ≤ G(c), that is
f(x) ≤ f(c) + h e − λe²/2 with e = x − c, so 2λ(f(x) − f(c)) ≤ 2λhe − λ²e² = h² − (h − λe)² ≤ h². ∎

## V3. A positive arc from the turning point (`Vdc2HeadFacts`)
On a side with 0 ≤ w ≤ π and f(d) − f(c) ≤ w: ∫_c^d sin(w − (f − f(c))) ≤ A(w)/(2√λ).
Proof. F = f − f(c): F(c) = 0, F strictly increasing, 0 ≤ F ≤ w on [c, d], F > 0 on (c, d]. Put
Γ(v) = ∫_0^{√(2v)} sin(w − u²/2) du for v ≥ 0 and H(x) = Γ(F(x))/√λ − ∫_c^x sin(w − F). H is continuous on [c, d]
(√ and the primitive are continuous) and H(c) = 0. At c < x < d, with v = F(x) > 0: Γ′(v) = sin(w − v)/√(2v) (chain
rule; √(2v) has derivative 1/√(2v) at v > 0, and the integrand is continuous), so
H′(x) = sin(w − F(x)) · (F′(x)/√(2λF(x)) − 1) ≥ 0, because sin(w − F(x)) ≥ 0 (0 ≤ w − F(x) ≤ π) and
F′(x) = f′(x) ≥ √(2λF(x)) by V2 and f′(x) > 0. By (M): ∫_c^d sin(w − F) ≤ Γ(F(d))/√λ. Finally
Γ(w) − Γ(F(d)) = ∫_{√(2F(d))}^{√(2w)} sin(w − u²/2) du ≥ 0, the integrand being ≥ 0 for u²/2 ≤ w ≤ π, and Γ(w) = A(w)/2. ∎
Equality holds for f = λ(x − c)²/2 with f(d) − f(c) = w. Degenerate cases: c = d (0 ≤ A(w)/(2√λ), which holds since
the integrand of A(w) is ≥ 0 for 0 ≤ w ≤ π); w = 0 forces c = d.

## V4. From the start of a negative arc (`Vdc2TailFacts`)
On a side with sin(f(c) − α) = 1: ∫_c^d cos(f − α) ≤ 0.
Proof. Put g = f − α; cos g(c) = 0 and, for every x, cos g(x) = −sin(g(x) − g(c)), sin g(x) = cos(g(x) − g(c)).
*One period.* Suppose in addition g(d) − g(c) ≤ 2π. Then ∫_c^d cos g ≤ 0:
(i) if g(d) − g(c) ≤ π, then cos g = −sin(g − g(c)) ≤ 0 on [c, d];
(ii) otherwise let m ∈ (c, d) be the point with g(m) − g(c) = π (intermediate value theorem; g is continuous), and
s = f′(m) > 0. On [c, m]: H₁(x) = (sin g(x) − sin g(c))/s − ∫_c^x cos g is continuous with
H₁′(x) = cos g(x) (f′(x)/s − 1) ≥ 0 for c < x < m, since cos g(x) ≤ 0 and 0 < f′(x) ≤ f′(m) = s. By (M),
∫_c^m cos g ≤ (sin g(m) − sin g(c))/s = (−1 − 1)/s = −2/s. On [m, d]: H₂(x) = (sin g(x) − sin g(m))/s − ∫_m^x cos g has
H₂′(x) = cos g(x) (f′(x)/s − 1) ≥ 0 for m < x < d, since cos g(x) ≥ 0 there (π ≤ g(x) − g(c) ≤ 2π) and f′(x) ≥ s. By
(M), ∫_m^d cos g ≤ (sin g(d) + 1)/s ≤ 2/s. The sum is ≤ 0.
*Induction on the number of periods.* Claim for n = 0, 1, 2, …: on every side with sin(f(c) − α) = 1 and
f(d) − f(c) ≤ 2π(n + 1), ∫_c^d cos(f − α) ≤ 0. n = 0 is one period. Step: if f(d) − f(c) > 2π, take q ∈ (c, d) with
f(q) − f(c) = 2π; [c, q] is a side of one period, [q, d] is a side with sin(f(q) − α) = sin(f(c) − α + 2π) = 1 and
f(d) − f(q) ≤ 2π n; add the two integrals. Every side is covered by some n (Archimedes). ∎
(f′ may tend to 0 at c; nothing above divides by f′ near c.)

## V5. One side (`Vdc2OneSideFacts`, from V3 and V4)
Given θ, choose the integer n with θ′ := θ − 2πn ∈ (−3π/2, π/2]; cos(v − θ) = cos(v − θ′) for all v.
Case A, θ′ ∈ (−π/2, π/2]: w := θ′ + π/2 ∈ (0, π], and cos(v − θ′) = sin(w − v). On a side put F = f − f(c).
If F(d) ≤ w: V3 gives the bound. If F(d) > w: take q ∈ (c, d) with F(q) = w; V3 on the side [c, q] gives
∫_c^q ≤ A(w)/(2√λ); V4 on the side [q, d] with α = f(c) + θ′ (sin(f(q) − α) = sin(w − θ′) = sin(π/2) = 1, and
cos(f − f(c) − θ) = cos(f − α)) gives ∫_q^d ≤ 0.
Case B, θ′ ∈ (−3π/2, −π/2]: w := π; v₀ := θ′ + 3π/2 ∈ (0, π], and cos(v − θ′) = sin(v − v₀).
If F(d) ≤ v₀: the integrand sin(F − v₀) is ≤ 0 on [c, d] (−π ≤ F − v₀ ≤ 0) and A(π) ≥ 0. Otherwise take p ∈ (c, d) with
F(p) = v₀; ∫_c^p ≤ 0 as before. On [p, d]: sin(F − v₀) = sin(π − (f − f(p))). If f(d) − f(p) ≤ π: V3 on the side [p, d]
with w = π gives ∫_p^d ≤ A(π)/(2√λ). Otherwise take q ∈ (p, d) with f(q) − f(p) = π: V3 on [p, q], and V4 on [q, d] with
α = f(c) + θ′ (sin(f(q) − α) = sin(v₀ + π − θ′) = sin(5π/2) = 1).
In both cases w depends on θ only. ∎

## V6. VC2-S (assembly, from V1 and V5)
Let f, f′, a ≤ b, λ be as in VC2-S, J = ∫_a^b e^{if}, x₀ the turning point of V1 and θ = arg J − f(x₀), with w from V5.
|J| = Re(J e^{−i arg J}) = ∫_a^b cos(f − arg J) = ∫_a^{x₀} cos(f − f(x₀) − θ) + ∫_{x₀}^b cos(f − f(x₀) − θ).
[x₀, b] is a side for (f, f′), so the second integral is ≤ A(w)/(2√λ). For the first, x ↦ f(−x) with derivative
−f′(−x) is a side on [−x₀, −a] (the rate condition is invariant under this reflection, and −f′(−x) > 0 because f′ < 0
on (a, x₀)); its value at the left end −x₀ is f(x₀), and ∫_{−x₀}^{−a} cos(f(−x) − f(x₀) − θ) dx = ∫_a^{x₀} cos(f − f(x₀) − θ).
The same w serves both sides. So |J| ≤ A(w)/√λ. (J = 0 needs no separate case: arg 0 = 0 and the identity
|J| = Re(J e^{−i arg J}) holds.)

## V7. VC2-A (part)
With β = √(2w) and z = ∫_{−β}^{β} e^{ix²/2} dx: Im(e^{iw} z̄) = ∫_{−β}^{β} sin(w − x²/2) dx = 2 ∫_0^β sin(w − u²/2) du = A(w)
(the integrand is even), and Im(e^{iw} z̄) ≤ |z|.

## V8. VC2-N (part): A(w) ≤ 7/2 on [0, π]
For 0 ≤ y: sin y ≤ P(y) := y − y³/6 + y⁵/120 − y⁷/5040 + y⁹/362880 (the Taylor polynomial of degree 9; P − sin
vanishes at 0 with its first nine derivatives, and its tenth derivative is sin y, which is ≥ 0 on [0, π]; iterate
(M) ten times, or use the Lagrange remainder; only 0 ≤ y ≤ π is needed).
For 0 ≤ u ≤ √(2w), y = w − u²/2 ∈ [0, w] ⊆ [0, π], so A(w) ≤ 2 ∫_0^{√(2w)} P(w − u²/2) du =: B(w). With
∫_0^{√(2w)} (w − u²/2)^n du = √(2w) w^n 4^n (n!)²/(2n + 1)!:
B(w) = 2√(2w) (2w/3 − 8w³/105 + 32w⁵/10395 − 128w⁷/2027025 + 512w⁹/654729075)
(coefficients computed by the lead in exact rationals; the prover recomputes them). On a grid of step 1/1000 the
lead found max B = 3.364571 (near w = 2.298), a margin of 0.135 to 7/2. Then B ≤ 7/2 on [0, π] by a certified
subdivision in β = √(2w) ∈ [0, √(2π)] (B is an odd polynomial of degree 19 in β with rational coefficients): on each
cell bound the positive terms at the right end and the negative ones at the left end. The statement is frozen with
7/2; a weaker constant is not acceptable.

## V9. VC2-K (assembly, from VC2-S and VC2-N)
φ″ is a derivative with |φ″| ≥ μ > 0 on (a, b), so it has one sign there
(`hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne`, as in `OscInt/VanDerCorput/Split.lean`). If φ″ ≥ μ, the mean
value inequality (`SplitAux.mul_sub_le_of_le_deriv`) gives the rate condition for φ′ + p with λ = μ on every [a, y],
y ∈ [a, b]; VC2-S and VC2-N give |∫_a^y e^{i(φ + px)}| ≤ (7/2)/√μ. If φ″ ≤ −μ, the same for −(φ + px), and the
integral of the conjugate has the same modulus. The amplitude: `AmplitudeTransferFacts` (proved for S1.k,
`OscInt/VanDerCorput/Amplitude.lean`) turns a uniform bound C for the partial integrals into C (|ψ(b)| + ∫_a^b |ψ′|).
μ^{−1/2} = 1/√μ.

## Blueprint, assembly and parts
Blueprint: `Blueprint/SecondDerivSharp.lean` (the definition `Vdc2Side` and five propositions). Assembly by the lead,
`OscInt/Front/SecondDerivSharpAssembly.lean`, written after the stamp of the review answers and compiled before any
part: `Vdc2Side.mono`, `norm_integral_exp_eq`, `secondDerivSharp_of` (V6) and `secondDerivSevenHalves_of` (V9).

| Part | Target | Section |
|---|---|---|
| VC1 | `Vdc2TurningPointFacts` and `Vdc2RootFacts` | V1, V2 |
| VC2 | `Vdc2HeadFacts` from `Vdc2RootFacts` | V3 |
| VC3 | `Vdc2TailFacts` | V4 |
| VC4 | `Vdc2OneSideFacts` from `Vdc2HeadFacts` and `Vdc2TailFacts` | V5 |
| VC5 | `Vdc2ProfileBoundStatement` (the frozen VC2-N) | V8 |
| VC6 | `SecondDerivAttainedStatement` (the frozen VC2-A) | V7 |

Interface checks (floating point; evidence, not proof): `numerics/review/vc2_interface_checks.py` tests V-root,
V-head, V-tail and V-side on eleven families of phases, three rates and three left ends, and the attainment by the
quadratic phase; results `numerics/results-vc2-interface-checks-2026-11-17.txt`. A first version of that script
reported violations of V-tail and V-side; they were quadrature errors (panels of fixed length at phase speeds of
10⁹), and they disappeared when the panels were cut by phase.
