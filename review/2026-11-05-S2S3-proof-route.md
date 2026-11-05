<!-- Referee of the on-paper proof route docs/proof-S2S3.md (fresh-context agent). Prompt: review/prompts/S2S3-proof-route.md. Read commit 68d4b36. Verbatim final report from the agent's hand-back call. -->

68d4b363175445d543256f4df48f560646adc49c

# Referee report: on-paper proof route for S2.1, S2.2 and S3

I read only `docs/statements.md` and `docs/proof-S2S3.md`, as the prompt allows.

**Summary.** I found no BLOCKER. Every step is correct in substance. The derivative counts are tight but sufficient, and nothing in the argument is circular. All the findings are fixes that can be made with a remark. One of them, the parametric calculus behind Part F1, is the largest piece of work that the text does not spell out. Details follow, step by step.

## (R1) Linear term as family parameter
- **Correct.** T = Λ × K′ is compact (product of two compact spaces). D Q_τ = DΨ_σ + p, and the higher derivatives are those of Ψ_σ, so joint continuity carries over.
- **Hypotheses translate correctly.**
  - S2.2: at a critical point (p, k) with k ∈ K, H ≠ 0, which is case (ii).
  - S3: FoldOrNondeg holds at every k ∈ K whatever p is. That is stronger than needed and covers (ii) and (iii) at critical points.
- No findings.

## (R2) Localisation
- **Correct, including the S(τ) device.**
  - Each (τ, k) lies in some U_i × B(k_i, δ_i/2), so the balls with i ∈ S(τ) cover K.
  - There are finitely many subsets S, each with a fixed partition, so the constants C_S are uniform.
  - The tsupport of χ_i A lies in B(k_i, δ_i), which is inside the closed ball the local estimate needs.
  - The Leibniz bound for j ≤ 2 is fine.
  - Σχ = 1 is needed only on K, which contains supp A.
- **NIT.** State that the partition satisfies Σ_{i∈S} χ_i^S = 1 on K and tsupport χ_i^S ⊆ B(k_i, δ_i) (open ball).
- **NIT.** In (L2) the local box is a rectangle R in the L-coordinates. Say that δ is chosen after a and b so that k₀ + L R contains B̄(k₀, δ).

## (L1) Non-critical point
- **Correct.**
  - Uses Q ∈ C² and B ∈ C¹.
  - |∂_e(B/∂_eQ)| ≤ |∂_eB|/c + |B| |∂²_eQ|/c².
  - B/∂_eQ is a global C¹ function. With Lean's x/0 = 0 it vanishes off B̄(k₀, δ), and ∂_eQ ≠ 0 on B(k₀, 2δ), which contains the boundary sphere.
- **MINOR (uniformity on U), which applies to L1 and L3–L6.** The text says "shrink U to a compact neighbourhood". That is not available: Λ is only a compact topological space, not Hausdorff or regular, so a closed neighbourhood of τ₀ inside U need not exist. Use the tube lemma instead:
  - If f is continuous on T × C with C compact, and |f(τ₀, ·)| < s on C, then there is an open U ∋ τ₀ with |f| < s on U × C.
  - Every "sup over U × box" in L1 and L3–L6 should be obtained this way. It needs no compactness of U and no Hausdorff property.
  - The genuine sups over compact sets are T × K in (N1) and T × K₁ in (N2). Those sets are compact and the functions are continuous on them, so those sups are fine.

## (L2) Normal form
- **Correct**, with two remarks.
- **MINOR.** v must be nonzero. In case (ii), take v ≠ 0 in the D²Q-orthogonal complement of w. That complement is a line, and it does not contain w because D²Q[w, w] ≠ 0, so L is invertible.
- **MINOR.** Say why a w with D²Q[w, w] ≠ 0 exists: a nonzero symmetric form has a nonzero diagonal value, by polarisation.
- **Checks.**
  - The new determinant is det D²Q · (det L)² ≠ 0, so ∂²_xQ = D²Q[v, v] ≠ 0 in case (ii).
  - In case (iii), ∂²_xQ = 0 and ∂³_xQ = D³Q[v, v, v] ≠ 0.
  - Amplitude derivatives scale by ‖L‖^j.

## (L3) Implicit critical point
- **Correct in substance.** The contraction argument with a parameter goes through:
  - Choose b, and a first U and a, so that |1 − ∂²_yQ_τ/q₀| ≤ 1/2 on [−2a, 2a] × [−2b, 2b], where q₀ = ∂²_yQ_{τ₀}(0, 0).
  - Then shrink U and a so that |∂_yQ_τ(x, 0)|/|q₀| < b/2.
  - This gives a self-map of [−b, b] with constant 1/2 and |y*| < b.
  - Continuity in (τ, x) follows from the fixed-point stability estimate, using the tube lemma uniformly in y ∈ [−b, b].
  - y*(τ₀, 0) = 0 by uniqueness. (L4) uses this.
  - No uniform implicit function theorem beyond the contraction is needed.
- **MINOR (domain mismatch).** y* is defined on U × [−a, a], but (c) claims C³ on (−2a, 2a). Fix it one of two ways:
  - define y* on [−2a, 2a]; or
  - claim regularity on (−a, a) only. Then define g′, g″ and y*′ by their explicit formulas, which are continuous on the closed [−a, a]. That is all S1's "has derivative on [a, b]" needs: continuity up to the endpoints and a derivative on the open interval.
- **MINOR (monotonicity).** Uniqueness "by strict monotonicity from (a)" needs ∂²_yQ to keep one sign. |∂²_yQ| ≥ μ alone gives that only by connectedness and the intermediate value theorem. The contraction condition already gives both the sign and the bound, with μ = |q₀|/2; use that. The same point applies to |h| ≥ μ and |H| ≥ μ/2 in (L5).
- **MINOR (regularity).** Only differentiability of y* with derivative −∂_x∂_yQ/∂²_yQ at (x, y*) is needed from the classical IFT, as a strict derivative from `ImplicitFunctionData`.
  - Higher regularity follows by bootstrapping from that formula: f = −∂_x∂_yQ/∂²_yQ is C², so y*′ = f(x, y*) is differentiable.
  - Joint continuity of y*′ and y*″ in (τ, x) follows from the formulas.
  - y* ∈ C² is all that is used; C³ is true but not needed.
  - Identifying the local IFT solution with y* is correct: the IFT solution is continuous and equals y*(τ, x) ∈ (−b, b) at x, so near x it stays in (−b, b), and uniqueness in (b) makes it equal to y*.

## (L4) Reduced phase
- **Correct.** I checked the derivatives:
  - g″ = ∂²_xQ + ∂_x∂_yQ · y*′ = H/∂²_yQ.
  - g‴ = ∂³_xQ + 2∂²_x∂_yQ · y*′ + ∂_x∂²_yQ · (y*′)² + ∂_x∂_yQ · y*″, which equals ∂³_xQ(0) at (τ₀, 0).
- g‴ needs y*″ and third derivatives of Q, both available.
- Shrinking a and U to get |g″| ≥ ν or |g‴| ≥ ν (tube lemma around x = 0) is harmless: b is unchanged and (L3) still holds on the smaller interval.

## (L5) Hadamard factorisation
- **Correct**, given the sign constancy point under (L3).
- **MINOR.** (L5) is stated on [−a, a] × [−b, b], but (L6) uses h and K on [−a, a] × [−2b, 2b]. Restate (L5) on the larger box; the segment from y* ∈ (−b, b) to y ∈ [−2b, 2b] stays in [−2b, 2b].
- **NIT (H is unused).** H and the identity Q − g = (y − y*)² H are never used. (L6) applies S1.2 in y directly to Q − g.
- **NIT (statements.md justification).** The modelling note in `statements.md` justifies C⁴ by "H ∈ C²". The real use of C⁴ is in (L6b)(ii): ∂²_y(Kθ/h) involves ∂²_yK = ∫s² ∂³_y∂_xQ ds and ∂²_yh = ∫s² ∂⁴_yQ ds, which are fourth derivatives of Q. C⁴ is therefore exactly what the proof needs; only the stated reason should be corrected.
- Only y-derivatives of h and K up to order 2, together with joint continuity, are used. x-regularity of h and K is never used.

## (L6) The estimate
- **Correct.** I checked:
  - **The algebra.** ∂_y e^{imQ} = im (y − y*) h e^{imQ}. The same identity holds with Q − g, because ∂_y g = 0.
  - **Integration by parts.** The boundary terms vanish because θ and θ′ vanish at ±2b.
  - **Fubini.** The integrand is continuous on a compact rectangle.
  - **The final exponents.** −1/2 − 1/2 = −1 and −1/2 − 1/3 = −5/6.
- **Amplitude regularity is used exactly.**
  - B ∈ C² is needed through ∂_yE = ∫s ∂²_yB ds in (L6a).
  - E is C¹, using y* ∈ C¹.
  - b′ = ∂_xB + ∂_yB · y*′, so |b′| ≤ C M′ given a tube-lemma bound on |y*′|.
- **S1 hypotheses.**
  - (i) S1.2 on [−2b, 2b]: phase m(Q − g) in y, with φ″ = m∂²_yQ and |φ″| ≥ mμ on the open interval by (L3)(a), since [−a, a] ⊆ [−2a, 2a]. Amplitude θ, with A(θ) = ∫|θ′|.
  - (ii) S1.2 with amplitude ψ = ∂_y(Kθ/h). ψ is continuous on the closed interval, ψ′ = ∂²_y(Kθ/h) is continuous and so integrable, and ψ(2b) = 0. Needs |h| ≥ μ on the whole segment, which holds.
  - (iii) bJ is continuous on [−a, a], so the "known weak point" is resolved:
    - J is differentiable by differentiation under the integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`; θ has compact support and the x-derivative of the integrand is continuous).
    - J′ is continuous, so (bJ)′ = b′J + bJ′ is continuous and integrable.
    - b(±a) = 0 because B is continuous and vanishes outside R.
- **NIT.** y* exists only for |x| ≤ a, so the decomposition should be written for x ∈ [−a, a], with the integrand zero outside. Also, the 2D integral of θ(y − y*)E should be bounded as 2a · sup over x of the 1D bound.

## (N1) Compactification of the linear term
- **Correct.**
  - G is finite: a sup over the compact Λ × K of a continuous function.
  - T is closed. It is ⋂_k {(σ, p) : |∇Ψ_σ(k) + p| ≥ c}, each set closed for fixed k. A closed subset of the compact Λ × B̄(0, R) is compact; no Hausdorff property is needed.
  - Large |p|: |s∇Ψ + u| ≥ 1 − G/R ≥ 1/2 in any norm, and m/s > m ≥ 1.
  - The family over Λ × [0, 1/R] × S¹ is fine, including s = 0.
  - S¹ is the unit sphere of whichever norm is used, which is compact either way.

## (N2) Compact non-stationary family, order N
- **Correct**, by induction with the same family at each level. I checked:
  - The sign: (−1/(im)) = i/m.
  - The derivative count: div(wA) is C^{N−1} and uses D^N w and D^N A, with Φ ∈ C^{N+1}.
  - The base case N = 0.
- **MINOR (the neighbourhood K₁).** It does not follow from joint continuity alone that |∇Φ_τ| ≥ c on a compact neighbourhood K₁ of K.
  - What does hold, using compactness of T × K (finite cover by products and a Lebesgue-number argument), is |∇Φ_τ| ≥ c/2 on K₁ = K + B̄(0, ρ) for all τ.
  - Replace c by c/2.
- **MINOR (norm in w).** w must be defined with the Euclidean square (∂₁Φ)² + (∂₂Φ)², not with Lean's max norm on ℝ × ℝ, which is not differentiable. A lower bound for the max norm gives the same lower bound for the Euclidean norm.
- **MINOR (uncited ingredient: Part F1).** This is the largest ingredient the text does not spell out. (N2) needs D^j w for all j ≤ N, with general N, to be jointly continuous in (τ, k).
  - That needs a parametric chain rule or Faà di Bruno, or at least the following closure facts for "family of class C^n" with a topological parameter:
    - closure under products (parametric Leibniz);
    - closure under the reciprocal of a non-vanishing function (induction on n via D(1/f) = −Df/f²);
    - closure under composition with fixed smooth maps.
  - Mathlib's ContDiff tools do not apply directly because τ is not in a normed space.
  - Part F1 asserts this without proof. Write the reciprocal-by-induction argument explicitly; it avoids general Faà di Bruno.
  - For (L3)–(L6) only derivatives up to order 4, from explicit formulas, are needed. There, plus parametric integrals in s (h, K, E) and the composition (τ, x) ↦ (τ, x, y*(τ, x)), it is a finite and explicit check.

## Assembly and the five questions
- **Regularity counts.** Phase C⁴ is used exactly, by ∂²_y(Kθ/h) in (L6b)(ii). Amplitude C² is used exactly, by ∂_yE in (L6a). C^{N+1}/C^N in S2.1 is exact. No step uses a derivative that is not available: H is never differentiated, h and K only twice in y, y* at most twice, E once, J once.
- **Uniformity.** Constants are uniform provided every sup on an open U is replaced by the tube-lemma argument (MINOR above).
- **S1 hypotheses.** Met in all three applications, (L6b)(i)–(iii).
- **Circularity and extra results.** Nothing is circular. No Morse lemma and no uniform IFT beyond the contraction is needed. Beyond the listed results, the proof uses:
  - Fubini on rectangles;
  - differentiation under the integral sign;
  - the tube lemma;
  - the parametric C^n algebra (Part F1).

## Verdict
The blueprint can be cut along these steps as they stand. Each step is mathematically correct, the derivative counts are right and tight, and the S1 interfaces are satisfied.

Before encoding, fold in these remarks:
- the tube lemma instead of compact neighbourhoods (Λ is not assumed Hausdorff);
- sign constancy of ∂²_yQ from the contraction condition;
- the domain of y*, and the formulas for g′ and g″ up to the endpoints, in (L3)(c);
- v ≠ 0 in (L2);
- (L5) stated on [−2b, 2b], with H dropped;
- c/2 and a Euclidean |∇Φ|² in (N2).

Part F1 (parametric Leibniz, reciprocal and composition, for general N in S2.1) should be specified as its own blueprint part with a written proof. It is the one place where real work hides behind a phrase.

The justification for C⁴ in `docs/statements.md` ("H ∈ C²") should be corrected to the actual use, ∂²_y of K and h in (L6b)(ii). The statement itself needs no change.
