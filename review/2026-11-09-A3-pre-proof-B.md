c7282ab463cca3bf87bbca51341ce168f927152d

# Referee B: blind pre-proof statement review of batch A3 (S1.k, S5.1, S5.1′)

## Summary

All three statements are **TRUE** and **FAITHFUL** to `docs/statements.md`. I found no BLOCKER and no MAJOR. The findings are four MINOR and three NIT, and every one concerns the sanity file or the documentation. None affects the frozen text of `OscInt/Statements/Cusp.lean`.

- **Definitions.** `IsA3Point` is exactly "rank-one Hessian, third derivative zero along the kernel, reduced quartic nonzero". `IsStableA3Point`'s extra condition does not depend on which `w` (or which kernel `v`) is chosen.
- **Proof routes.**
  - S1.k follows from Stein's induction with the stated constant.
  - The S5.1 dyadic route works. I find C⁴ is already enough for `FamilyCk 4`, where the docs conjecture C⁵.
  - The S5.1′ route works with C² amplitudes. It also proves S5.1.
- **Corpus points.** The discrete Klein–Gordon and QWZ (m = 3) A3 points are stable A3 points after translation to the origin. I checked this exactly at all four points of each model.
- **Main weakness.** The sanity bites do not semantically pin condition (i), the kernel condition. If (i) is removed, the bite theorems stay true and the definition then accepts the nondegenerate point x² + y² + x⁴. A copy of S5.1′ with (i) removed would be false; y² + y⁴ + x⁶ is a counterexample. I checked this in Lean scratch.

I did not prove any statement under review, in scratch or anywhere else. My Lean checks only evaluated definitions on concrete data, or evaluated planted copies of the definitions. I wrote nothing in the repository, and `git status` is clean. I ran at most one Lean process at a time, under `nice -n 10`.

## Evidence (scratch, outside the tree)

**Python** (venv `/tmp/refB/venv`, built from `numerics/census/requirements.txt`, plus numpy and scipy):
- `/tmp/refB/exact.py` writes `/tmp/refB/exact.out`. These are exact SymPy checks.
- `/tmp/refB/sweep.py`, `/tmp/refB/sweep2.py` and `/tmp/refB/profile.py` write `/tmp/refB/sweep.out` and `/tmp/refB/sweep2.out`. These are exploratory numerics, not evidence.

**Lean:**
- `/tmp/refB/Defs.lean` checks the following, all passing:
  - `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)` and `∞ ≠ ω`.
  - `(5 : ℝ) * 2 ^ (k - 1) - 2` elaborates with a natural-number exponent `k - 1`; it equals 38 at k = 4 and 78 at k = 5.
  - `μ ^ (-(1 : ℝ) / k)` is `Real.rpow μ ((-1)/k)`, and `t ^ (-(3:ℝ)/4)` is `Real.rpow t (-3/4)`; both close by `rfl`.
  - The header's form `(5 * 2 ^ (k - 1) - 2 : ℝ)` is the same term (`rfl`).
  - `iteratedFDeriv_succ_apply_left` confirms the first vector is the outermost derivative.
  - `#print axioms` on the sanity theorems shows only the standard axioms.
- `OscInt/Front/CuspSanity.lean` compiles at HEAD.
- `/tmp/refB/Plant.lean` (planted copies of the definitions, evaluated on the sanity data) compiles; details under MINOR 1 and 2.

## 1. Verdicts per constant and definition

**`DerivChain D k a b`: FAITHFUL.**
- It requires `HasDerivOn (D j) (D (j+1)) a b` for `j < k`. So D₀, …, D_{k−1} are continuous on [a, b], each D_j is differentiable on (a, b) with derivative D_{j+1}, and D_k is constrained only on (a, b).
- This is exactly the doc's "derivative chain of length k".
- At k = 2 and k = 3 it reproduces the hypotheses of S1.2 and S1.3.

**`VdCkStatement` (S1.k): FAITHFUL to statements.md, and TRUE.**
- Against the classical result (Stein VIII §1.2, Proposition 2 and its Corollary) it is FAITHFUL-WEAKER in hypotheses: it asks for less regularity than Cᵏ (endpoint continuity of D₀…D_{k−1} only, D_k only on the open interval), so the theorem is more general. The constant c_k = 5·2^{k−1} − 2 is Stein's.
- Parsing:
  - `2 ^ (k - 1)` is a real number raised to the natural `k - 1`, and k ≥ 2 rules out truncation.
  - `-(1:ℝ)/(k:ℝ)` is −1/k.
  - At k = 0 or 1 the formula would give 3, but those k are excluded.
- Why it is true:
  - Darboux's theorem on (a, b) gives D_k a constant sign. So D_{k−1} is strictly monotone on [a, b] (it is continuous there).
  - The set {|D_{k−1}| < γ} is an interval of length at most 2γ/μ (mean value theorem). Its complement is at most two intervals, where the k−1 case applies.
  - With γ = μ^{(k−1)/k} this gives c_k = 2c_{k−1} + 2 from c₁ = 3 (S1.1, which applies because D₁ + p is monotone with derivative D₂).
  - For the amplitude: put F(x) = oscInt on [a, x], which satisfies the plain bound because every hypothesis is inherited by subintervals. Integrating by parts gives F(b)ψ(b) − ∫Fψ′, which is exactly `ampNorm`.
  - The linear term p enters only through D₁ + p in the base case.

**`IsA3Point`: FAITHFUL to statements.md, and correct against the classical notion.**
- What the conditions force:
  - If v = 0, then (iv) equals 0, so v ≠ 0 is forced.
  - (ii) forces H ≠ 0.
  - (i) with v ≠ 0 forces rank ≤ 1. Hence the rank is exactly one, with kernel span v.
  - If w lies in the kernel, (ii) fails. A w that is not orthogonal to the kernel is fine.
- Choice of w:
  - Replacing w by c·w + λv multiplies (ii) by c². This uses symmetry of D², which `ContDiff ℝ ∞` provides.
  - D³[v,v,w] changes to c·D³[v,v,w] + λ·D³[v,v,v] = c·D³[v,v,w] by (iii). This uses linearity only.
  - Replacing v by a·v multiplies g₄ by a⁴.
  - Hence the existential form ⇔ the universal form, and no point that is not A3 satisfies the existential.
- I checked the reduced quartic exactly with a general 4-jet: g(u) = φ(uv + s(u)w) has u, u², u³ coefficients 0 and 24·h·[u⁴] = h·b₄₀ − 3a₂₁². So g₄ is the reduced quartic, not the quartic along the straight line.
- (iii) is the u³ coefficient of the reduced function.
- The argument order of `iteratedFDeriv` is irrelevant for C⁴ phases.

**`IsStableA3Point`: FAITHFUL.**
- By the above, condition (v) does not depend on the choice of (v, w), given (iii).
- In adapted coordinates the gradient map is (T/h)·uσ + (g₄/6h)·u³ in the first component, with σ as the second. This is a Whitney cusp exactly when T ≠ 0 and g₄ ≠ 0, so the doc's "Whitney cusp" reading is correct.

**`CuspBoundStatement` (S5.1) and `CuspBoundGenStatement` (S5.1′): FAITHFUL to statements.md, and TRUE.**
- The Lean text matches the doc:
  - `ContDiff ℝ ∞` is the smooth index, not ω.
  - The amplitude hypothesis is `AmpBound 2 (closedBall 0 δ)` with the max-norm ball.
  - The quantifiers are ∃δ>0, ∃C, then ∀A, M, y, t. C depends only on φ and δ.
  - The bound holds for all y ∈ ℝ² and all t ≥ 1.
  - `t ^ (-(3:ℝ)/4)` is rpow with t > 0.
  - A negative M makes `AmpBound` false, so such M are vacuous.
- Against the classical estimate (Duistermaat 1974; Varchenko and Karpushkin for two variables):
  - **Weaker in perturbations:** S5.1 and S5.1′ are uniform only over linear perturbations, while the classical estimate is uniform over all small perturbations.
  - **Stronger in amplitude:** the bound is explicit in the C² norm.
  - Both routes below support the C² claim.
- Truth for S5.1′:
  - The miniversal deformation u⁴ + a₂u² + a₁u ± s² induces every linear deformation.
  - The 1D van der Corput bound with k = 4 is uniform in (a₁, a₂).
- Exploratory numerics. The amplitude is Gaussian (σ = 0.3); the y-integral is done in closed form. I used a 25×25 grid of linear terms at t ≤ 10³ and 15×15 at t = 10⁴, with y₂ up to 12·t^{1/2}. The table shows t^{3/4}·max over y of |I|, and t^{1/2}·|I(t, 0)| for the trap:

| Phase | t = 10² | t = 10³ | t = 10⁴ | Reading |
|---|---|---|---|---|
| Stable 2y² + x²y + 3x⁴ + x⁵ | 1.52 | 2.01 | 2.37 | Growth ratios 1.32, 1.18 are falling, so the values are settling |
| Non-stable y² + x⁴ + x⁵ | 2.50 | 2.97 | 3.13 | Converging |
| Trap (y + x²/2)², positive control | t^{1/2}·\|I(t,0)\| = 0.925 | 0.928 | 0.928 | Decay is t^{−1/2}; t^{3/4}·\|I\| grows like t^{1/4} (5.2 → 9.3) |

  - For the stable phase, the maximum sits at y₂ ≈ 10–16·t^{1/2}. This matches interference of three Morse points, whose contribution scales as λ^{−1/2}·t^{−3/4} with λ = y₂·t^{−1/2}, plus pre-asymptotic drift (I see a second interference peak at λ ≈ 48).
  - Every result here is consistent with a bounded sup over y, and shows that the sweep would detect a slower rate.

## 2. Derivability

**S1.k.** It can be proved by the classical induction with c_{k+1} = 2c_k + 2, as above. S1.2 and S1.3 are exactly its cases k = 2 and k = 3: `vdCk_to_vdC2` and `vdCk_to_vdC3` compile, with standard axioms only.

**S5.1 by the dyadic route.**
- Set Φ_ε(u,s) = ε⁻⁴[φ(εuv + ε²sw) − φ(0) − Dφ(0)(εuv + ε²sw)], using H[v,v] = H[v,w] = 0 and D³[v³] = 0.
- Then Φ_ε = h s²/2 + (T/2)u²s + (Q/24)u⁴ + O(ε).
- The Taylor remainder R = φ − P₄ satisfies ∂^αR(x) = o(|x|^{4−|α|}) for |α| ≤ 4. So ε⁻⁴·∂^α[R(εu, ε²s)] = o(ε^{α_s}) → 0 uniformly on compact sets.
- Hence the family over [0, ε₀] is `FamilyCk 4` already for φ ∈ C⁴. The doc's "CONJECTURED: C⁵ suffices" is true and can be sharpened (NIT 1).
- On the anisotropic annulus ½ ≤ (u⁴ + s²)^{1/4} ≤ 2 (outside the origin), every point of the model is nondegenerate or a fold:
  - M_ss = h ≠ 0.
  - On the degenerate curve g₃ = h²u·g₄, and u = 0 on that curve only at the origin. This is check E1, which I re-derived.
  - The set where fold-or-nondegenerate fails is closed in (ε, k), so compactness extends this to ε ≤ ε₀.
- The pieces:
  - For bounded rescaled linear terms p_ε = (ε⁻³(y + t∇φ(0))·v/t, ε⁻²(…)·w/t), apply S3.
  - For |p_ε| ≥ R, apply S2.1 with N = 2 (`FamilyCk 3`).
  - On the inner region ρ ≤ t^{−1/4}, the trivial bound M·t^{−3/4}.
  - The amplitude bound is χ(ρ)·A(εu, ε²s), whose C² bound is ≤ C·M for ε ≤ 1.
  - Summing the pieces: Σ_{ε ≥ t^{−1/4}} ε³·(tε⁴)^{−5/6} ≈ t^{−3/4}.
- The route works.

**S5.1′ with C² amplitudes.**
- When T = 0 the dyadic route fails: the model h s²/2 + Q u⁴/24 is A3 along the whole line u = 0 (check E2, confirmed).
- That makes S5.1′ only harder to prove, not false.
- The route sketched in the doc works:
  - In the transverse variable, |∂²_sφ| ≥ h/2 on the ball. 1D stationary phase in s with parameters (u, η = y₂/t) gives c·t^{−1/2}·e^{itΦ(u,η)}·a(u,η) + R, with |R| ≤ C·t^{−1}·‖A‖_{C²}. Write b(σ) − b(0) = σ·c(σ) with c ∈ C¹ and integrate by parts once.
  - Φ(u,η) = φ(u, s_c) + η·s_c and ∂_u⁴Φ(0, η₀) = g₄/h ≠ 0.
  - Because H_us(0) = 0, |s_c(u,η) − s_c(0,η)| = O(δ²). So whenever a(·,η) ≠ 0, the lower bound on |∂_u⁴Φ| holds on all of [−δ, δ].
  - Then S1.k with k = 4 (constant 38) gives t^{−1/4}·(BV norm of a) ≤ C·t^{−1/4}·M.
  - Non-stationary η are handled by one integration by parts in s, giving O(t^{−1}).
  - With a Morse change of variables, b ∈ C² needs φ ∈ C⁵; without it, C⁴ is enough.
- I found no step where the route fails. This route never uses T, so it also proves S5.1, making S5.1 a corollary of S5.1′ (via `stable_isA3`).
- Missing tool: a 1D stationary-phase lemma with parameters and a C² remainder.

## 3. Vacuity and usefulness

- **Satisfiable.** `gen_isStableA3` gives the stable generic datum (h = 4, T = 2, Q = 72, g₄ = 276; exact). `nonv_isA3` gives x⁴ + y². The quartic is `ContDiff ℝ ω`, which implies `ContDiff ℝ ∞`. Nonzero amplitudes satisfying `AmpBound` exist.
- **Discrete Klein–Gordon**, ω = √(5 − 2cos k₁ − 2cos k₂), with ω² ≥ 1 so ω is C^∞ on ℝ²:
  - At (π/2, π/2) the Hessian is −(1/(5√5))·[[1,1],[1,1]]. With v = (1,−1), w = (1,0): H[w,w] = −√5/25, D³[v³] = 0, Q = 0, T = −√5/5, g₄ = −3/5.
  - With the lead's v = (−√5/25, √5/25): T = −√5/625, as the doc states.
  - All four points (±π/2, ±π/2) give |T| = √5/5 and g₄ = −3/5.
  - So all four are stable A3 points after translation, since iteratedFDeriv of a translate equals iteratedFDeriv at k₀.
- **QWZ at m = 3**, ω² = 11 + 6(cos k₁ + cos k₂) + 2cos k₁cos k₂ ≥ 1:
  - At (a, a) with a = arccos(−1/3), H = (8√65/12675)·[[1,1],[1,1]]. With v = (1,−1), w = (1,0): T = 6√130/65, Q = 18√65/65, g₄ = −13992/4225.
  - The doc's 128√130/53551875 corresponds to v = H₁₁·(1,−1); it is consistent.
  - All four points (±a, ±a) are stable.
- **What a downstream user loses:**
  - **Smoothness on all of ℝ².** Nothing is lost: cut off the phase, then shrink δ (an `AmpBound` on a smaller ball implies the one on the stated ball).
  - **A general point k₀.** A translation lemma is needed; the integral changes only by a unimodular constant.
  - **Lost:**
    - compact families of phases, e.g. KG uniform in the mass (Borovyk–Goldberg's masses and couplings);
    - uniformity over non-linear perturbations, which a family passing through an A3 point needs;
    - the global assembly.
  - **Note for the next batch.** A global theorem need not assume finitely many A3 points. A pointwise classification (each point of K is nondegenerate, a fold, D4 or A3) plus compactness and a partition of unity suffices. Non-stable A3 points come in curves (x⁴ + y² is A3 at every (0, y)), while stable ones are isolated (E1 plus continuity).

## 4. Sanity theorems and bites

Coverage of the five conditions:

| Bite | Datum | Fails exactly its target? |
|---|---|---|
| Trap, condition (iv) | (y + x²/2)² | Yes. For every w, g₄ = 2w₂²·6 − 3(2w₂)² = 0. |
| Fold, condition (iii) | x³ + y² | Yes. With (iii) removed it satisfies (i), (ii), (iv) via v = e₁, w = (1,1), g₄ = −108. |
| Hessian zero, condition (ii) | x³ + y³ | Yes. v = (1,−1), w = (1,0) satisfies (i), (iii), (iv) with g₄ = −108. |
| Non-stable, condition (v) | x⁴ + y² | Yes, but its D³ is identically zero. |
| Rank two, condition (i) | x² + y² | **No.** It fails (iv) for every v, w (D³ = D⁴ = 0), whatever (i) says. |

**Plants the bites catch:**
- changing the 3 in g₄ to another number;
- `![v,v,w]` → `![v,w,w]` inside g₄ (the trap then becomes A3);
- straight-line quartic in place of g₄;
- removing (ii), (iii), (iv) or (v);
- swapping the roles of v and w in (iv);
- the S1.k constant or exponent changed at k = 2 or 3; `2 ≤ k` → `3 ≤ k`;
- any change to the conclusions of S5.1 / S5.1′, because the sanity theorems restate the conclusion with the constants.

**Plants they miss:** see MINOR 1–4.

## 5. Findings

**MINOR 1 (sanity coverage of condition (i)).**
- Condition (i) is `(∀ z, iteratedFDeriv ℝ 2 Ψ k₀ ![v, z] = 0)`.
- No bite depends on it semantically. In `/tmp/refB/Plant.lean`, the planted copy `PlantNoKer` (with (i) removed) still satisfies:
  - `¬ PlantNoKer (quartic qTrap) 0`
  - `¬ PlantNoKer (quartic qNondeg) 0`
  - `¬ PlantNoKer (quartic qFold) 0`
  - while `x³ + y³` still fails through (ii).
- And `PlantNoKer (quartic qX) 0` holds for the nondegenerate x² + y² + x⁴.
- A copy of S5.1′ with (i) removed is false: y² + y⁴ + x⁶ with v = w = e₂ satisfies (ii)–(iv) with g₄ = 48, and its decay is t^{−2/3}.
- The header's claim that `x² + y²` (rank two) "fails the condition it targets" is inaccurate.
- **Fix:** add a rank-two bite with a nonzero quartic, e.g. x² + y² + x⁴, and/or a rank-one datum with an off-kernel v. This follows lessons 17 and 38.

**MINOR 2 (sanity coverage of condition (v)).**
- Condition (v) is `iteratedFDeriv ℝ 3 Ψ k₀ ![v, v, w] ≠ 0`.
- The plant `![v, w, w]` passes (`PlantStable`, Lean-checked):
  - the generic datum has D³[e₁,e₂,e₂] = 10 ≠ 0;
  - the only non-stable bite, x⁴ + y², has D³ identically zero.
- The planted statement stays true (by S5.1′) but no longer means "stable".
- **Fix:** add a non-stable bite with D³ ≠ 0, e.g. x⁴ + y² + xy² (T = 0, D³[v,w,w] = 2).

**MINOR 3 (sanity data all at k₀ = 0 with v = e₁, w = e₂).**
- Every datum for `IsA3Point Ψ k₀` / `IsStableA3Point Ψ k₀` has k₀ = 0, v = e₁ and w = e₂.
- So these plants pass:
  - evaluating at `0` instead of `k₀`;
  - fixing v := (1,0), which would exclude the KG and QWZ points, whose kernel is (1,∓1).
- This is lessons 38's GD finding again. The definitions are exported for the global batch.
- **Fix:** add a translated datum and one with an oblique kernel. The KG point itself would serve, or a rotated quartic.

**MINOR 4 (S1.k pinned only at k = 2, 3).**
- `vdCk_to_vdC2` and `vdCk_to_vdC3` exercise `VdCkStatement` only at k = 2, 3. `chain4_satisfies` checks `DerivChain` but not through the statement.
- Plants that agree at k ≤ 3 pass all sanity theorems:
  - `∀ j < min k 3` in `DerivChain`, which makes S1.k false at k = 4: D₀ = 0, D₄ = 1 unconstrained, |∫| = b − a;
  - a constant such as `10 * k - 12`.
- **Fix:** add a sanity theorem applying `VdCkStatement` at k = 4 to `chain4`, with the constant 38.

**NIT 1.** In statements.md, Modelling choice 2 says "CONJECTURED: C⁵ suffices for the rescaled family to be FamilyCk 4". By the Taylor little-o argument in §2, C⁴ suffices. The S5.1′ route with a Morse change needs C⁵ for a C² amplitude, or C⁴ without it.

**NIT 2.** statements.md gives QWZ's D³ω[v,v,w] = 128√130/53551875 without stating v. It holds for v = H₁₁(φ)·(1,−1) = (8√65/12675)·(1,−1) and w = (1,0). Stating v would make the number checkable.

**NIT 3.** The statements.md text says the S5.1′ route uses a "Morse lemma with parameters". A 1D stationary phase in s with parameters suffices, and the same route proves S5.1. Saying so would let the proof plan choose the cheaper route.
