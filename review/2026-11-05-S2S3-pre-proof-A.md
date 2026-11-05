<!-- Blind pre-proof review of S2.1, S2.2, S3, referee A (fresh-context agent). Prompt: review/prompts/S2S3-pre-proof.md. Read commit 5ae5589. Verbatim final report from the agent's hand-back call. -->

5ae558950e489b5b469336a61af3fb93fa26c67c
2650f1484b3252166e9442f383ad734075f60f180d595c7d6729d9737edba5ad  OscInt.Statements.FoldStatement / a837c8bd…  VdC1Statement / 66cc331d…  VdC2Statement / 30b3f96c…  VdC3Statement / 238318a7…  NonStationaryStatement / 283a23fe…  StationaryPhaseStatement (full lines as in `build/commit/commitments.txt`)

# Referee A: blind pre-proof review of S2.1, S2.2, S3

**Overall: no BLOCKER and no MAJOR findings.** All three statements are FAITHFUL to `docs/statements.md` and, I believe, TRUE. None of them is vacuous.

## What I read and ran
- I read only `docs/statements.md` (the S2/S3 section, with S1 as context) and `OscInt/Statements/StationaryPhase.lean`.
- I compiled two scratch files, `/tmp/refA/check.lean` and `/tmp/refA/check2.lean`, one process at a time with `nice -n 10`. I wrote nothing in the repository.
- From `#print` with `pp.coercions` and `pp.numericTypes` on:
  - `AmpBound` and `FamilyCk` elaborate to `ContDiff ℝ (↑n)` with `n : ℕ` coerced to `WithTop ℕ∞`, so finite smoothness, not analytic (ω).
  - `m ^ N` is a natural power.
  - The fold exponent is `m ^ (-5 / 6 : ℝ)`, i.e. `Real.rpow`, and `m ≥ 1` keeps it harmless.
- I proved (check2.lean compiled with no errors) that for C⁴ Ψ, `dd Ψ k v w = iteratedFDeriv ℝ 2 Ψ k ![w, v]`, i.e. D²Ψ(k)(w, v). By symmetry of the second derivative for C² functions this is ∂_w∂_vΨ, so `hessDet` is the true Hessian determinant. The same nesting makes `ddd Ψ k v v v` equal D³Ψ(k)(v, v, v).
- I proved `AmpBound n K A M → 0 ≤ M` (take j = 0), so there is no trick with negative M.

## Checks common to all three statements
- **Lean conventions:**
  - The Bochner integral is safe. Under `AmpBound`, A is continuous and `tsupport A ⊆ K` with K compact, so the integrand is continuous with compact support and integrable; the junk value 0 is never reached.
  - The `fderiv` junk value never arises, because every derivative in a hypothesis is of a C^{N+1} or C⁴ function.
  - `/ m ^ N` and `/ m` are safe since m ≥ 1.
- **Quantifier order:** `∃ C` comes after (Λ, N, Ψ, K, c) in S2.1, after (Ψ, K, K') in S2.2 and after (Λ, Ψ, K, K') in S3. It comes before A, M, σ, p and m in all three, so C cannot depend on A, M, σ, p or m. This matches the docs.
- **`FamilyCk`:** joint continuity of `(σ,k) ↦ iteratedFDeriv ℝ j (Ψ σ) k` into the normed space of multilinear maps is what the docs describe. With Λ compact it gives uniform bounds on Λ × K.
- **Norms:** the max norm on `ℝ × ℝ` affects the operator norms in `AmpBound` only up to constants. `GradLower` is written with Euclidean squares, which is equivalent to |∇(Ψ+p·)| ≥ c because c > 0.

## S2.1 `NonStationaryStatement`
**Verdict:** FAITHFUL, and TRUE.

**Why it is true.**
- Integrate by parts N times with the transposed operator L^t f = −div(f V)/(i m), where V = ∇Φ/|∇Φ|² and Φ = Ψ_σ + p·.
- The smallness condition is only on K, but by continuity |∇Φ| > c/2 on an open neighbourhood of K. A·V extended by zero is therefore C^N with support in K.
- Each derivative of V is a sum of terms built from D^{≥2}Ψ_σ divided by powers of |∇Φ|. The homogeneity is −1 − (number of derivatives), with the ∇Φ factors in the numerator balanced against the denominator. So every term is bounded using |∇Φ| ≥ c and sup over Λ × K of ‖D^jΨ‖ for 2 ≤ j ≤ N+1.
- This is uniform in p. As |p| → ∞ the terms only get smaller (|∇Φ| grows), and p enters only through ∇Φ.
- Order count: N integrations need D^{N+1}Ψ and D^N A, matching `FamilyCk (N + 1)` and `AmpBound N`.

**Edge cases.** N = 0 is the trivial bound vol(K)·M. K = ∅ forces A = 0. m near 1 is trivial.

**Findings.**
- NIT: `∀ (Λ : Type)` restricts Λ to universe 0. This is harmless for the intended use (Λ = [0, ε₀] as a subtype of ℝ).
- NIT: `GradLower` is required on all of `K`, not just on `tsupport A`. This is documented and necessary for C to be uniform over A.

## S2.2 `StationaryPhaseStatement`
**Verdict:** FAITHFUL, and TRUE.

**Why it is true.**
- Let Z = {(p,k) ∈ K'×ℝ² : k critical for Ψ+p·, `hessDet` = 0}. Z is closed and disjoint from the compact set K'×K, so it lies at positive distance from it. Degenerate critical points just outside K therefore cannot approach `tsupport A`.
- The nondegenerate critical pairs in K'×K form a compact set on which |hessDet| is bounded below. Near it, |∇Ψ(k)+p| ≳ |k − k*(p)| uniformly (implicit function theorem).
- Away from it, |∇(Ψ+p·)| ≥ c > 0, and S2.1 with N = 1 applies.
- A partition of unity on K (with C² cutoffs) reduces the problem to one nondegenerate critical point. That case is Hörmander, Thm 7.7.5, with k = 1 and n = 2: an amplitude in C²₀, a phase in C^{3k+1} = C⁴, and remainder ≤ C ω^{-1} Σ_{|α|≤2} sup|D^α u|. The leading term is ω^{-1}|u(x₀)|·|det f''|^{-1/2}.
- Hörmander's constant is uniform when f stays bounded in C⁴ and |x − x₀|/|f'(x)| is uniformly bounded, which compactness of K' gives.
- So |I| ≤ C M m^{-1} with exactly C⁴ phase and C² amplitude.
- Ill-conditioned regimes are excluded or harmless: a Hessian eigenvalue tending to 0 is ruled out by compactness and continuity. A critical point on ∂K is just an interior stationary point of a C² amplitude vanishing outside K.

**Findings.**
- NIT: the statement is for a single phase, not uniform over a family (the docs say the same). This only matters if a later statement needs family-uniform nondegenerate stationary phase.

## S3 `FoldStatement`
**Verdict:** FAITHFUL, and TRUE.

**Does `FoldOrNondeg` mean the fold condition?** Yes. If `hessDet = 0` and `∃ v w, dd Ψ k v w ≠ 0`, the symmetric 2×2 Hessian has rank exactly one. Its kernel `{v | ∀ w, dd Ψ k v w = 0}` is a line (left and right kernels agree by symmetry). `ddd Ψ k v v v ≠ 0` is D³Ψ(k)(v,v,v) ≠ 0. The right disjunct does not require hessDet = 0, but when hessDet ≠ 0 the left disjunct holds anyway, so this is harmless.

**Why it is true (and uniform).**
- **The condition is open.** The set of (Hessian, cubic) jets satisfying "nondegenerate, or rank one with cubic nonzero along the kernel" is open: near a rank-one jet the Hessian stays rank ≥ 1, and the kernel moves continuously. The jets over the compact set Λ × K lie in this open set by hypothesis, so a degeneration "in the limit" is impossible. The limit σ belongs to Λ and satisfies the hypothesis; a Hessian dropping to rank 0, or the cubic along the kernel tending to 0, would violate it there.
- **Near a fold point (σ₀, k₀):** take ∂_y²Ψ ≠ 0 with the kernel along x.
  - Solve ∂_yΨ_σ + p₂ = 0 for y*(x; σ, p₂), which is C³.
  - One-dimensional stationary phase in y (Hörmander 7.7.5, n = 1, k = 1, C⁴ phase, C² amplitude) gives m^{-1/2} e^{imφ(x)} b(x) + O(m^{-1}‖A‖_{C²}). Here b is C¹.
  - Along the curve φ'' = hessDet/∂_y²Ψ, and φ''' ≠ 0 near x₀ by the fold condition. This is uniform in σ near σ₀ and in p ∈ K'.
  - One-dimensional van der Corput with the third derivative, uniform in the linear term p₁x (cf. S1.3), gives m^{-1/3}∫|b'|. The total is m^{-5/6}.
  - Where y* does not exist, the y-integral is non-stationary and decays faster.
- **Elsewhere:** at nondegenerate points away from folds the bound is m^{-1} ≤ m^{-5/6}. Points with hessDet ≠ 0 but small lie in the fold neighbourhoods.
- The sharpness and uniformity of the exponent 5/6 for the A₂ (fold) singularity under all small perturbations is classical: Duistermaat 1974; Arnold–Gusein-Zade–Varchenko, where A_k singularities are stable.
- Uniformity over all p ∈ ℝ² would also hold, since for large |p| the integral is non-stationary. Compact K' is a weaker, correct choice.

**Findings.**
- MINOR: `(∀ σ, ∀ k ∈ K, FoldOrNondeg (Ψ σ) k)` imposes the condition at every point of K, critical or not, and independently of K'. This is a stronger hypothesis than the classical one, which needs it only at critical points of Ψ_σ + p· for p ∈ K'. For example, Ψ = k₁⁴ + k₂² with K' chosen to avoid critical points near the origin is excluded. It is documented and makes the theorem weaker but still correct. Flag it only if S4's phases fail it at non-critical points of K.
- NIT: `∀ (Λ : Type)` has the same universe-0 restriction as in S2.1.

## Item 4: is C² amplitude regularity plausible?
Yes; it is known for S2.2 and, I believe, standard for S3.
- **S2.2:** Hörmander, Thm 7.7.5 with k = 1 in dimension 2 is exactly "C⁴ phase, C²₀ amplitude, bound C ω^{-1} Σ_{|α|≤2} sup|D^α u|". This is the known result, not merely plausible. It avoids the Morse lemma, which would lose derivatives (a C⁴ phase gives only C² Morse coordinates and a C¹ Jacobian). For quadratic phases, even H^{1+ε} amplitude suffices via ‖û‖_{L¹}.
- **S3:** the route above uses two derivatives of A. One-dimensional stationary phase in y with remainder O(m^{-1}) needs the C² amplitude. van der Corput in x needs only b ∈ C¹, and b(x) = A(x, y*(x))·(∂_y²Ψ)^{-1/2} is C¹ (indeed C²). The O(m^{-1}) remainder is ≤ m^{-5/6}. So the m^{-5/6} bound with constants depending on derivatives of A of order ≤ 2 is plausible, and I believe it is correct.
- **Phase regularity:** C⁴ matches Hörmander's C^{3k+1} with k = 1. It also gives y* ∈ C³, so φ''' is continuous.

## Findings summary
| # | Severity | Statement | Lean text | Note |
|---|---|---|---|---|
| 1 | MINOR | S3 | `(∀ σ, ∀ k ∈ K, FoldOrNondeg (Ψ σ) k)` | Imposed at every point of K, not only at critical points for p ∈ K'. A stronger hypothesis than classical; documented; not wrong. |
| 2 | NIT | S2.1, S3 | `∀ (Λ : Type) [TopologicalSpace Λ] [CompactSpace Λ]` | Universe 0 only; fine for Λ ⊆ ℝ. |
| 3 | NIT | S2.2 | `∀ (Ψ : ℝ × ℝ → ℝ) …` | Single phase, no family uniformity (docs agree). |
| 4 | NIT | S3 | `p ∈ K'` with `IsCompact K'` | Uniformity over all of ℝ² would also hold; compact K' is weaker but correct. |
| 5 | NIT | S2.1 | `(∀ k ∈ K, GradLower (Ψ σ) p k c)` | On K rather than on supp A; documented and needed for C to be uniform in A. |

The `dd`, `ddd`, `hessDet`, `IsCritical`, `GradLower`, `AmpBound` and `oscInt2` definitions mean what the header says. For `dd` the argument order is D²Ψ(k)(w, v), which is irrelevant by symmetry for C² functions.
