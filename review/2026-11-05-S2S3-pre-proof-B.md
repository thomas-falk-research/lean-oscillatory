<!-- Blind pre-proof review of S2.1, S2.2, S3, referee B (fresh-context agent). Prompt: review/prompts/S2S3-pre-proof.md. Read commit 5ae5589. Verbatim final report from the agent's hand-back call. -->

5ae558950e489b5b469336a61af3fb93fa26c67c
2650f1484b3252166e9442f383ad734075f60f180d595c7d6729d9737edba5ad  OscInt.Statements.FoldStatement / a837c8bd…  VdC1Statement / 66cc331d…  VdC2Statement / 30b3f96c…  VdC3Statement / 238318a7…f4a648a64bf9ab4f4  OscInt.Statements.NonStationaryStatement / 283a23fe…6f8  OscInt.Statements.StationaryPhaseStatement
(Full lines are in `build/commit/commitments.txt`. I've shortened the hashes here.)

# Referee B: blind pre-proof statement review of S2.1, S2.2 and S3

## Summary

| Statement | Matches docs/statements.md? | True classically? | Findings |
|---|---|---|---|
| `NonStationaryStatement` | FAITHFUL | TRUE | 1 NIT |
| `StationaryPhaseStatement` | FAITHFUL | TRUE | none |
| `FoldStatement` | FAITHFUL | TRUE (only a proof sketch for the C² amplitude case; no single reference found) | 1 MINOR, 1 NIT |

There is no BLOCKER and no MAJOR finding.

**What I read:** only the allowed sources. These were `docs/statements.md` (lines 1–5 and the S2/S3 section), `OscInt/Statements/StationaryPhase.lean`, and my knowledge of the classical results. I did not open any other repository file or any Mathlib source; I relied on what I already know of the Mathlib definitions.

**What I compiled:** one scratch file, `/tmp/refB/check.lean`, which imports the statements module. It used one Lean process under `nice -n 10`, and nothing was written to the repository. It checks:
- that `-(5 : ℝ) / 6 = -5/6`;
- that `C * M / m ^ N` parses as `(C * M) / (m ^ N)`, with `m ^ N` a natural-number power;
- the `#print` output of `NonStationaryStatement` and `FoldStatement`. This shows the quantifier order is exactly as documented: `∃ C` comes after Λ, N, Ψ, K, K′, c and the hypotheses, and before A, M, σ, p, m.

## Checks that apply to all three statements

- **Lean conventions do not make anything vacuous.**
  - `oscInt2` is a Bochner integral over `ℝ × ℝ` with its product (Lebesgue) measure. Under `AmpBound n K A M` the amplitude A is continuous with `tsupport A ⊆ K`, and K is compact. The phase is continuous because it is at least C¹, so the integrand is continuous with compact support and therefore integrable. Lean's default value 0 for non-integrable integrands is never reached, and it would only weaken the claim anyway.
  - `fderiv`, `dd` and `ddd` are only applied to phases of class C^{N+1} ⊇ C¹ (S2.1) or C⁴ (S2.2, S3). So `fderiv`'s default value 0 for non-differentiable functions is never reached.
  - `rpow` only has base m ≥ 1 > 0. The only division is by `m ^ N` with m ≥ 1.
- **The amplitude bound is not vacuous.** For j = 0, `AmpBound` gives ‖A k‖ ≤ M, so M ≥ 0 is forced, which is what the bound needs. `sanity_ampBound_exists` builds a nonzero amplitude satisfying `AmpBound` for every n. A is not forced to be 0.
- **The constant C cannot depend on A, M, σ, p or m.** It is chosen before all of them. It may depend on (Λ, N, Ψ, K, c) or (Ψ, K, K′), as `docs/statements.md` intends. Using the max norm on `ℝ × ℝ` (and the induced operator norms on `iteratedFDeriv`) only changes C. `GradLower` is stated with squares, so it is the Euclidean condition |∇(Ψ + p·)| ≥ c, as in the doc.
- **The derivative helpers mean what they should.**
  - `dd Ψ k v w = D²Ψ(k) w v` and `ddd Ψ k u v w = D³Ψ(k) w v u`. For C⁴ phases these forms are symmetric, so the argument order does not matter.
  - `hessDet` is ∂₁₁∂₂₂ − ∂₁₂². `IsCritical` is ∇Ψ + p = 0.
  - In `FoldOrNondeg`, if `hessDet = 0` and `∃ v w, dd Ψ k v w ≠ 0`, the Hessian has rank exactly one. Then `∀ w, dd Ψ k v w = 0` says v spans its kernel, and `ddd Ψ k v v v ≠ 0` is the cubic term along the kernel. This is exactly the condition for a Morse or A₂ (fold) critical point.
  - Two quick checks: x⁴ + y² at 0 (an A₃ point, kernel e₁, cubic term zero) fails the definition, and x²y (D₄, Hessian zero) also fails. So the definition excludes the higher singularities it should exclude.
- **The parameter space Λ is unproblematic.** The `∀ (Λ : Type) [TopologicalSpace Λ] [CompactSpace Λ]` binders elaborate without trouble, and the product topology on `Λ × (ℝ × ℝ)` is the one meant. An empty Λ makes an instance trivially true, but the statement is still quantified over all Λ. The compactness arguments below do not need Hausdorffness: a continuous real function on a compact space still attains its minimum.

## NonStationaryStatement (S2.1)

**Verdict: FAITHFUL and TRUE.**

**Proof sketch.** Write Φ = Ψ_σ + p·. Integrate by parts N times using L = (∇Φ·∇)/(im|∇Φ|²).
- After N transposes, (Lᵗ)ᴺA is a sum of terms. Each term is ∂^βA (|β| ≤ N) times a product of derivatives ∂^γΦ (1 ≤ |γ| ≤ N+1), divided by |∇Φ|^{2s}.
- Count degrees in ∇Φ: each step contributes ∇Φ/|∇Φ|², of degree −1, and each derivative of that factor lowers the degree by one more. So every term is at most |∇Φ|^{−N−j} times bounded factors. These factors are derivatives of Ψ_σ of order 2 to N+1, and they do not depend on p.
- Those derivatives are bounded uniformly on Λ × K, because `FamilyCk (N+1)` gives joint continuity and Λ × K is compact. Since |∇Φ| ≥ c on K ⊇ supp A, every term is bounded by C(c) times M, uniformly in σ, uniformly in p, and in fact better as |p| → ∞.
- The case N = 0 is trivial: |I| ≤ M·vol(K).

The regularity counts are right: a C^{N+1} phase and a C^N amplitude. The gradient bound is imposed on all of K, not only on supp A, so there is no boundary issue. Values of m near 1 are absorbed into C.

**Finding.**
- NIT: `∀ (Λ : Type)` limits Λ to universe 0. This is harmless for the intended use (parameters ε ∈ [0, ε₀] ⊂ ℝ), but `Type*` would be more general. The same applies to `FoldStatement` and `FamilyCk`.

## StationaryPhaseStatement (S2.2)

**Verdict: FAITHFUL and TRUE.**

**Lean hypothesis.** `(∀ p ∈ K', ∀ k ∈ K, IsCritical Ψ p k → hessDet Ψ k ≠ 0)` matches the doc word for word.

**Uniformity.** The set {(p, k) ∈ K′ × K : critical} is compact, and H ≠ 0 on it. Two situations could look dangerous, and neither is:
- *Degenerate critical points approaching K from outside.* If degenerate critical points k_p ∉ K of Ψ + p· accumulated at ∂K as p → p₀ ∈ K′, the limit would be a degenerate critical point in K, which the hypothesis rules out. So degenerate critical points stay a uniform positive distance from K.
- *Critical points on ∂K.* These are covered because the hypothesis is imposed on the closed set K.

Every point of K′ × K therefore has a product neighbourhood on which either |∇Φ| ≥ c > 0, or there is a unique nondegenerate critical point with |H| ≥ δ that moves continuously with p (implicit function theorem). Take finitely many such neighbourhoods. For each of the finitely many p₀, fix a partition of unity in k. The cut-off amplitudes χ_i A have C² norm at most C·M.

**Is the C² amplitude enough for m⁻¹? (item 4) Yes, and this is a known result.** Hörmander, ALPDO I, Theorem 7.7.5, with k = 1: if f ∈ C^{3k+1} = C⁴, u ∈ C₀^{2k} = C₀², and x₀ is the only critical point, nondegenerate, then

|∫ u e^{iωf} − e^{iωf(x₀)} (det(ωf″(x₀)/2πi))^{−1/2} u(x₀)| ≤ C ω^{−1} Σ_{|α|≤2} sup|D^α u|.

In dimension n = 2 the main term is O(ω^{−1}|u(x₀)|), so |I| ≤ C ω^{−1} ‖u‖_{C²}.

The constant stays bounded when f is bounded in C⁴ and |x − x₀|/|f′(x)| is bounded. Both hold here: Ψ is fixed, p ranges over the compact set K′, and |H| ≥ δ near the critical points. On the pieces with no critical point, S2.1 with N = 2 (which needs a C³ phase) gives m⁻². So "C⁴ phase, C² amplitude" is exactly Hörmander's hypothesis for this rate. The naive argument via ‖Â‖_{L¹} loses a logarithm at C², but Hörmander's L² argument (H^s with s > n/2 = 1, and C² with compact support lies in H²) avoids that loss.

**Findings:** none.

## FoldStatement (S3)

**Verdict: FAITHFUL and TRUE.** I give a proof sketch for the C² amplitude case; I could not cite one theorem that states exactly this with a C² amplitude.

**Fidelity.** The hypothesis `∀ σ, ∀ k ∈ K, FoldOrNondeg (Ψ σ) k` matches the doc's condition "at every point of K". The Hessian does not depend on p, so neither does this condition.

**Uniformity over σ and k; no degeneration in the limit (item 3).** `FoldOrNondeg` is an open condition in (σ, k) under `FamilyCk 4`, which gives joint continuity of D² and D³. The reason:
- H ≠ 0 is open, and rank ≥ 1 is open.
- Near a rank-one point, the kernel direction of nearby rank-one Hessians varies continuously, so D³(v, v, v) stays away from 0.

Λ × K is compact and the condition holds at every point, including limit points. So there is a uniform δ > 0 and a neighbourhood U of K such that at every (σ, k) ∈ Λ × U either |H| ≥ δ, or ‖D²Ψ_σ‖ ≥ δ and |D³Ψ_σ(v, v, v)| ≥ δ along the unit near-kernel direction. A family where the condition "holds pointwise but degenerates in the limit" is impossible, because the limit point belongs to Λ × K and the condition is required there too.

**Proof sketch (item 4).** Work on a local patch where |∂_y²Φ| ≥ δ.
1. Apply Hörmander 7.7.5 in one variable (n = 1, k = 1, phase C⁴ in y uniformly in x, amplitude A(x, ·) ∈ C²) to the y-integral:

   ∫ e^{imΦ} A dy = m^{−1/2} a(x) e^{imφ(x)} + O(m⁻¹ M),

   where φ(x) = Φ(x, y*(x)). Here y* ∈ C³, and a(x) is built from A(x, y*(x)) and ∂_y²Φ(x, y*(x)), so a ∈ C¹ with ‖a‖_{C¹} ≤ C·M.
2. φ″ = H/∂_y²Φ. Where H = 0, φ‴ = D³Φ(v, v, v) with v = (1, y*′), which is the kernel vector. I checked this by a linear change of variables with determinant 1, which leaves H unchanged.
3. So |φ″| + |φ‴| ≥ δ′ uniformly. Van der Corput in x, applied on boundedly many intervals with k = 2 or k = 3, gives m^{−1/3}(‖a‖_∞ + ‖a′‖_{L¹}).
4. The total is m^{−5/6}·C·M. The remainder O(m⁻¹) decays faster than m^{−5/6}.

This sketch matches the lead's planned route in the doc, which rates C² as "PLAUSIBLE, not yet checked by a referee". I regard C² as sufficient. The exponent 5/6 = 1/2 + 1/3 is the oscillation exponent of the A₂ singularity, and uniformity under perturbations of A₂ is classical: Duistermaat 1974 for simple singularities, and Karpushkin's uniform estimates in two dimensions, though both usually assume smooth amplitudes. Remaining technical points for the proof (not statement defects):
- y*(x) may leave the patch; this needs either an extension of Φ in y or a non-stationary estimate in y with a uniform lower bound on |∂_yΦ|.
- Because the hypotheses hold only on K, the openness argument above must be used to extend the quantitative bounds to a neighbourhood of K, since y*(x) may lie slightly outside K.

**Findings.**
- MINOR: the S3 proof depends on the point just made. In `(∀ σ, ∀ k ∈ K, FoldOrNondeg (Ψ σ) k)`, the condition is on K only, while the x-integration uses points (x, y*(x)) that can lie just outside K. The statement is still true, because the condition is open and extends to a neighbourhood of K. No change to the statement is needed; I am noting it so the proof does it explicitly.
- NIT: as for S2.1, `Λ : Type` is universe 0.
- NIT: uniformity over all p ∈ ℝ² would also be true for S3, since the hypothesis does not depend on p and large |p| falls into the non-stationary regime. Restricting to p ∈ K′ (compact) is what the doc states, so this is not a fidelity issue.

## Answers to items 2–4 of the prompt
- **Hypotheses that cannot be met together:** none. The sanity theorems give non-degenerate instances for all three statements. For S3, `sanity_Fold_hyps` gives a rank-one point at 0 (hessDet = 0), so the fold branch is genuinely used.
- **Quantifier order of C:** correct, as confirmed by the elaborated `#print`.
- **Ill-conditioned regimes:**
  - Hessian eigenvalue tending to 0, and degeneration over the family: excluded by compactness together with the pointwise condition (S2.2 at critical points, S3 everywhere on K).
  - Critical points on ∂K, and amplitude support touching ∂K: covered, because the conditions are imposed on the closed set K.
  - |p| → ∞ in S2.1: the bound stays uniform.
  - m near 1: absorbed into C.
- **C² amplitudes:** for S2.2 this is a known result (Hörmander 7.7.5 with k = 1 and a C⁴ phase). For S3 it is plausible and, by the sketch above, true.