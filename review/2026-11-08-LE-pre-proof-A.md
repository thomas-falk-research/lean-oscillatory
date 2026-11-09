af2a6e8e (HEAD af2a6e8)

# Referee A: blind pre-proof review of batch LE (T0E, T6F, T6E)

**What I did.** I read every file the brief lists. I ran numerical checks in Python (standard library only): composite Gauss–Legendre with 20 nodes per panel, a rank-1 Fibonacci lattice rule for the 2D kernel, and a bisection to find where the bounds start beating the trivial ones. I compiled one scratch Lean file, `/tmp/refereeA/Parse.lean`, which only checks how exponents parse, prints the elaborated statements, evaluates `0 ^ (-1/2)`, and proves one general rpow identity. I did not prove any LE statement. I wrote nothing in the repository. Scratch files are in `/tmp/refereeA/`.

**Summary.** I found no BLOCKER. All three statements are FAITHFUL to `docs/statements.md` and, in my judgement, TRUE. I found no counterexample, and the derivation routes check out. There is one MAJOR presentation finding (it needs a docs change only, no re-freeze), plus several MINOR and NIT findings.

## 1. Fidelity and truth

**`latticeKernel1`.** The definition is `∫ k in (-Real.pi)..Real.pi, Complex.exp (↑(t * Real.cos k + ξ * k) * Complex.I)`.
- `#print` shows the cast `↑(…)` wrapping the whole real phase before the multiplication by `I`.
- The interval is oriented with −π < π, so the sign is correct.
- Numerical spot checks: I(0,0) = 2π (error 4e-15), I(0,1) = 0 (9e-16), and I(1,0)/2π = 0.7651976866 = J₀(1). This is Bessel's integral I(t,n) = 2π iⁿ Jₙ(t), as the docstring says.

**Exponent parsing.** In Lean, `-(1 : ℝ) / 3` is `(-1)/3`, which equals `-(1/3)`. The same holds for `-(1:ℝ)/2` and `-(2:ℝ)/3`; `norm_num` confirms all three.
- `(2:ℝ)^((1:ℝ)/4)` and the `t ^ …` terms are `Real.rpow`.
- The outer `(…) ^ 2` in T6E is `Monoid.npow` with ℕ exponent 2. That is the intended value.
- `Real.zero_rpow` confirms `0 ^ (-(1:ℝ)/2) = 0`. So T0E would be false at t = 0 (take ξ = 0, where |I| = 2π). The hypothesis `0 < t` is necessary and correct.

**T0E: FAITHFUL** to the docs. Taking ξ real is stronger than integer ξ, as the docs disclose.
- TRUE numerically. I checked t from 1e-4 to 1e3 (141 log-spaced points). At each t I used ξ ∈ {0, ±0.5, −1.3, √2, ±t, t+0.37, t+2t^{1/3}+0.11, t − t^{1/3}}, a band t + d·t^{1/3}, and 6 random real ξ. The worst ratio |I|/bound was 0.0859, at (t, ξ) = (1000, 992).
- Asymptotically the ratio tends to 2π·0.675/B ≈ 0.105, so it stays below 1.
- Against the classical facts:
  - It is consistent with Landau's bound (sup t^{1/3}|Jₙ(t)| ≈ 0.7858, i.e. 4.94 t^{−1/3} in this normalisation). B ≈ 40.4 is about 8× Landau's constant, and about 9.5× the large-t truth 2π·0.675.
  - The statement does not encode Bessel or Landau, and the docs say so.

**T6F: FAITHFUL.**
- `latticeKernel` is a set integral over `torusBox = Icc ×ˢ Icc` under `volume` on ℝ×ℝ, which is the product Lebesgue measure.
- The integrand factors exactly, since exp(↑(a+b)·I) = exp(↑a·I)·exp(↑b·I).
- The interval integral is the integral over Ioc, which agrees with the integral over Icc almost everywhere.
- The casts `(x.1 : ℝ)` from ℤ match on both sides.
- Nothing restricts t, and none is needed: the identity holds for every real t, including t ≤ 0.
- Numerically, a non-product rank-1 lattice rule (N = 121393, shifted) against the products of 1D values gives agreement to at most 6e-14 at (t, x) = (−2.5, (1,−2)), (0, (0,0)), (0, (2,1)), (−7.1, (3,−4)) and (4, (−3,5)).

**T6E: FAITHFUL** to T6 with an explicit constant (A+B)² ≈ 4754.05.
- TRUE numerically: the worst ratio over t ∈ [1, 100] is 0.00486, matching the pre-registration's 0.0048.
- The constant is explicit and is placed after `∀ t x`, so the bound is uniform with no `∃ C`.

## 2. Derivability

**T0E from S1.2 and S1.3: yes, by the route in the docs.** I found no step that fails.

- **The pieces.** Split at ±π/4 and ±3π/4. The cos pieces are [−π,−3π/4], [−π/4,π/4] and [3π/4,π]. The sin pieces are [−3π/4,−π/4] and [π/4,3π/4].
- **Cos pieces (S1.2).** Use φ = t·cos, φ' = −t·sin, φ'' = −t·cos.
  - On each open piece |cos| > 1/√2, so the lower bound μ ≤ |φ''| holds with μ = t/√2 > 0. S1.2 only needs it on the open interval.
  - `HasDerivOn` on the closed interval holds because the functions are smooth.
- **Sin pieces (S1.3).** Use φ''' = t·sin with |sin| > 1/√2 on each open piece.
- **Amplitude.** ψ = 1 with ψ' = 0. `sanity_amplitude_one` already gives `AmplitudeOn` and `ampNorm = 1`.
- **Integrand.** `oscInt (fun x => t*cos x + ξ*x) (fun _ => 1) a b` has integrand `exp(↑(t*cos x + ξ*x) * I) * 1`. Up to the `* 1`, this is the integrand of `latticeKernel1`, with p = ξ.
- **Constant arithmetic.**
  - 8/√(t/√2) = 8·2^{1/4}·t^{−1/2}, using √t⁻¹ = t^{−1/2} for t > 0.
  - (t/√2)^{−1/3} = 2^{1/6}·t^{−1/3}.
  - Total: 3·8·2^{1/4} = 24·2^{1/4} = A and 2·18·2^{1/6} = 36·2^{1/6} = B. Both are correct.
- **Assembly.** Additivity of the interval integral needs interval integrability, which holds because the integrand is continuous; the triangle inequality then finishes the bound.
- **Numerical cross-check.** On t ∈ {0.01, …, 250} and 8 values of ξ:
  - The sum of the 5 pieces equals the full integral to 3e-15.
  - The worst per-piece ratio to the S1.2 bound is 0.33, and to the S1.3 bound 0.18.
- S1.2 and S1.3 are proved: `StatementTypes.lean` asserts `OscInt.vanDerCorput_two/three` against `VdC2/VdC3Statement`.

**T6F:** derivable by Fubini on the box plus the exponential identity, as above.

**T6E from T0E and T6F for t ≥ 1: yes.**
- T6F gives |K| = |I(t,x₁)|·|I(t,x₂)| ≤ (A t^{−1/2} + B t^{−1/3})².
- For t ≥ 1, t^{−1/2} ≤ t^{−1/3}, so this is at most ((A+B) t^{−1/3})².
- Finally (t^{−1/3})² = t^{−2/3} for t > 0. I checked this general rpow fact in Lean.

## 3. Vacuity and usefulness

- **Not vacuous.** The hypotheses are satisfiable, the kernels are nontrivial, and the decay rate t^{−2/3} is sharp (T6L).
- **What T6E adds over T6.** It replaces `∃ C` with an explicit number, which a downstream user can cite directly.
- **The bound beats the trivial one only at large t.** This is not disclosed; see the MAJOR finding below.
- **Nothing a user needs is lost relative to T6.**
  - T6 also has t ≥ 1, integer x and no (2π)^{−2}.
  - For small t, a user can combine T0E (all t > 0) with T6F themselves, or use the trivial 4π².
  - Non-integer x is meaningless for the lattice. T0E is stated for real ξ anyway.
- **The constants are honestly described as non-sharp.** The "×200" and "B ≈ 9.5× too large" figures check out: 1/0.0048 ≈ 208, and B/(2π·0.675) = 9.53.

## 4. Sanity theorems and planted controls

- **Do they test the frozen text?** Yes, the theorems are in the conditional form of lessons 33.
- **The six plants were rejected for the stated reasons.** I read the generator and the T0E-int output: the plant rejects because `↑(1/2 : ℤ)` is 0. All unplanted copies were accepted.
- **What they miss.** The structural limit is acknowledged in the file. Weakening a hypothesis or strengthening a conclusion is not detected:
  - **T0E: `0 < t ↦ 0 ≤ t`.** This makes T0E false, yet it would go undetected because the only datum is t = 8. Adding `1 ≤ t` or `8 ≤ t` to T0E would also go undetected.
  - **T6F: an added restriction on t** (`0 < t`, `1 ≤ t`) would go undetected, because the only datum is t = 3.
  - **A smaller constant in T0E or T6E.** This plant matters most, because the numerics cannot catch it either. The margins (0.086 and 0.0049) mean that even a 10× smaller constant is numerically TRUE. Only the proof via the S1 constants pins A and B.
  - **The `latticeKernel1` definition is not planted at all.** See the NIT below on what the I(0,·) facts actually pin.

## 5. Findings

**BLOCKER:** none.

**MAJOR (presentation; docs change only, no re-freeze).** The explicit bounds are weaker than the trivial bounds over a long stretch of t, and nowhere in the docs is this said.
- The trivial bounds are |I| ≤ 2π and |K| ≤ 4π².
- `24 * (2 : ℝ) ^ ((1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 2) + 36 * (2 : ℝ) ^ ((1 : ℝ) / 6) * t ^ (-(1 : ℝ) / 3)` falls below 2π only for t > 518.5.
- `(24 * … + 36 * …) ^ 2 * t ^ (-(2 : ℝ) / 3)` falls below 4π² only for t > ((A+B)²/4π²)^{3/2} = 120.42^{3/2} ≈ 1321.5.
- So on 1 ≤ t ≤ 1321, T6E says less than |K| ≤ 4π².
- `docs/statements.md`, modelling choice 3, and the Lean module doc ("about 4754") report sharpness ratios but not this crossover. A downstream user who "asked for explicit constants" should be told that the constant only has content for t ≳ 1.3·10³. They can use min(4π², …) below that.
- Recommendation: add one sentence to modelling choice 3 and to the module doc.

**MINOR.** T6E's form `(A + B)^2 * t^(-2/3)` throws away a factor up to (A+B)²/B² ≈ 2.9 at large t, compared with what T6F and T0E give directly, namely (A t^{−1/2} + B t^{−1/3})². It would help to note that users wanting the better bound should compose T6F and T0E themselves.

**MINOR.** The user's actual normalisation is left entirely to the user.
- With Δ the standard 5-point Laplacian on ℤ², the kernel of e^{itΔ} is (2π)^{−2} e^{−4it} K(2t, x). Its bound is then (2π)^{−2}(A+B)²(2t)^{−2/3} ≈ 75.9 |t|^{−2/3} for |t| ≥ 1/2, with the convention to be checked against the project's.
- Negative times rely on I(−t, ξ) = conj I(t, −ξ), equivalently |K(−t,x)| = |K(t,−x)|. This is stated in the docs (modelling choice 2) but not formalised.
- Suggestion: add a docs line giving the user-ready constant, and flag the t < 0 reduction as unformalised.

**MINOR (sanity coverage).**
- `latticeKernel1Explicit_eight` uses only t = 8, and `latticeKernelFactor_generic` only t = 3. A plant that weakens `0 < t` to `0 ≤ t` (making T0E false), or that adds `1 ≤ t` to T0E or T6F, would stay green.
- Suggestion: one extra datum at t < 1 for T0E (e.g. t = 1/8, where (1/8)^{−1/3} = 2), plus a T6F instance at t ≤ 0. These would detect added restrictions on t. `0 ≤ t` remains detectable only by review and proof.

**NIT.** The sanity file says "`I(0, 0) = 2π`, `I(0, 1) = 0` (unconditional: pins the interval `[−π, π]` and the sign and scale of `ξk`)". This overstates what they pin.
- Both facts also hold on any interval of length 2π, and with `−ξ * k` in place of `ξ * k`.
- The deviation is harmless here: under k ↦ −k and under translation, |I| and the T6F product are unchanged for integer x.
- Suggested rewording: "pins the length 2π and the integer frequency scale".

**NIT.** The docstring of `latticeKernel1Explicit_eight` says the plants detect "a changed constant". Only an increased constant is detected, as in the plant 24 ↦ 25. A decreased constant is not, which the next sentence of the docstring concedes. Suggested wording: "an enlarged constant".

**NIT.** The elaborated T6E reuses the auxiliary lemmas `LatticeKernel1ExplicitStatement._proof_k` (numeral instances). This is harmless and only cosmetic for comparator diffs. `comparator-LE.json` has `definition_names: []`, consistent with earlier batches: `latticeKernel1` lives in the shared Statements module.

**Answer key, per constant:**
| Statement | vs `docs/statements.md` | True? | Derivable as claimed? |
|---|---|---|---|
| `LatticeKernel1ExplicitStatement` | FAITHFUL; ξ real is stronger than integer ξ, as disclosed | TRUE | Yes, from S1.2 and S1.3 |
| `LatticeKernelFactorStatement` | FAITHFUL | TRUE | Yes, by Fubini, for all real t |
| `LatticeLaplacianExplicitStatement` | FAITHFUL; T6 with an explicit constant | TRUE | Yes, from T6F and T0E for t ≥ 1 |

The scratch checks are `/tmp/refereeA/chk.py` (numerics) and `/tmp/refereeA/Parse.lean` (definition and parsing facts only).
