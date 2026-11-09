240455ca27eb1a818a82e333caed7fa04e35faf8

# Route referee report: batch LE (T0E, T6F, T6E)

**Verdict:** the route is sound. All three blueprint parts are true as stated and follow from S1.2/S1.3 with the frozen hypotheses. The assembly proves exactly T0E and T6E from the parts (plus T6F for T6E), with no extra hypotheses. Every Mathlib name exists with a signature that fits its use. I found no BLOCKER and one MAJOR, which is about process, not mathematics.

**What I ran:** scratch files in `/tmp/routeref/` only (`A.lean`, `B.lean`). Nothing was written in the repository. I did not prove the parts.

## BLOCKER
None.

## MAJOR
**M1. Proofs of the parts are being written in the working tree while this review runs** (CONTRIBUTING steps 6 and 7; lessons 16, 23, 29).
- At 16:58 UTC, `git status` showed two untracked files dated 16:57, after HEAD (16:55):
  - `OscInt/Front/LatticeExplicitParts.lean`. Its header says it proves P-angle, P-vdc2, P-vdc3 and T6F, and it opens with a proof of `two_rpow_neg_half`.
  - `OscInt/Front/LatticeExplicitFinal.lean`.
- Tracked files were also modified but not committed: `OscInt/API.lean`, `StatementTypes.lean`, `stamps/statements.json`, `docs/api.json`, `docs/api/annotations.json`, `examples/api/Snippets.lean`. These were not there when I started.
- Step 6 says to fold the route referee's findings into a "Revision after the route referee" section before step 7 (proofs). Lessons 16 says to freeze the tree during referee runs.
- None of my findings would change a part, so the mathematics is not at risk. But the claim "route reviewed before any part was proved" is no longer available.
- Fix: park these files in the scratchpad until the review is committed, or state the order honestly in the docs.

## MINOR
**m1. The assembly is not in the default build, and the committed tree was not built with `make quick`.**
- No module imports `OscInt/Front/LatticeExplicitAssembly.lean` at HEAD: `OscInt.API` imports only `LatticeExplicitSanity`. So `make quick`, the guard and the replay never compile or check it.
- `.lake/build/lib/lean/Blueprint.olean` (16:46) is older than the commit that added `import Blueprint.LatticeExplicit` to `Blueprint.lean`. With `import Blueprint` alone, the parts are unknown identifiers, so the lessons 20 check cannot have used the built root.
- I compiled the assembly with `import OscInt` + `import Blueprint` + `import Blueprint.LatticeExplicit`. It elaborates with no name clash. `#print axioms` on `t0e_of` and `t6e_of` shows only propext, Classical.choice and Quot.sound.
- Fix: import the assembly from the final module that goes into `OscInt.API` (the untracked `LatticeExplicitFinal` seems meant for this), and run `make quick` before the next commit (lessons 35).

**m2. The record of the name checks is outside the tree.**
- The route cites `/tmp/lead/Names.lean` and says the output is "in the commit message". The commit message lists the names but not the `#check` output.
- None of the new names were added to `MathlibNames.lean`, which lessons 19 names as the check. The `#check`s are not reproducible from the tree (compare lessons 36).
- I re-ran `#check @…` on every name in the route; all exist at the pin (signatures below).

**m3. The T6F route leaves out the regrouping step.**
- Before `setIntegral_prod_mul` applies, the integrand `↑(t*(cos k₁+cos k₂) + (x₁k₁+x₂k₂)) * I` must be regrouped as `↑(t cos k₁ + x₁k₁)*I + ↑(t cos k₂ + x₂k₂)*I`.
- That needs a pointwise `ring`/`push_cast` under the cast before `Complex.ofReal_add`, `add_mul` and `Complex.exp_add`. A plain `simp_rw` with the three lemmas the route lists will not produce the product form.
- Suggest stating it as a pointwise lemma (`= lkf t x₁ k.1 * lkf t x₂ k.2`) and rewriting the set integral with `funext`.

## NIT
- **n1.** `HasDerivAt.neg` gives `HasDerivAt (-f) …` (a pi-negation, not a lambda). For `φ″ = fun x => t * -cos x`, use `HasDerivAt.fun_neg` (exists: `HasDerivAt (fun i => -f i) (-f') x`) or `.congr`.
- **n2.** `Real.rpow_neg` is stated for `x ^ (-y)`. The blueprint writes `-(1:ℝ)/2`, which is `(-1)/2`, so `neg_div` or a `show … = -(1/2) by ring` is needed. The untracked parts file already does this.
- **n3.** `rw [MeasureTheory.Measure.volume_eq_prod]` takes α and β explicitly and may hit an unintended `volume`. The two measures are defeq (I checked by `rfl`: `volume = volume.prod volume` on `ℝ × ℝ`), so `setIntegral_prod_mul (μ := volume) (ν := volume)` via `exact`/`show` is safer.

## Checks behind the verdict

### (1) Truth of the parts, and derivation from S1.2/S1.3
**`LEAngleFacts`** is true.
- `cos |x| = cos x`, and cos is decreasing on [0, π], so `cos x ≥ cos(π/4) = √2/2 = 2^{−1/2}`.
- At the endpoint |x| = π/4 the two sides are equal and the `≤` holds.
- The hypotheses of `Real.cos_le_cos_of_nonneg_of_le_pi : 0 ≤ x → y ≤ π → x ≤ y → cos y ≤ cos x` are met by x = |x|, y = π/4.

**`LEPiece2Facts`** is true and is S1.2 instantiated as follows:
- φ = fun k => t·cos k, φ′ = t·(−sin), φ″ = t·(−cos), μ = t·2^{−1/2} > 0, ψ = 1, ψ′ = 0, p = ξ.
- `HasDerivOn` needs `ContinuousOn` on Icc plus `HasDerivAt` on Ioo; both hold everywhere.
- The bound is needed only on Ioo, which is exactly what the part assumes: |φ″| = t|cos| ≥ μ.
- `sanity_amplitude_one a b` gives both `AmplitudeOn` and `ampNorm = 1`.
- I checked by `simp [oscInt]` that `oscInt (fun x => (fun k => t*cos k) x + ξ*x) (fun _ => 1) a b` equals the blueprint integrand.
- Edge cases:
  - a = b: the left side is 0 and the right side is positive.
  - Small t: the right side blows up and stays true.
  - |cos| = 2^{−1/2} at the endpoints: the hypothesis is only on Ioo, and S1.2 needs only Ioo.

**`LEPiece3Facts`** is true in the same way.
- φ‴ = t·(−(−sin)) = t·sin, |φ‴| = t|sin| ≥ μ.
- `HasDerivOn φ″ φ‴` holds.

**Constant algebra:**
- 8/√(t·2^{−1/2}) = 8·2^{1/4}·t^{−1/2}, using `Real.sqrt_eq_rpow`, `rpow_neg`, `Real.mul_rpow` (both factors ≥ 0) and `Real.rpow_mul` (base 2 ≥ 0, (−1/2)(−1/2) = 1/4).
- 18·(t·2^{−1/2})^{−1/3} = 18·2^{1/6}·t^{−1/3}, the same way with (−1/2)(−1/3) = 1/6.
- Checked numerically at t ∈ {10⁻³, 0.5, 1, 7.3, 10⁴}; agreement is exact to double precision.
- 3·8·2^{1/4} = 24·2^{1/4} and 2·18 = 36 match T0E. (A + B)² ≈ 4754.05.

### (2) The assembly
- `t0e_of : LEAngleFacts → LEPiece2Facts → LEPiece3Facts → LatticeKernel1ExplicitStatement`.
- `t6e_of : LatticeKernel1ExplicitStatement → LatticeKernelFactorStatement → LatticeLaplacianExplicitStatement`.
- Neither has extra hypotheses. Both conclusions are the frozen constants, syntactically.
- The angle conditions on all five pieces are derived correctly from P-angle via the cos shift identities.
- T6F has no blueprint part. It is a direct proof by the lead (route "Assembly"), and `t6e_of` takes it as a hypothesis. This is consistent with the route; the final T6E theorem must combine `t6e_of` with that direct proof.

### (3) The T6F route in Lean terms
Sound, apart from m3 and n3:
- `torusBox = Icc ×ˢ Icc` (checked by `rfl`).
- `volume` on ℝ × ℝ is `volume.prod volume` (checked by `rfl`).
- `setIntegral_prod_mul (f g) (s t) : ∫ z in s ×ˢ t, f z.1 * g z.2 ∂μ.prod ν = (∫ x in s, f x ∂μ) * ∫ y in t, g y ∂ν`. It needs only `SFinite` (available) and no integrability.
- `integral_Icc_eq_integral_Ioc` needs `NullSingletonClass`; `Real.nullSingletonClass_volume` exists.
- `intervalIntegral.integral_of_le (−π ≤ π)` takes Ioc to the interval integral.
- The `Int`→`ℝ` casts `(x.1 : ℝ)` match between `latticeKernel` and `latticeKernel1`.

### (4) Mathlib names
All exist at the pin with signatures that fit their use:
- `OscInt.vanDerCorput_two`, `OscInt.vanDerCorput_three`, `sanity_amplitude_one`
- `Real.cos_abs`, `Real.cos_le_cos_of_nonneg_of_le_pi`, `Real.cos_pi_div_four`
- `Real.sqrt_eq_rpow`, `Real.rpow_neg {x} (0 ≤ x) y`, `Real.mul_rpow`, `Real.rpow_mul`, `Real.rpow_le_rpow_of_exponent_le (1 ≤ x) (y ≤ z)`, `Real.rpow_natCast`
- `Real.hasDerivAt_cos`, `Real.hasDerivAt_sin`, `HasDerivAt.const_mul (c)`, `HasDerivAt.neg`
- `intervalIntegral.integral_add_adjacent_intervals`, `Continuous.intervalIntegrable`, `intervalIntegral.integral_of_le`
- `norm_add_le`, `norm_mul`, `mul_le_mul`
- `Real.cos_sub_pi`, `Real.cos_add_pi`, `Real.cos_sub_pi_div_two`, `Real.cos_add_pi_div_two`
- `Complex.ofReal_add`, `Complex.exp_add`
- `MeasureTheory.Measure.volume_eq_prod`, `MeasureTheory.setIntegral_prod_mul`, `MeasureTheory.integral_Icc_eq_integral_Ioc`

None is renamed or has an unexpected hypothesis. The caveats are n1 (`HasDerivAt.neg` gives pi-negation) and n2 (`rpow_neg` takes `-y`, not `(-1)/2`).
