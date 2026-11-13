# Route: batch HC (TdF, TdE′)

Lead, session 10, after the pre-proof reviews were answered (`review/2026-11-12-HC-pre-proof-answers.md`). Blueprint:
`Blueprint/Hypercubic.lean` (one `…Facts`). Assembly: `OscInt/Front/HypercubicAssembly.lean`, compiled before the part
is proved. Every Mathlib name below is `#check`ed in `MathlibNames.lean`.

## Part
- **P-fubini** `HCFubiniFacts`: for every `d` and continuous `f : Fin d → ℝ → ℂ`,
  `∫ k in hypercubeBox d, ∏ j, f j (k j) = ∏ j, ∫ x in (−π)..π, f j x`.
  `MeasureTheory.volume_pi` (the volume on `Fin d → ℝ` is `Measure.pi (fun _ => volume)`),
  `MeasureTheory.Measure.restrict_pi_pi` (restriction to a box is the product of restrictions),
  `MeasureTheory.integral_fintype_prod_eq_prod` (Fubini over a finite index type, any σ-finite factors), then each
  factor `∫ x, f x ∂(volume.restrict (Icc (−π) π)) = ∫ x in (−π)..π, f x` by `MeasureTheory.integral_Icc_eq_integral_Ioc`
  and `intervalIntegral.integral_of_le`. `d = 0` needs no special case (empty products, `Measure.pi` of the empty family
  is the Dirac mass of total mass 1).

## Assembly (lead)
- **TdF** from P-fubini: the integrand `exp(↑(t Σ_j cos k_j + Σ_j x_j k_j) · I)` equals `∏_j exp(↑(t cos k_j + x_j k_j) · I)`
  (`Finset.mul_sum`, `Finset.sum_add_distrib`, `Complex.ofReal_sum`, `Finset.sum_mul`, `Complex.exp_sum`), then P-fubini
  with `f j x = exp(↑(t cos x + x_j x) · I)` (continuous) and `latticeKernel1` unfolded.
- **TdE′** from TdF and the proved T0E′ (`OscInt.API.latticeKernel1CubeRoot`): `norm_prod`, `Finset.prod_le_prod`
  (factors nonnegative), `Finset.prod_const`, `Finset.card_fin`, and `(t^{−1/3})^d = t^{−d/3}` (`← Real.rpow_natCast`,
  `← Real.rpow_mul`).

## Revision after the route referee (2026-11-12, at 11652d7)
Verdict: route sound. `HCFubiniFacts` is true for every `d` (including `0`: the box is `univ` and the volume a Dirac
mass), and the assembly proves exactly the frozen statements (a scratch theorem from `HCFubiniFacts` to both compiles,
axioms propext, Classical.choice, Quot.sound). Every watch item (the set integral as a restricted integral by `rfl`, the
box shape for `Measure.restrict_pi_pi`, the σ-finite instances, `d = 0`) checked by compilation.
- **MINOR, adopted:** `Set.pi_univ_Icc` is a simp lemma that turns the box into a function-space `Icc`, after which
  `Measure.restrict_pi_pi` no longer matches: unfold `hypercubeBox` with `rw`, never with `simp`.
- **NIT, noted:** the continuity hypothesis of `HCFubiniFacts` is not needed (`integral_fintype_prod_eq_prod` has no
  integrability hypothesis); kept (harmless, the blueprint is not changed).
- **NIT, done:** the assembly's names (`Finset.prod_le_prod₀`, `Finset.card_univ`, `Fintype.card_fin`, `mul_pow`,
  `Finset.mul_sum`, `Finset.sum_add_distrib`, `Finset.sum_mul`) are now `#check`ed in `MathlibNames.lean`.

## The part as proved (2026-11-12)
P-fubini (`OscInt/Front/HypercubicFubini.lean`, lead, after the route referee was answered at 85d1748): `rw` with
`hypercubeBox`, `MeasureTheory.volume_pi`, `Measure.restrict_pi_pi`, `integral_fintype_prod_eq_prod`, then each factor
by `intervalIntegral.integral_of_le` and `integral_Icc_eq_integral_Ioc`, exactly as routed. Final theorems:
`OscInt/Front/HypercubicFinal.lean`.
