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
