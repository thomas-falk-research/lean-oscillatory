/-
Copyright (c) 2026 Thomas Falk III. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Falk III
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib

/-! Every Mathlib declaration the plan or the docs rely on by name; `make lean` fails if one disappears. -/

#check @intervalIntegral.integral_mul_deriv_eq_deriv_mul
#check @ContDiffBump
#check @exists_contMDiffMap_zero_one_of_isClosed
#check @exists_contDiff_zero_iff_one_iff_of_isClosed
#check @SmoothPartitionOfUnity
#check @IsCompact.elim_finite_subcover
#check @Metric.finite_approx_of_totallyBounded
#check @ContractingWith.fixedPoint
#check @ContractingWith.fixedPoint_lipschitz_in_map
#check @Real.contDiffAt_arccos
#check @integral_cexp_quadratic
#check @fourier_gaussian_pi
#check @fourierIntegral_gaussian
#check @taylor_mean_remainder_lagrange
#check @taylor_mean_remainder_cauchy
#check @MeasureTheory.tendsto_integral_of_dominated_convergence
#check @integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
#check @ImplicitFunctionData
#check @map_add_eq_sum_add_integral_iteratedFDeriv
#check @ImplicitFunctionData.contDiffAt_implicitFunction

-- S4.4 route (docs/proof-S44.md), checked 2026-11-06 with signatures (lessons 19): the complex Gamma integral
-- below takes a real rate `0 < r`, which is why E1 uses the Beta route.
#check @Complex.integral_cpow_mul_exp_neg_mul_Ioi
#check @Real.integral_rpow_mul_exp_neg_mul_Ioi
#check @Real.Gamma_mul_Gamma_one_sub
#check @Real.Gamma_mul_Gamma_add_half
#check @Real.Gamma_one_half_eq
#check @Real.sin_pi_div_three
#check @Complex.Gamma_mul_Gamma_eq_betaIntegral
#check @Complex.Gamma_ofReal
#check @Complex.ofReal_cpow
#check @MeasureTheory.integral_comp_rpow_Ioi_of_pos
#check @MeasureTheory.integral_image_eq_integral_abs_deriv_smul
#check @integral_comp_polarCoord_symm
#check @MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
#check @Real.range_arctan
#check @Real.arctan_injective
#check @Real.hasDerivAt_arctan
#check @Real.cos_arctan
#check @Real.sin_arctan
#check @Function.Periodic.intervalIntegral_add_eq
#check @MeasureTheory.tendsto_integral_filter_of_dominated_convergence
#check @MeasureTheory.integral_integral_swap
#check @MeasureTheory.lintegral_lintegral_swap
#check @MeasureTheory.Integrable.of_integral_ne_zero
#check @intervalIntegral.intervalIntegrable_of_integral_ne_zero
#check @MeasureTheory.setIntegral_union
#check @integral_comp_neg_Ioi
#check @integral_rpow_mul_exp_neg_mul_rpow
#check @Matrix.toLin_finTwoProd_apply
#check @LinearMap.det_toLin
#check @Matrix.det_fin_two_of
#check @intervalIntegral.integral_add_adjacent_intervals
#check @Continuous.intervalIntegrable
#check @MeasureTheory.setIntegral_prod_mul
#check @MeasureTheory.integral_Icc_eq_integral_Ioc
#check @intervalIntegral.integral_of_le
#check @MeasureTheory.Measure.volume_eq_prod
#check @Real.cos_abs
#check @Real.cos_le_cos_of_nonneg_of_le_pi
#check @Real.cos_pi_div_four
#check @Real.cos_sub_pi
#check @Real.cos_add_pi
#check @Real.cos_sub_pi_div_two
#check @Real.cos_add_pi_div_two
#check @Real.sqrt_eq_rpow
#check @Real.mul_rpow
#check @Real.rpow_mul
#check @Real.rpow_le_rpow_of_exponent_le
#check @Real.rpow_natCast
#check @Real.hasDerivAt_cos
#check @Real.hasDerivAt_sin
#check @Complex.exp_add
#check @exists_dual_vector''
#check @ContinuousLinearMap.integral_comp_comm
#check @ContinuousLinearMap.iteratedFDeriv_comp_left
#check @ContinuousLinearMap.norm_compContinuousMultilinearMap_le
