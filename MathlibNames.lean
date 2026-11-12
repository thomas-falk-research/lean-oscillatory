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
#check @ContinuousLinearMap.norm_restrictScalars
#check @ContinuousLinearMap.norm_iteratedFDeriv_comp_left
#check @tsupport_comp_subset
#check @notMem_tsupport_iff_eventuallyEq
#check @Continuous.integrable_of_hasCompactSupport
#check @HasCompactSupport.intro
#check @image_eq_zero_of_notMem_tsupport

-- Batch A3 route (docs/proof-A3.md), checked at the pin 2026-11-10.
#check @ContinuousLinearMap.iteratedFDeriv_comp_right
#check @LinearMap.equivOfDetNeZero
#check @LinearEquiv.toContinuousLinearEquiv
#check @hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne
#check @Convex.mul_sub_le_image_sub_of_le_deriv
#check @intervalIntegral.integral_mul_deriv_eq_deriv_mul
#check @MeasureTheory.integral_prod
#check @iteratedFDeriv_succ_apply_left
#check @Cubic.discr
#check @Cubic.discr_eq_prod_three_roots
#check @Cubic.discr_ne_zero_iff_roots_nodup

-- Batch LE2 route (docs/proof-LE2.md), checked at the pin 2026-11-11.
#check @Real.arcsin_le_iff_le_sin
#check @Real.le_arcsin_iff_sin_le
#check @Real.sin_arcsin
#check @Real.arcsin_sin
#check @Real.arcsin_nonneg
#check @Real.arcsin_le_pi_div_two
#check @Real.neg_pi_div_two_le_arcsin
#check @Real.arcsin_neg
#check @Real.arcsin_zero
#check @Real.hasDerivAt_arcsin
#check @Real.sin_ge_sub_cube
#check @Real.sin_le
#check @strictConcaveOn_sin_Icc
#check @MonotoneOn.convexOn_of_deriv
#check @ConvexOn.le_max_of_mem_Icc
#check @antitoneOn_of_deriv_nonpos
#check @monotoneOn_of_deriv_nonneg
#check @intervalIntegral.integral_eq_sub_of_hasDerivAt
#check @intervalIntegral.norm_integral_le_of_norm_le_const
#check @intervalIntegral.integral_comp_neg
#check @intervalIntegral.integral_mono_on
#check @intervalIntegral.norm_integral_le_integral_norm
#check @Real.hasDerivAt_sqrt
#check @Real.sin_pi_div_four
#check @Real.sin_pi_sub
#check @Real.cos_nonneg_of_mem_Icc
#check @Real.cos_nonpos_of_pi_div_two_le_of_le
#check @Real.strictMonoOn_sin
#check @Real.strictAntiOn_cos
#check @Complex.norm_exp_ofReal_mul_I
#check @Real.rpow_le_rpow_left_iff
#check @Real.pi_lt_d2
#check @Real.pi_gt_three
#check @ConvexOn.secant_mono
#check @ConvexOn.slope_mono_adjacent
#check @convexOn_zpow
#check @HasDerivAt.inv
#check @HasDerivAt.div
#check @intervalIntegral.integral_congr
#check @HasDerivAt.cexp
#check @HasDerivAt.ofReal_comp
#check @ContinuousOn.intervalIntegrable
#check @Real.sin_neg
#check @Real.cos_neg
#check @Real.rpow_le_rpow_of_nonpos
#check @Real.lt_sqrt
#check @Real.cos_two_mul
#check @Real.cos_sq'
#check @Real.sin_pi_div_two_sub
#check @HasDerivAt.sqrt
#check @HasDerivAt.deriv
#check @ConvexOn.add
#check @Real.sqrt_mul
#check @Real.sin_pi_div_six
#check @ConvexOn.slope_le_of_hasDerivAt
#check @antitoneOn_of_hasDerivWithinAt_nonpos
#check @convexOn_id

-- Batch HC route (docs/proof-HC.md), checked at the pin 2026-11-12.
#check @MeasureTheory.volume_pi
#check @MeasureTheory.Measure.restrict_pi_pi
#check @MeasureTheory.integral_fintype_prod_eq_prod
#check @MeasureTheory.integral_Icc_eq_integral_Ioc
#check @intervalIntegral.integral_of_le
#check @Complex.exp_sum
#check @Finset.prod_le_prod₀
#check @norm_prod
#check @Finset.prod_const
#check @Finset.card_univ
#check @Fintype.card_fin
#check @mul_pow
#check @Finset.mul_sum
#check @Finset.sum_add_distrib
#check @Finset.sum_mul

-- Batch LS route (docs/proof-LS.md), checked at the pin before the parts.
#check @NormedSpace.exp
#check @hasDerivAt_exp_smul_const
#check @NormedSpace.exp_series_hasSum_exp'
#check @Commute.exp_left
#check @ODE_solution_unique_univ
#check @lp.ext
#check @lp.norm_apply_le_norm
#check @lp.single
#check @lp.evalCLM
#check @lp.norm_rpow_eq_tsum
#check @memℓp_gen_iff
#check @Equiv.summable_iff
#check @Summable.tsum_comm'
#check @summable_prod_of_nonneg
#check @MeasureTheory.hasSum_integral_of_dominated_convergence
#check @NormedAlgebra.complexToReal
