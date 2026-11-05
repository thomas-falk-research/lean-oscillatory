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
