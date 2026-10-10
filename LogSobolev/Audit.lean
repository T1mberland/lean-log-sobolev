import LogSobolev
import Lean.Util.CollectAxioms

/-! # Recursive axiom audit

This checks every declaration under `LogSobolev`, including definitions,
instances and generated auxiliary declarations, not merely selected theorems.
Only Mathlib's three usual foundational axioms are allowed. The core Lean
collector shares its visited set across roots, so each transitive dependency is
traversed once; all project declarations are still submitted as roots.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count := 0
  let mut state : CollectAxioms.State := {}
  for (name, _) in env.constants.toList do
    if (`LogSobolev).isPrefixOf name then
      count := count + 1
      let (_, next) := ((CollectAxioms.collect name).run env).run state
      state := next
      for ax in state.axioms do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unapproved axiom {ax} in the dependency closure of {name}"
  logInfo m!"Recursive axiom audit passed for {count} LogSobolev declarations."

#print axioms LogSobolev.entropy_nonneg
#print axioms LogSobolev.integrable_marginal_mul_log
#print axioms LogSobolev.integrable_slice_entropy
#print axioms LogSobolev.entropy_prod_chain
#print axioms LogSobolev.entropy_marginal_le
#print axioms LogSobolev.entropy_map
#print axioms LogSobolev.HasEnergyLSI.map
#print axioms LogSobolev.localSlope_eq_limsup_nhdsNE
#print axioms LogSobolev.localSlope_lt_top
#print axioms LogSobolev.localSlope_comp_le
#print axioms LogSobolev.localSlope_comp_isometryEquiv
#print axioms LogSobolev.measurable_localSlope
#print axioms LogSobolev.MetricLSI.map
#print axioms LogSobolev.integrable_localSlope_sq
#print axioms LogSobolev.MetricLSI.real_form
#print axioms LogSobolev.frobenius_norm_sq_eq_trace
#print axioms LogSobolev.norm_unitary_mul
#print axioms LogSobolev.norm_mul_unitary
#print axioms LogSobolev.eq_unitaryHaar
#print axioms LogSobolev.specialUnitaryHaar
#print axioms LogSobolev.phaseMap_lipschitz
#print axioms LogSobolev.entryReal_not_ae_constant
#print axioms LogSobolev.unitary_regular
#print axioms LogSobolev.intervalUniform_univ
#print axioms LogSobolev.map_intervalUniform
#print axioms LogSobolev.phaseDomainMeasure_probability
#print axioms LogSobolev.intervalPhaseMap_lipschitz

#print axioms LogSobolev.circleSpecialUnitaryMap_surjective
#print axioms LogSobolev.map_circleSpecialUnitaryMap
#print axioms LogSobolev.map_circleSpecialUnitaryMap_mul_root
#print axioms LogSobolev.phaseSliceMeasure_periodic
#print axioms LogSobolev.map_intervalPhaseMap
#print axioms LogSobolev.unitary_metricLSI_of_phaseDomain

-- Audit the definitions as well as the proof terms and their dependencies.
#print LogSobolev.entropy
#print LogSobolev.localSlope
#print LogSobolev.slopeEnergy
#print LogSobolev.MetricLSI
#print LogSobolev.unitaryHaar
#print LogSobolev.phaseMap
#print LogSobolev.intervalUniform
#print LogSobolev.phaseDomainMeasure

-- Fully elaborated types expose the chosen norm and metric instances.
set_option pp.all true in
#check LogSobolev.frobenius_norm_sq_eq_trace
set_option pp.all true in
#check LogSobolev.phaseMap_lipschitz
set_option pp.all true in
#check LogSobolev.unitary_regular

set_option pp.all true in
#check LogSobolev.map_intervalPhaseMap
set_option pp.all true in
#check LogSobolev.unitary_metricLSI_of_phaseDomain
set_option pp.all true in
#check LogSobolev.entropy_prod_chain

#print axioms LogSobolev.specialUnitaryLieAlgebra
#print axioms LogSobolev.negTracePair_self
#print axioms LogSobolev.negTracePair_lie
#print axioms LogSobolev.sum_matrixUnits_double_lie
#print axioms LogSobolev.specialUnitary_commutator_energy
set_option pp.all true in
#check LogSobolev.specialUnitary_commutator_energy
#print LogSobolev.specialUnitaryLieAlgebra
#print LogSobolev.negTracePair

#print axioms LogSobolev.hasDerivAt_det_at_one
#print axioms LogSobolev.det_exp_smul_eq_one_of_trace_zero
#print axioms LogSobolev.mem_specialUnitaryLieAlgebra_iff_curve_velocity
#print axioms LogSobolev.specialUnitaryExpCurve_speed
#print axioms LogSobolev.specialUnitary_curve_velocity_leftTranslate
#print axioms LogSobolev.specialUnitaryExpCurve_lipschitz
#print LogSobolev.specialUnitaryExpCurve
set_option pp.all true in
#check LogSobolev.mem_specialUnitaryLieAlgebra_iff_curve_velocity
set_option pp.all true in
#check LogSobolev.specialUnitaryExpCurve_speed

#print axioms LogSobolev.specialUnitaryAlgebraInnerProductSpace
#print axioms LogSobolev.specialUnitary_ad_skew
#print axioms LogSobolev.specialUnitaryAdjointIsometry
#print axioms LogSobolev.specialUnitaryAdjoint_lie
#print axioms LogSobolev.specialUnitaryAdjoint_exp_derivative
#print axioms LogSobolev.specialUnitary_killing_self
#print axioms LogSobolev.specialUnitary_commutator_energy_basis_independent
#print axioms LogSobolev.specialUnitary_killing_self_nonpos
#print LogSobolev.specialUnitaryAlgebraInnerProductSpace
set_option pp.all true in
#check LogSobolev.specialUnitary_killing_self
set_option pp.all true in
#check LogSobolev.specialUnitaryAdjoint_exp_derivative

#print axioms LogSobolev.matrix_real_trace_ad_sq
#print axioms LogSobolev.matrix_real_trace_eq_twice_skew
#print axioms LogSobolev.specialUnitary_killing_eq_skew_trace
#print axioms LogSobolev.specialUnitary_killing_self_eq
#print axioms LogSobolev.specialUnitary_killing_eq_inner
#print axioms LogSobolev.specialUnitary_orthonormal_commutator_energy
#print LogSobolev.tracelessSkewSubmodule
#print LogSobolev.specialUnitaryTracelessSkewEquiv
set_option pp.all true in
#check LogSobolev.specialUnitary_killing_self_eq
set_option pp.all true in
#check LogSobolev.specialUnitary_orthonormal_commutator_energy

#print axioms LogSobolev.det_matrix_exp
#print axioms LogSobolev.matrixExpLocalHomeomorph
#print axioms LogSobolev.matrixLog_hasStrictFDerivAt_one
#print axioms LogSobolev.matrixLog_contDiffAt_one
#print axioms LogSobolev.exists_specialUnitary_exp_neighborhood
#print axioms LogSobolev.exists_specialUnitary_exp_homeomorph
#print LogSobolev.matrixExpLocalHomeomorph
set_option pp.all true in
#check LogSobolev.exists_specialUnitary_exp_homeomorph
set_option pp.all true in
#check LogSobolev.matrixLog_contDiffAt_one

#print axioms LogSobolev.exists_specialUnitary_analytic_exp
#print axioms LogSobolev.specialUnitaryExpChart
#print axioms LogSobolev.specialUnitaryChartedSpace
#print axioms LogSobolev.specialUnitaryAlgebraProjection_val
#print axioms LogSobolev.specialUnitary_chart_transition_contDiffOn
#print axioms LogSobolev.specialUnitaryIsManifold
#print LogSobolev.specialUnitaryExpChart
#print LogSobolev.specialUnitaryChartedSpace
set_option pp.all true in
#check LogSobolev.specialUnitaryIsManifold
set_option pp.all true in
#check LogSobolev.specialUnitary_chart_transition_contDiffOn

#print axioms LogSobolev.specialUnitary_val_contMDiff
#print axioms LogSobolev.contMDiff_specialUnitary_iff
#print axioms LogSobolev.specialUnitary_mul_contMDiff
#print axioms LogSobolev.specialUnitary_inv_contMDiff
#print axioms LogSobolev.specialUnitaryLieGroup
#print axioms LogSobolev.specialUnitary_exp_contMDiff
set_option pp.all true in
#check LogSobolev.contMDiff_specialUnitary_iff
#print LogSobolev.specialUnitaryLieGroup

#print axioms LogSobolev.specialUnitary_val_hasMFDerivAt
#print axioms LogSobolev.specialUnitary_mfderiv_val_norm
set_option pp.all true in
#check LogSobolev.specialUnitary_val_hasMFDerivAt
set_option pp.all true in
#check LogSobolev.specialUnitary_mfderiv_val_norm

#print axioms LogSobolev.rightMul_lieBracket
#print axioms LogSobolev.rightMulDeriv_commutator
#print axioms LogSobolev.specialUnitary_mfderiv_mul_left_apply
#print axioms LogSobolev.specialUnitary_mulInvariantVectorField_val
#print axioms LogSobolev.specialUnitary_exists_local_smooth_extension
#print axioms LogSobolev.specialUnitaryDeriv_contMDiff
#print axioms LogSobolev.specialUnitaryDeriv_commutator
#print LogSobolev.specialUnitaryDeriv
#print LogSobolev.specialUnitaryLocalRetraction
set_option pp.all true in
#check LogSobolev.specialUnitary_exists_local_smooth_extension
set_option pp.all true in
#check LogSobolev.specialUnitaryDeriv_commutator

#print axioms LogSobolev.sum_sq_sub_transpose_le
#print axioms LogSobolev.specialUnitary_dual_commutator_energy
#print axioms LogSobolev.specialUnitary_second_derivative_energy_lower_bound
#print axioms LogSobolev.specialUnitaryDeriv_twice_mul
#print axioms LogSobolev.specialUnitaryLaplacian_contMDiff
#print axioms LogSobolev.specialUnitaryGamma_eq
#print axioms LogSobolev.specialUnitaryGamma_nonneg
#print LogSobolev.specialUnitaryLaplacian
#print LogSobolev.specialUnitaryGamma
set_option pp.all true in
#check LogSobolev.specialUnitary_second_derivative_energy_lower_bound
set_option pp.all true in
#check LogSobolev.specialUnitaryGamma_eq

#print axioms LogSobolev.sum_squares_commute_of_skew_coefficients
#print axioms LogSobolev.specialUnitaryDerivRepresentation
#print axioms LogSobolev.specialUnitaryDerivEnd_commutator
#print axioms LogSobolev.specialUnitaryCasimir_commute
#print axioms LogSobolev.specialUnitaryLaplacian_deriv
#print axioms LogSobolev.specialUnitaryGammaTwo_eq
#print axioms LogSobolev.specialUnitaryGammaTwo_lower_bound
#print LogSobolev.specialUnitarySmoothFunctions
#print LogSobolev.specialUnitaryDerivEnd
#print LogSobolev.specialUnitaryGammaTwo
set_option pp.all true in
#check LogSobolev.specialUnitaryLaplacian_deriv
set_option pp.all true in
#check LogSobolev.specialUnitaryGammaTwo_lower_bound

#print axioms LogSobolev.specialUnitary_hasDerivAt_mul_exp
#print axioms LogSobolev.eq_specialUnitaryHaar
#print axioms LogSobolev.specialUnitary_integral_deriv_eq_zero
#print axioms LogSobolev.specialUnitary_integral_mul_deriv
#print axioms LogSobolev.specialUnitary_integral_laplacian_eq_zero
#print axioms LogSobolev.specialUnitary_integral_mul_laplacian
#print axioms LogSobolev.specialUnitary_laplacian_symmetric
#print axioms LogSobolev.specialUnitary_laplacian_nonpos
#print axioms LogSobolev.specialUnitary_integral_gammaTwo
#print axioms LogSobolev.specialUnitary_integrated_gammaTwo_lower_bound
set_option pp.all true in
#check @LogSobolev.specialUnitary_integral_mul_laplacian
set_option pp.all true in
#check @LogSobolev.specialUnitary_integrated_gammaTwo_lower_bound

#print axioms LogSobolev.hasDerivAt_integral_of_compact
#print axioms LogSobolev.hasDerivAt_entropy_of_compact
#print axioms LogSobolev.hasDerivAt_entropy_of_compact_of_integral_eq_zero
#print axioms LogSobolev.specialUnitaryDeriv_comp
#print axioms LogSobolev.specialUnitaryLaplacian_comp
#print axioms LogSobolev.specialUnitaryLaplacian_log
#print axioms LogSobolev.specialUnitaryGamma_log
#print axioms LogSobolev.specialUnitary_integral_log_mul_laplacian
#print axioms LogSobolev.specialUnitary_integrable_fisher
#print axioms LogSobolev.specialUnitary_hasDerivAt_entropy
#print axioms LogSobolev.specialUnitary_entropy_deriv_nonpos
#print axioms LogSobolev.specialUnitary_weighted_gammaTwo_log_lower_bound
set_option pp.all true in
#check @LogSobolev.hasDerivAt_entropy_of_compact
set_option pp.all true in
#check @LogSobolev.specialUnitary_hasDerivAt_entropy
set_option pp.all true in
#check @LogSobolev.specialUnitary_weighted_gammaTwo_log_lower_bound

#print axioms LogSobolev.specialUnitaryGamma_comm
#print axioms LogSobolev.specialUnitaryGamma_log_mixed
#print axioms LogSobolev.specialUnitary_mul_gamma_log_mixed
#print axioms LogSobolev.specialUnitary_integral_weighted_gammaTwo_log
#print axioms LogSobolev.specialUnitary_fisher_variation_identity
#print axioms LogSobolev.specialUnitary_fisher_variation_le
#print axioms LogSobolev.specialUnitary_hasDerivAt_fisher
#print axioms LogSobolev.specialUnitary_hasDerivAt_fisher_of_heat
#print axioms LogSobolev.specialUnitary_fisher_deriv_le
set_option pp.all true in
#check @LogSobolev.specialUnitary_fisher_variation_identity
set_option pp.all true in
#check @LogSobolev.specialUnitary_fisher_deriv_le

#print axioms LogSobolev.secondDeriv_nonneg_of_isLocalMin
#print axioms LogSobolev.secondDerivative_nonneg_of_isLocalMin
#print axioms LogSobolev.secondDerivative_nonpos_of_isLocalMax
#print axioms LogSobolev.nonneg_of_compact_strict_minimum_principle
#print axioms LogSobolev.nonneg_of_compact_minimum_principle
#print axioms LogSobolev.specialUnitaryDeriv_twice_nonneg_at_min
#print axioms LogSobolev.specialUnitary_laplacian_nonneg_at_min
#print axioms LogSobolev.specialUnitary_laplacian_nonpos_at_max
#print axioms LogSobolev.specialUnitary_heat_lower_bound
#print axioms LogSobolev.specialUnitary_heat_upper_bound
#print axioms LogSobolev.specialUnitary_heat_nonneg
#print axioms LogSobolev.specialUnitaryLaplacian_affine
#print axioms LogSobolev.specialUnitaryLinearHeat_hasDerivAt
#print axioms LogSobolev.specialUnitaryLinearHeat_lower_bound
#print axioms LogSobolev.specialUnitaryLinearHeat_pos
#print LogSobolev.specialUnitaryLinearHeatMatrix
#print LogSobolev.specialUnitaryLinearHeat
set_option pp.all true in
#check @LogSobolev.specialUnitary_laplacian_nonneg_at_min
set_option pp.all true in
#check @LogSobolev.specialUnitary_heat_nonneg
set_option pp.all true in
#check @LogSobolev.specialUnitaryLinearHeat_hasDerivAt
set_option pp.all true in
#check @LogSobolev.specialUnitaryLinearHeat_pos

#print axioms LogSobolev.derivation_mem_submodule_pow
#print axioms LogSobolev.specialUnitaryPolynomialSpace_finite
#print axioms LogSobolev.specialUnitaryDerivEnd_mem_polynomial
#print axioms LogSobolev.specialUnitaryLaplacianEnd_mem_polynomial
#print axioms LogSobolev.specialUnitaryPolynomialHeat_add
#print axioms LogSobolev.specialUnitaryPolynomialHeat_hasDerivAt_apply
#print axioms LogSobolev.specialUnitaryPolynomialHeat_pos
#print axioms LogSobolev.specialUnitaryPolynomialHeat_norm_le
#print axioms LogSobolev.specialUnitaryPolynomialHeat_integral
#print axioms LogSobolev.specialUnitaryPolynomialForwardHeat_clm_hasDerivAt
#print axioms LogSobolev.specialUnitaryPolynomialForwardHeat_hasDerivAt_entropy
#print axioms LogSobolev.specialUnitaryPolynomialForwardHeat_hasDerivAt_fisher
#print axioms LogSobolev.specialUnitaryPolynomialForwardHeat_fisher_deriv_le
#print axioms LogSobolev.le_exp_mul_of_deriv_le
#print axioms LogSobolev.specialUnitaryPolynomialForwardHeat_fisher_le_exp
#print LogSobolev.specialUnitaryAffineSpace
#print LogSobolev.specialUnitaryPolynomialSpace
#print LogSobolev.specialUnitaryPolynomialToContinuous
#print LogSobolev.specialUnitaryPolynomialNormedAddCommGroup
#print LogSobolev.specialUnitaryPolynomialLaplacian
#print LogSobolev.specialUnitaryPolynomialHeat
#print LogSobolev.specialUnitaryPolynomialForwardHeat
set_option pp.all true in
#check @LogSobolev.specialUnitaryPolynomialHeat_hasDerivAt_apply
set_option pp.all true in
#check @LogSobolev.specialUnitaryPolynomialHeat_integral
set_option pp.all true in
#check @LogSobolev.specialUnitaryPolynomialForwardHeat_hasDerivAt_fisher
set_option pp.all true in
#check @LogSobolev.specialUnitaryPolynomialForwardHeat_fisher_le_exp


#print axioms LogSobolev.expUnitary_argSelfAdjoint_of_finite_spectrum
#print axioms LogSobolev.unitary_connectedSpace_of_finite_spectrum
#print axioms LogSobolev.unitaryConnectedSpace
#print axioms LogSobolev.unitaryToSpecialUnitary_continuous
#print axioms LogSobolev.unitaryToSpecialUnitary_inclusion
#print axioms LogSobolev.specialUnitaryConnectedSpace
#print axioms LogSobolev.specialUnitaryGamma_eq_zero_of_integral_eq_zero
#print axioms LogSobolev.specialUnitaryDeriv_eq_zero_of_gamma_eq_zero
#print axioms LogSobolev.specialUnitary_eq_mul_exp_of_deriv_eq_zero
#print axioms LogSobolev.specialUnitary_isLocallyConstant_of_laplacian_eq_zero
#print axioms LogSobolev.specialUnitary_eq_const_of_laplacian_eq_zero
#print axioms LogSobolev.specialUnitary_eq_mean_of_integral_gamma_eq_zero
#print LogSobolev.unitaryDetCorrection
#print LogSobolev.unitaryToSpecialUnitary
set_option pp.all true in
#check @LogSobolev.unitaryConnectedSpace
set_option pp.all true in
#check @LogSobolev.specialUnitaryConnectedSpace
set_option pp.all true in
#check @LogSobolev.specialUnitary_eq_const_of_laplacian_eq_zero
set_option pp.all true in
#check @LogSobolev.specialUnitary_eq_mean_of_integral_gamma_eq_zero


#print axioms LogSobolev.specialUnitaryPolynomial_energy_continuous
#print axioms LogSobolev.specialUnitaryPolynomial_entropy_continuous
#print axioms LogSobolev.specialUnitary_integral_gamma_le_mul_fisher
#print axioms LogSobolev.specialUnitaryPolynomialForwardHeat_energy_tendsto_zero
#print axioms LogSobolev.specialUnitaryPolynomialForwardHeat_tendsto_mean
#print axioms LogSobolev.specialUnitaryPolynomialForwardHeat_entropy_tendsto_zero
#print axioms LogSobolev.initial_le_div_of_dissipation_decay
#print axioms LogSobolev.specialUnitaryGamma_sq_add_const
#print axioms LogSobolev.specialUnitary_fisher_sq_add_const_le
#print axioms LogSobolev.specialUnitaryPolynomial_entropy_le_fisher
#print axioms LogSobolev.specialUnitaryPolynomial_entropy_sq_le
#print LogSobolev.specialUnitaryPolynomialConst
set_option pp.all true in
#check @LogSobolev.specialUnitaryPolynomialForwardHeat_tendsto_mean
set_option pp.all true in
#check @LogSobolev.specialUnitaryPolynomialForwardHeat_entropy_tendsto_zero
set_option pp.all true in
#check @LogSobolev.specialUnitaryPolynomial_entropy_le_fisher
set_option pp.all true in
#check @LogSobolev.specialUnitaryPolynomial_entropy_sq_le


#print axioms LogSobolev.localSlope_eq_of_hasDerivAt
#print axioms LogSobolev.specialUnitary_isometry_mul_left
#print axioms LogSobolev.specialUnitaryDeriv_le_localSlope
#print axioms LogSobolev.specialUnitaryGradient_norm_sq
#print axioms LogSobolev.specialUnitaryDeriv_gradient
#print axioms LogSobolev.specialUnitaryGamma_le_localSlope_sq
#print axioms LogSobolev.specialUnitaryPolynomial_exists_contDiff_extension
#print axioms LogSobolev.specialUnitaryPolynomial_locallyLipschitz
#print axioms LogSobolev.specialUnitary_integral_gamma_le_slopeEnergy
#print axioms LogSobolev.specialUnitaryPolynomial_metric_entropy_sq_le
#print axioms LogSobolev.specialUnitaryPolynomial_slopeEnergy_ne_top
#print axioms LogSobolev.specialUnitaryPolynomial_entropy_sq_le_slope
#print LogSobolev.specialUnitaryGradient
set_option pp.all true in
#check @LogSobolev.specialUnitaryGamma_le_localSlope_sq
set_option pp.all true in
#check @LogSobolev.specialUnitaryPolynomial_metric_entropy_sq_le
set_option pp.all true in
#check @LogSobolev.specialUnitaryPolynomial_entropy_sq_le_slope
#print axioms LogSobolev.continuous_integral_continuousMap_uniform
#print axioms LogSobolev.continuous_entropy_continuousMap
#print axioms LogSobolev.continuous_entropy_sq_continuousMap
#print axioms LogSobolev.tendsto_entropy_sq_of_tendsto_continuousMap
#print axioms LogSobolev.specialUnitaryPolynomial_exists_linear_pullback
#print axioms LogSobolev.specialUnitaryPolynomial_exists_mul_left
#print axioms LogSobolev.specialUnitaryPolynomial_exists_mul_right
#print axioms LogSobolev.specialUnitaryPolynomial_exists_inv
#print axioms LogSobolev.specialUnitaryPolynomial_exists_inv_mul
#print axioms LogSobolev.specialUnitaryPolynomial_exists_convolution
#print axioms LogSobolev.specialUnitaryPolynomial_exists_averaging
#print axioms LogSobolev.specialUnitary_averaging_integral
#print axioms LogSobolev.specialUnitary_averaging_le
set_option pp.all true in
#check @LogSobolev.tendsto_entropy_sq_of_tendsto_continuousMap
set_option pp.all true in
#check @LogSobolev.specialUnitaryPolynomial_exists_averaging
