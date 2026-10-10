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
