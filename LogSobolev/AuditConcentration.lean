module

public import LogSobolev
public meta import Lean.Util.CollectAxioms

@[expose] public section

/-! Recursively audit all visible project declarations by originating module,
including upstream namespaces in the Gaussian ports. -/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx.toNat]!
    if (`LogSobolev).isPrefixOf modName then
      count := count + 1
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unapproved axiom {ax} in dependency closure of {name}"
  if count == 0 then
    throwError "No project declarations were selected for audit"
  logInfo m!"Recursive project concentration axiom audit passed for {count} declarations."

#print axioms LogSobolev.herbst_ratio_nonpos
#print axioms LogSobolev.quadratic_bound_of_herbst
#print axioms LogSobolev.entropy_exp_eq_mgf_mul
#print axioms LogSobolev.hasSubgaussianMGF_of_entropy_exp_bound
#print axioms LogSobolev.localSlope_comp_hasDerivAt_le
#print axioms LogSobolev.MetricLSI.entropy_exp_le
#print axioms LogSobolev.MetricLSI.hasSubgaussianMGF_of_compact
#print axioms LogSobolev.MetricLSI.measure_ge_le
#print axioms LogSobolev.MetricLSI.measure_le_le
#print axioms LogSobolev.MetricLSI.measure_abs_ge_le
#print axioms LogSobolev.hasSubgaussianMGF_of_uniform_approximation
#print axioms LogSobolev.unitary_hasSubgaussianMGF
#print axioms LogSobolev.unitary_measure_ge_le
#print axioms LogSobolev.unitary_measure_le_le
#print axioms LogSobolev.unitary_measure_abs_ge_le
#print axioms LogSobolev.specialUnitary_hasSubgaussianMGF
#print axioms LogSobolev.specialUnitary_measure_ge_le
#print axioms LogSobolev.specialUnitary_measure_le_le
#print axioms LogSobolev.specialUnitary_measure_abs_ge_le
#print axioms LogSobolev.gaussian_integrable_exp_mul
#print axioms LogSobolev.gaussian_hasSubgaussianMGF_of_contDiff
#print axioms LogSobolev.gaussian_hasSubgaussianMGF
#print axioms LogSobolev.gaussian_measure_ge_le
#print axioms LogSobolev.gaussian_measure_le_le
#print axioms LogSobolev.gaussian_measure_abs_ge_le
#print axioms GaussianSobolev.mollify_lipschitzWith
#print axioms GaussianSobolev.mollify_smooth_of_lipschitz
#print axioms GaussianSobolev.mollify_dist_le_of_lipschitz'

set_option pp.all true in
#check @LogSobolev.MetricLSI.hasSubgaussianMGF
set_option pp.all true in
#check @LogSobolev.MetricLSI.hasSubgaussianMGF_of_compact
set_option pp.all true in
#check @LogSobolev.unitary_measure_abs_ge_le
set_option pp.all true in
#check @LogSobolev.specialUnitary_measure_abs_ge_le
set_option pp.all true in
#check @LogSobolev.gaussian_hasSubgaussianMGF
set_option pp.all true in
#check @LogSobolev.gaussian_measure_abs_ge_le
#print ProbabilityTheory.HasSubgaussianMGF
#print LogSobolev.MetricLSI
#print LogSobolev.localSlope
#print LogSobolev.slopeEnergy
#print LogSobolev.entropy
#print LogSobolev.unitaryHaar
#print LogSobolev.specialUnitaryHaar
#print LogSobolev.standardGaussian
#print GaussianMeasure.stdGaussianE
#print GaussianMeasure.stdGaussianPi
#print GaussianSobolev.mollify
