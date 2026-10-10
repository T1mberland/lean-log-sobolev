module

public import LogSobolev
public import Lean.Util.CollectAxioms

@[expose] public section

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

#print axioms LogSobolev.ae_intervalUniform_of_ae
#print axioms LogSobolev.phaseMul_mul
#print axioms LogSobolev.unitaryPhaseFlow_hasDerivAt
#print axioms LogSobolev.unitaryPhaseFlow_speed_sq
#print axioms LogSobolev.unitaryPhaseFlow_lipschitz
#print axioms LogSobolev.unitary_isometry_mul_right
#print axioms LogSobolev.unitary_SU_average_deriv_sq_le
#print axioms LogSobolev.unitary_phase_convolution_deriv_sq_le
#print axioms LogSobolev.unitary_phase_convolution_energy_le
#print axioms LogSobolev.lintegral_phase_decomposition
#print axioms LogSobolev.unitary_SU_average_slopeEnergy
#print axioms LogSobolev.phase_SU_average_slopeEnergy
#print axioms LogSobolev.unitary_phase_integrated_energy_le
#print axioms LogSobolev.unitary_exists_phase_polynomial_energy
#print axioms LogSobolev.unitarySUConvolution_apply
#print axioms LogSobolev.tendsto_unitarySUConvolution
#print axioms LogSobolev.tendsto_entropy_sq_unitarySUConvolution

set_option pp.all true in
#check @LogSobolev.unitary_exists_phase_polynomial_energy

set_option pp.all true in
#check @LogSobolev.tendsto_entropy_sq_unitarySUConvolution
#print LogSobolev.unitarySUConvolution
#print LogSobolev.unitaryPhaseFlow
