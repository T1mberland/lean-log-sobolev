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

#print axioms LogSobolev.intervalUniform_entropy_sq_le_of_ae_hasDerivAt
#print axioms LogSobolev.specialUnitaryPolynomialFamily_deriv_measurable
#print axioms LogSobolev.specialUnitaryPolynomialFamily_deriv_sq_integrable
#print axioms LogSobolev.polynomialPhase_interval_entropy_sq_le
#print axioms LogSobolev.polynomialPhase_entropy_sq_le
#print axioms LogSobolev.phase_entropy_sq_le_energy
#print axioms LogSobolev.entropy_phase_decomposition
#print axioms LogSobolev.unitarySUConvolution_entropy_sq_le
#print axioms LogSobolev.unitary_entropy_sq_le_pi_of_locallyLipschitz
#print axioms LogSobolev.unitary_entropy_sq_le_of_locallyLipschitz
#print axioms LogSobolev.unitary_metricLSI
#print axioms LogSobolev.specialUnitary_metricLSI
#print axioms LogSobolev.unitary_regular
#print axioms LogSobolev.entryReal_not_ae_constant
#print axioms LogSobolev.frobenius_norm_sq_eq_trace
#print axioms LogSobolev.map_intervalPhaseMap

set_option pp.all true in
#check @LogSobolev.unitary_metricLSI

set_option pp.all true in
#check @LogSobolev.unitary_entropy_sq_le_of_locallyLipschitz

set_option pp.all true in
#check @LogSobolev.unitary_entropy_sq_le_pi_of_locallyLipschitz

set_option pp.all true in
#check @LogSobolev.unitary_regular

set_option pp.all true in
#check @LogSobolev.frobenius_norm_sq_eq_trace
#print LogSobolev.MetricLSI
#print LogSobolev.localSlope
#print LogSobolev.slopeEnergy
#print LogSobolev.entropy
#print LogSobolev.unitaryHaar
#print LogSobolev.intervalUniform
