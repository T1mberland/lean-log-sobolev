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

#print axioms LogSobolev.interval_integral_sq_le_of_integrable
#print axioms LogSobolev.lipschitz_intervalIntegrable_deriv_sq
#print axioms LogSobolev.sq_sub_le_interval_integral_deriv_sq_of_lipschitz
#print axioms LogSobolev.sum_sq_uniform_increments_le_of_lipschitz
#print axioms LogSobolev.unitInterval_entropy_sq_le_of_lipschitzWith
#print axioms LogSobolev.ofReal_norm_deriv_le_localSlope
#print axioms LogSobolev.intervalUniform_entropy_sq_le_of_locallyLipschitz
#print axioms LogSobolev.intervalUniform_metricLSI
#print axioms LogSobolev.MetricLSI.mono
#print axioms LogSobolev.map_unitaryOnePhaseMap
#print axioms LogSobolev.unitary_fin_one_metricLSI_pi
#print axioms LogSobolev.unitary_fin_one_metricLSI
#print axioms LogSobolev.unitary_fin_one_entropy_sq_le

set_option pp.all true in
#check @LogSobolev.intervalUniform_entropy_sq_le_of_locallyLipschitz

set_option pp.all true in
#check @LogSobolev.unitary_fin_one_entropy_sq_le

set_option pp.all true in
#check @LogSobolev.unitary_fin_one_metricLSI
#print LogSobolev.intervalUniform
#print LogSobolev.unitaryHaar
#print LogSobolev.MetricLSI
#print LogSobolev.localSlope
#print LogSobolev.entropy
