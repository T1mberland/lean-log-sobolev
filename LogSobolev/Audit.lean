import LogSobolev
import Lean.Util.CollectAxioms

/-! # Recursive axiom audit

This checks every declaration under `LogSobolev`, including definitions,
instances and generated auxiliary declarations, not merely selected theorems.
Only Mathlib's three usual foundational axioms are allowed.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, _) in env.constants.toList do
    if (`LogSobolev).isPrefixOf name then
      count := count + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unapproved axiom {ax} in the dependency closure of {name}"
  logInfo m!"Recursive axiom audit passed for {count} LogSobolev declarations."

#print axioms LogSobolev.entropy_nonneg
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
