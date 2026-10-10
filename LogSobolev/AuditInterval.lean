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

#print axioms LogSobolev.TwoPoint.rothaus_lemma
#print axioms LogSobolev.TwoPoint.entropy_le_of_nonneg
#print axioms LogSobolev.TwoPoint.sq_entropy_le
#print axioms LogSobolev.integral_uniformOn_univ
#print axioms LogSobolev.uniformOn_univ_prod
#print axioms LogSobolev.entropy_uniformOn_equiv
#print axioms LogSobolev.entropy_prod_le_integral_entropy_add_of_continuous
#print axioms LogSobolev.entropy_uniformOn_prod_fin_two_sq_le
#print axioms LogSobolev.uniformGridEntropy_double_le
#print axioms LogSobolev.discreteWeightedEnergy_double_le
#print axioms LogSobolev.uniformGridEntropy_pow_two_le
#print axioms LogSobolev.uniformGridEntropy_pow_two_le_unweighted
#print axioms LogSobolev.uniformGridAverage_error_le
#print axioms LogSobolev.tendsto_uniformGridAverage_pow_two
#print axioms LogSobolev.interval_integral_sq_le
#print axioms LogSobolev.sum_sq_uniform_increments_le
#print axioms LogSobolev.tendsto_uniformGridEntropy_samples
#print axioms LogSobolev.unitInterval_entropy_sq_le_of_hasDerivAt
#print axioms LogSobolev.entropy_intervalUniform_eq_unit
#print axioms LogSobolev.intervalUniform_entropy_sq_le_of_hasDerivAt

set_option pp.all true in
#check @LogSobolev.intervalUniform_entropy_sq_le_of_hasDerivAt
#print LogSobolev.intervalUniform
#print LogSobolev.entropy
#print LogSobolev.uniformGridEntropy
#print LogSobolev.discreteWeightedEnergy
