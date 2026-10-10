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

#print axioms LogSobolev.mul_log_le_mul_log_add_sub
#print axioms LogSobolev.integral_mul_log_le_entropy_of_integral_pos
#print axioms LogSobolev.integral_mul_log_le_entropy
#print axioms LogSobolev.continuous_parametric_entropy
#print axioms LogSobolev.entropy_marginal_le_integral_entropy
#print axioms LogSobolev.entropy_prod_le_integral_entropy_add
#print axioms LogSobolev.entropy_prod_le_integral_entropy_add_of_continuous_pos
#print axioms LogSobolev.entropy_prod_le_integral_entropy_add_of_continuous

#print LogSobolev.entropy_prod_le_integral_entropy_add_of_continuous
