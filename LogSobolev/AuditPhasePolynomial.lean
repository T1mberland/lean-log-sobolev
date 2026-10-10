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

#print axioms LogSobolev.phaseMul_sqrt_lipschitz
#print axioms LogSobolev.phaseMul_isometry
#print axioms LogSobolev.unitaryPhaseSlice_lipschitz
#print axioms LogSobolev.specialUnitaryPolynomial_averaging_dist_le
#print axioms LogSobolev.specialUnitaryPolynomial_exists_lipschitz_averaging
#print axioms LogSobolev.specialUnitaryPolynomialFamily_ae_differentiable
#print axioms LogSobolev.unitary_exists_phase_polynomial
#print axioms LogSobolev.unitary_exists_phase_polynomial_of_locallyLipschitz
#print axioms LogSobolev.specialUnitaryPolynomial_hasDerivAt_moving_eval
#print axioms LogSobolev.specialUnitaryPolynomial_hasDerivAt_phase_flow
#print axioms LogSobolev.frobenius_norm_sq_add_scalar
#print axioms LogSobolev.specialUnitary_phase_velocity_norm_sq

set_option pp.all true in
#check @LogSobolev.unitary_exists_phase_polynomial_of_locallyLipschitz

set_option pp.all true in
#check @LogSobolev.specialUnitaryPolynomial_hasDerivAt_phase_flow

set_option pp.all true in
#check @LogSobolev.specialUnitary_phase_velocity_norm_sq
