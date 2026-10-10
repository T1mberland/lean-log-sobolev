module

public import LogSobolev.Gaussian.LSI
public meta import Lean.Util.CollectAxioms

@[expose] public section

/-! # Recursive Gaussian dependency audit

Audit every visible declaration originating in a Gaussian module, including ported
lemmas outside the `LogSobolev` namespace, and the generic geometry bridge.
Each root's full transitive closure is inspected by Lean's axiom collector.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx.toNat]!
    if (`LogSobolev.Gaussian).isPrefixOf modName ||
        modName == `LogSobolev.Geometry.LocalSlopeFDeriv then
      count := count + 1
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unapproved axiom {ax} in dependency closure of {name}"
  if count == 0 then
    throwError "No Gaussian declarations were selected for audit"
  logInfo m!"Recursive Gaussian axiom audit passed for {count} declarations."

#print axioms LogSobolev.gaussian_entropy_sq_le_of_contDiff
#print axioms LogSobolev.gaussian_entropy_sq_le_of_contDiff_of_hasCompactSupport
#print axioms LogSobolev.gaussian_entropy_sq_le_slopeEnergy_of_contDiff
#print axioms LogSobolev.sum_sq_apply_single_eq_norm_sq
#print axioms LogSobolev.ofReal_norm_fderiv_le_localSlope
#print axioms GaussianLSI.gaussian_logSobolev_CompSmo
#print axioms GaussianSobolevReal.gaussian_logSobolev_W12_real
#print axioms GaussianLSI.gaussian_logSobolev_W12_pi

set_option pp.all true in
#check @LogSobolev.gaussian_entropy_sq_le_of_contDiff
set_option pp.all true in
#check @LogSobolev.gaussian_entropy_sq_le_slopeEnergy_of_contDiff
#print LogSobolev.standardGaussian
#print GaussianMeasure.stdGaussianE
#print GaussianMeasure.stdGaussianPi
#print GaussianLSI.gradNormSq
#print GaussianLSI.partialDeriv
#print GaussianLSI.MemW12GaussianPi
#print GaussianSobolevReal.MemW12GaussianReal
#print EfronSteinApp.CompactlySupportedSmooth
#print LogSobolev.entropy
#print LogSobolev.localSlope
#print LogSobolev.slopeEnergy
