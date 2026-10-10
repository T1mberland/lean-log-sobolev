module

public import LogSobolev.Unitary.PhaseEntropyEnergy
public import LogSobolev.Unitary.PhaseEntropyTransport
public import LogSobolev.Unitary.UnitaryPhaseIntegratedEnergy
public import LogSobolev.Unitary.UnitarySUConvolution

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Logarithmic Sobolev inequality on U(N)

Theorem 15 of Meckes–Meckes, *Spectral Measures of Powers of Random Matrices*
(arXiv:1210.2681): normalized Haar on the actual matrix unitary group, with
unnormalized Hilbert–Schmidt metric, satisfies LSI with constant `6/N`.

The proof uses positive SU convolution, a polynomial-valued Lipschitz phase
curve, slice entropy inequalities, and the exact orthogonality of central and
traceless velocities. Its intermediate entropy coefficient is `π²/N ≤ 12/N`.
All locally Lipschitz real functions are covered, including dimension one.
-/

open Matrix MeasureTheory Filter
open scoped Matrix.Norms.Frobenius NNReal ENNReal Topology

namespace LogSobolev

/-- Each actual SU-convolution approximant satisfies the required entropy bound
in terms of the original function's local-slope energy. -/
theorem unitarySUConvolution_entropy_sq_le (N : ℕ) (hN : 0 < N) (d : ℕ)
    {f : Matrix.unitaryGroup (Fin N) ℂ → ℝ} (hf : LocallyLipschitz f) :
    entropy (unitaryHaar (Fin N))
      (fun U => unitarySUConvolution d ⟨f, hf.continuous⟩ U ^ 2) ≤
      (Real.pi ^ 2 / N) * ∫ U, (localSlope f U).toReal ^ 2 ∂unitaryHaar (Fin N) := by
  let b := stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin N))
  obtain ⟨K, p, he, hp, henergy⟩ := unitary_exists_phase_polynomial_energy N hN d b hf
  have hmatch (t : ℝ) (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      unitarySUConvolution d ⟨f, hf.continuous⟩
        (phaseMul (Real.sqrt (2 / (N : ℝ))) t (specialUnitaryInclusion U)) = (p t).val U := by
    rw [unitarySUConvolution_apply, he]
    apply integral_congr_ae
    exact Eventually.of_forall fun V => by
      simp only [ContinuousMap.coe_mk, map_mul, phaseMul_mul]
  have hent := entropy_phase_decomposition N hN
    ((unitarySUConvolution d ⟨f, hf.continuous⟩).continuous.pow 2)
  simp only [Pi.pow_apply, hmatch] at hent
  have h := (phase_entropy_sq_le_energy N hN d b hp).trans
    (mul_le_mul_right henergy (ENNReal.ofReal (Real.pi ^ 2 / N)))
  rw [← hent, slopeEnergy_eq_ofReal_integral hf,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.pi ^ 2 / (N : ℝ))] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by positivity) (integral_nonneg fun U => sq_nonneg _))).mp h

/-- U(N) entropy bound with coefficient `π²/N`, for all locally Lipschitz observables. -/
theorem unitary_entropy_sq_le_pi_of_locallyLipschitz (N : ℕ) (hN : 0 < N)
    {f : Matrix.unitaryGroup (Fin N) ℂ → ℝ} (hf : LocallyLipschitz f) :
    entropy (unitaryHaar (Fin N)) (fun U => f U ^ 2) ≤
      (Real.pi ^ 2 / N) * ∫ U, (localSlope f U).toReal ^ 2 ∂unitaryHaar (Fin N) := by
  have ht := tendsto_entropy_sq_unitarySUConvolution (by simpa using hN)
    (⟨f, hf.continuous⟩ : C(Matrix.unitaryGroup (Fin N) ℂ, ℝ))
  exact le_of_tendsto ht (Eventually.of_forall fun d => unitarySUConvolution_entropy_sq_le N hN d hf)

/-- Meckes–Meckes Theorem 15 in real entropy form: exact coefficient `12/N`,
actual normalized Haar, unnormalized HS local slope, and only local Lipschitz regularity. -/
theorem unitary_entropy_sq_le_of_locallyLipschitz (N : ℕ) (hN : 0 < N)
    {f : Matrix.unitaryGroup (Fin N) ℂ → ℝ} (hf : LocallyLipschitz f) :
    entropy (unitaryHaar (Fin N)) (fun U => f U ^ 2) ≤
      (12 / (N : ℝ)) * ∫ U, (localSlope f U).toReal ^ 2 ∂unitaryHaar (Fin N) := by
  apply (unitary_entropy_sq_le_pi_of_locallyLipschitz N hN hf).trans
  apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun U => sq_nonneg _)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hp := mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d4
  nlinarith

/-- Meckes–Meckes Theorem 15: U(N) has metric logarithmic Sobolev constant `6/N`
for every positive dimension, including N=1. All finite-entropy locally Lipschitz
real observables are included; compact regularity proves their integrability. -/
theorem unitary_metricLSI (N : ℕ) (hN : 0 < N) :
    MetricLSI (unitaryHaar (Fin N)) (6 / (N : NNReal)) := by
  intro f hf _ _
  have h := ENNReal.ofReal_le_ofReal (unitary_entropy_sq_le_of_locallyLipschitz N hN hf)
  rw [ENNReal.ofReal_mul (by positivity), ← slopeEnergy_eq_ofReal_integral hf] at h
  have hc : ENNReal.ofReal (12 / (N : ℝ)) = 2 * ((6 / (N : NNReal) : NNReal) : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hN)]
    rw [ENNReal.coe_div (by exact_mod_cast (Nat.ne_of_gt hN) : (N : NNReal) ≠ 0)]
    simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast, ENNReal.coe_ofNat, ENNReal.coe_natCast]
    rw [← mul_div_assoc]
    norm_num
  rwa [hc] at h

end LogSobolev
