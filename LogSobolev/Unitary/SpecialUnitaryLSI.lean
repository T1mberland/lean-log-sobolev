import LogSobolev.Unitary.SpecialUnitaryConvolutionEnergy
import LogSobolev.Unitary.SpecialUnitaryPolynomialApproximation
import LogSobolev.Unitary.SpecialUnitaryPolynomialLSI

/-! # Logarithmic Sobolev inequality on SU(N)

For every positive dimension, normalized Haar probability on the actual matrix
special unitary group, with the unnormalized Hilbert–Schmidt metric, satisfies
LSI with constant `2/N` in the convention `Ent(f²) ≤ 2C ∫ |∇f|²`.

The result applies to every locally Lipschitz real observable. Polynomial LSI
comes from the constructed heat flow and the verified `Γ₂ ≥ (N/2)Γ` bound.
Positive polynomial convolution approximates arbitrary continuous observables
uniformly; reverse Fatou controls its differential energy by the original local
metric slope energy. Entropy continuity then passes the inequality to the limit.

This proves the SU ingredient in the appendix proof of Meckes–Meckes,
*Spectral Measures of Powers of Random Matrices*, Theorem 15 (arXiv:1210.2681).
It does not by itself prove the interval LSI or the U(N) theorem.
-/

open Matrix MeasureTheory Filter
open scoped Matrix.Norms.Frobenius Manifold ContDiff Topology ENNReal NNReal

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- SU(N) logarithmic Sobolev inequality for all locally Lipschitz real functions.
The measure is normalized Haar and the local slope uses the unnormalized HS metric.
Square, log-moment, and slope-energy integrability follow from compact regularity. -/
theorem specialUnitary_entropy_sq_le_of_locallyLipschitz (hN : 0 < Fintype.card n)
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ} (hf : LocallyLipschitz f) :
    entropy (specialUnitaryHaar n) (fun U => f U ^ 2) ≤
      (4 / (Fintype.card n : ℝ)) *
        ∫ U, (localSlope f U).toReal ^ 2 ∂specialUnitaryHaar n := by
  let b := stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := n))
  obtain ⟨p, hp, _, ht⟩ := specialUnitaryPolynomial_exists_uniform_entropy_approximation
    hN (⟨f, hf.continuous⟩ : C(Matrix.specialUnitaryGroup n ℂ, ℝ))
  have hb (j : ℕ) : entropy (specialUnitaryHaar n) (fun U => (p j).val U ^ 2) ≤
      (4 / (Fintype.card n : ℝ)) * ∫ U, (localSlope f U).toReal ^ 2 ∂specialUnitaryHaar n := by
    have h := specialUnitary_convolution_energy_le_slopeEnergy b hf
      (specialUnitaryPolynomialToContinuous j (specialUnitaryPowerKernel j))
      (specialUnitaryPowerKernel_nonneg j) (specialUnitaryPowerKernel_integral hN j)
      (p j).val.contMDiff (hp j)
    rw [slopeEnergy_eq_ofReal_integral hf] at h
    have hr : (∫ U, specialUnitaryGamma b (p j).val (p j).val U ∂specialUnitaryHaar n) ≤
        ∫ U, (localSlope f U).toReal ^ 2 ∂specialUnitaryHaar n :=
      (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun U => sq_nonneg _)).mp h
    exact (specialUnitaryPolynomial_entropy_sq_le b j hN (p j)).trans
      (mul_le_mul_of_nonneg_left hr (by positivity))
  exact le_of_tendsto ht (Eventually.of_forall hb)

/-- Normalized Haar probability on SU(N) satisfies metric LSI with constant `2/N`
for every positive dimension, including the trivial group SU(1). -/
theorem specialUnitary_metricLSI (hN : 0 < Fintype.card n) :
    MetricLSI (specialUnitaryHaar n) (2 / (Fintype.card n : ℝ≥0)) := by
  intro f hf _ _
  have h := ENNReal.ofReal_le_ofReal (specialUnitary_entropy_sq_le_of_locallyLipschitz hN hf)
  rw [ENNReal.ofReal_mul (by positivity), ← slopeEnergy_eq_ofReal_integral hf] at h
  have hc : ENNReal.ofReal (4 / (Fintype.card n : ℝ)) =
      2 * ((2 / (Fintype.card n : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hN)]
    rw [ENNReal.coe_div (by exact_mod_cast (Nat.ne_of_gt hN) : (Fintype.card n : ℝ≥0) ≠ 0)]
    simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast, ENNReal.coe_ofNat, ENNReal.coe_natCast]
    rw [← mul_div_assoc]
    norm_num
  rwa [hc] at h

end LogSobolev
