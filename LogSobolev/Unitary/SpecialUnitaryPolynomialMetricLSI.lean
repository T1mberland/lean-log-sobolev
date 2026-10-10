import LogSobolev.Unitary.SpecialUnitaryPolynomialLSI
import LogSobolev.Unitary.SpecialUnitarySlope
import LogSobolev.Geometry.CompactRegularity
import LogSobolev.Unitary.SpecialUnitaryPolynomialExtension

/-! # Polynomial SU logarithmic Sobolev inequality with the paper's local slope

The previously proved polynomial entropy bound is transferred to the actual
upper local metric slope for the unnormalized Hilbert–Schmidt metric. The measure
is normalized Haar on the actual finite-dimensional SU group. This theorem still
requires polynomial observables; it does not assert the full `MetricLSI` predicate.
-/

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius Manifold ContDiff ENNReal NNReal

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

/-- Integrated smooth carré-du-champ energy is bounded by the actual squared local slope energy. -/
theorem specialUnitary_integral_gamma_le_slopeEnergy
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f) :
    ENNReal.ofReal (∫ U, specialUnitaryGamma b f f U ∂specialUnitaryHaar n) ≤
      slopeEnergy (specialUnitaryHaar n) f := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (specialUnitary_integrable_of_continuous (specialUnitaryGamma_contMDiff b hf hf).continuous)
    (Filter.Eventually.of_forall (specialUnitaryGamma_nonneg b hf))]
  exact lintegral_mono (specialUnitaryGamma_le_localSlope_sq b hf)

/-- The paper's local-slope LSI, with constant `2/N`, for every real polynomial SU observable.
No sign, nonvanishing, supplied trajectory, curvature, or entropy inequality is assumed. -/
theorem specialUnitaryPolynomial_metric_entropy_sq_le
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n))) (d : ℕ)
    (hN : 0 < Fintype.card n)
    (f : specialUnitaryPolynomialSpace (n := n) d) :
    ENNReal.ofReal (entropy (specialUnitaryHaar n) (fun U => f.val U ^ 2)) ≤
      2 * ((2 / (Fintype.card n : ℝ≥0) : ℝ≥0) : ℝ≥0∞) *
        slopeEnergy (specialUnitaryHaar n) f.val := by
  have h := ENNReal.ofReal_le_ofReal (specialUnitaryPolynomial_entropy_sq_le b d hN f)
  rw [ENNReal.ofReal_mul (by positivity)] at h
  have hc : ENNReal.ofReal (4 / (Fintype.card n : ℝ)) =
      2 * ((2 / (Fintype.card n : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hN)]
    rw [ENNReal.coe_div (by exact_mod_cast (Nat.ne_of_gt hN) : (Fintype.card n : ℝ≥0) ≠ 0)]
    simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast, ENNReal.coe_ofNat, ENNReal.coe_natCast]
    rw [← mul_div_assoc]
    norm_num
  rw [hc] at h
  exact h.trans (mul_le_mul_right (specialUnitary_integral_gamma_le_slopeEnergy b f.val.contMDiff) _)

/-- Polynomial slope energy is finite; the metric bound is not using an infinite right-hand side. -/
theorem specialUnitaryPolynomial_slopeEnergy_ne_top (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) :
    slopeEnergy (specialUnitaryHaar n) f.val ≠ ⊤ := by
  rw [slopeEnergy_eq_ofReal_integral (specialUnitaryPolynomial_locallyLipschitz d f)]
  exact ENNReal.ofReal_ne_top

/-- Real-valued local-slope LSI for every polynomial observable, with all local
Lipschitz and integrability requirements supplied by the proved ambient extension. -/
theorem specialUnitaryPolynomial_entropy_sq_le_slope
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n))) (d : ℕ)
    (hN : 0 < Fintype.card n)
    (f : specialUnitaryPolynomialSpace (n := n) d) :
    entropy (specialUnitaryHaar n) (fun U => f.val U ^ 2) ≤
      (4 / (Fintype.card n : ℝ)) *
        (∫ U, (localSlope f.val U).toReal ^ 2 ∂specialUnitaryHaar n) := by
  have he := specialUnitary_integral_gamma_le_slopeEnergy b f.val.contMDiff
  rw [slopeEnergy_eq_ofReal_integral (specialUnitaryPolynomial_locallyLipschitz d f)] at he
  have hn : 0 ≤ ∫ U, (localSlope f.val U).toReal ^ 2 ∂specialUnitaryHaar n :=
    integral_nonneg (fun U => sq_nonneg _)
  exact (specialUnitaryPolynomial_entropy_sq_le b d hN f).trans
    (mul_le_mul_of_nonneg_left ((ENNReal.ofReal_le_ofReal_iff hn).mp he) (by positivity))

end LogSobolev
