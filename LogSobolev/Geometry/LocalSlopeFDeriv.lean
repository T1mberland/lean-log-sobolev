import LogSobolev.Geometry.LocalSlopeDerivative
import LogSobolev.Geometry.MetricLSI
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Fréchet derivatives and local metric slope

A derivative in any real normed space is bounded by the upper local metric
slope. The proof restricts the function to affine lines of unit speed.
-/

open MeasureTheory
open scoped ENNReal

namespace LogSobolev

/-- A real Fréchet derivative is bounded by the upper local metric slope. -/
theorem ofReal_norm_fderiv_le_localSlope {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (x : E) :
    ENNReal.ofReal ‖fderiv ℝ f x‖ ≤ localSlope f x := by
  by_cases hf : DifferentiableAt ℝ f x
  swap
  · simp [fderiv_zero_of_not_differentiableAt hf]
  by_cases ht : localSlope f x = ⊤
  · simp [ht]
  apply (ENNReal.ofReal_le_iff_le_toReal ht).2
  apply ContinuousLinearMap.opNorm_le_of_unit_norm ENNReal.toReal_nonneg
  intro v hv
  let T : ℝ → E := fun t => x + t • v
  have hT : LipschitzWith 1 T := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp [T, dist_eq_norm, ← sub_smul, norm_smul, hv]
  have hdT : HasDerivAt T v 0 := by
    simpa [T] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hdf : HasDerivAt (f ∘ T) (fderiv ℝ f x v) 0 := by
    have hfT : HasFDerivAt f (fderiv ℝ f x) (T 0) := by
      simpa [T] using hf.hasFDerivAt
    exact hfT.comp_hasDerivAt 0 hdT
  have hs := localSlope_comp_le hT f 0
  rw [localSlope_eq_of_hasDerivAt hdf] at hs
  have hs' : ENNReal.ofReal ‖fderiv ℝ f x v‖ ≤ localSlope f x := by
    simpa [T] using hs
  exact (ENNReal.ofReal_le_iff_le_toReal ht).1 hs'

/-- The integrated derivative energy is bounded by the existing metric-slope
energy, with an explicit integrability hypothesis and no compactness assumption. -/
theorem ofReal_integral_norm_fderiv_sq_le_slopeEnergy {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (μ : MeasureTheory.Measure E) (f : E → ℝ)
    (hi : MeasureTheory.Integrable (fun x => ‖fderiv ℝ f x‖^2) μ) :
    ENNReal.ofReal (∫ x, ‖fderiv ℝ f x‖^2 ∂μ) ≤ slopeEnergy μ f := by
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  apply MeasureTheory.lintegral_mono
  intro x
  dsimp only
  rw [ENNReal.ofReal_pow (norm_nonneg _)]
  exact pow_le_pow_left' (ofReal_norm_fderiv_le_localSlope f x) 2

end LogSobolev
