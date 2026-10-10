import LogSobolev.Geometry.IntervalMetricLSI
import LogSobolev.Measure.IntervalAlmostEverywhere

/-! # Interval LSI in almost-everywhere derivative form

A globally Lipschitz real function may be differentiated only almost everywhere.
Any representative of that derivative with integrable square controls the
entropy under normalized interval measure. This form is useful for evaluations
of finite-dimensional Lipschitz curves.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace LogSobolev

/-- The normalized interval LSI with an almost-everywhere derivative representative. -/
theorem intervalUniform_entropy_sq_le_of_ae_hasDerivAt (L : ℝ) (hL : 0 < L)
    {f g : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (hg : Integrable (fun t : Icc (0 : ℝ) L => g t.val ^ 2) (intervalUniform L))
    (hd : ∀ᵐ t ∂volume, HasDerivAt f (g t) t) :
    entropy (intervalUniform L) (fun t => f t.val ^ 2) ≤
      (L ^ 2 / 4) * ∫ t, g t.val ^ 2 ∂intervalUniform L := by
  letI : Fact (0 < L) := ⟨hL⟩
  have hinc : LipschitzWith 1 (Subtype.val : Icc (0 : ℝ) L → ℝ) :=
    isometry_subtype_coe.lipschitz
  have hsub : LocallyLipschitz (fun t : Icc (0 : ℝ) L => f t.val) :=
    (hf.comp hinc).locallyLipschitz
  apply (intervalUniform_entropy_sq_le_of_locallyLipschitz L hL hsub).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono_ae (integrable_localSlope_sq hsub) hg
  filter_upwards [ae_intervalUniform_of_ae L hd] with t ht
  have hs := localSlope_comp_le hinc f t
  rw [localSlope_eq_of_hasDerivAt ht] at hs
  simp only [ENNReal.coe_one, one_mul] at hs
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
  rw [ENNReal.toReal_ofReal (norm_nonneg _)] at hr
  simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ ENNReal.toReal_nonneg hr 2

end LogSobolev
