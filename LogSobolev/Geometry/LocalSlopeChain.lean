module

public import LogSobolev.Geometry.LocalSlopeDerivative

@[expose] public section

/-! # A scalar chain bound for Lipschitz observables

The derivative of the outer scalar function supplies its exact pointwise factor.
This is needed for exponential tests in the metric Herbst argument.
-/

open Filter
open scoped Topology ENNReal NNReal

namespace LogSobolev

/-- A differentiable scalar postcomposition of a globally Lipschitz observable
has local slope at most the derivative norm times the global Lipschitz constant. -/
theorem localSlope_comp_hasDerivAt_le {X : Type*} [MetricSpace X]
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {g : ℝ → ℝ} {a : ℝ} (x : X) (hg : HasDerivAt g a (f x)) :
    localSlope (g ∘ f) x ≤ ENNReal.ofReal (‖a‖ * K) := by
  classical
  let q : ℝ → ℝ := Function.update (fun z => (g z - g (f x)) / (z - f x)) (f x) a
  have hq : ContinuousAt q (f x) := hg.continuousAt_div
  have ht : Tendsto (fun y => ENNReal.ofReal (‖q (f y)‖ * K)) (𝓝 x)
      (𝓝 (ENNReal.ofReal (‖a‖ * K))) := by
    simpa [q, Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((hq.comp (hf.continuous.continuousAt)).norm).mul_const (K : ℝ)).tendsto
  have hdist (y : X) : dist (g (f y)) (g (f x)) = ‖q (f y)‖ * dist (f y) (f x) := by
    by_cases hy : f y = f x
    · simp [hy]
    · simp only [q, Function.update_of_ne hy, Real.dist_eq, norm_div, Real.norm_eq_abs]
      exact (div_mul_cancel₀ _ (abs_ne_zero.mpr (sub_ne_zero.mpr hy))).symm
  unfold localSlope
  apply le_trans (limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)) ht.limsup_eq.le
  apply Eventually.of_forall
  intro y
  apply ENNReal.ofReal_le_ofReal
  simp only [Function.comp_apply]
  rw [hdist]
  by_cases hy : y = x
  · simp only [hy, dist_self, mul_zero, zero_div]
    positivity
  · apply (div_le_iff₀ (dist_pos.mpr hy)).mpr
    calc
      ‖q (f y)‖ * dist (f y) (f x) ≤ ‖q (f y)‖ * ((K : ℝ) * dist y x) :=
        mul_le_mul_of_nonneg_left (hf.dist_le_mul y x) (norm_nonneg _)
      _ = _ := by ring

end LogSobolev
