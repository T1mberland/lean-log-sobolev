import LogSobolev.Geometry.LocalSlope
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.LiminfLimsup

/-! # Local metric slope and ordinary derivatives

For a differentiable real function, the paper's upper local metric slope is
the absolute derivative. The punctured-neighborhood characterization handles
the zero difference quotient at the base point correctly.
-/

open Filter
open scoped Topology ENNReal

namespace LogSobolev

/-- The upper local metric slope on the real line equals the absolute derivative. -/
theorem localSlope_eq_of_hasDerivAt {f : ℝ → ℝ} {a x : ℝ} (hf : HasDerivAt f a x) :
    localSlope f x = ENNReal.ofReal ‖a‖ := by
  rw [localSlope_eq_limsup_nhdsNE]
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hf.tendsto_slope.norm
  have he : (fun y => ENNReal.ofReal (dist (f y) (f x) / dist y x)) =
      (fun y => ENNReal.ofReal ‖slope f x y‖) := by
    funext y
    simp only [slope, vsub_eq_sub, smul_eq_mul, norm_mul, norm_inv, dist_eq_norm, div_eq_mul_inv, mul_comm]
  rw [he]
  exact h.limsup_eq

/-- The totalized ordinary derivative is bounded by the local slope everywhere.
At nondifferentiability points the derivative is zero; no regularity is assumed. -/
theorem ofReal_norm_deriv_le_localSlope (f : ℝ → ℝ) (x : ℝ) :
    ENNReal.ofReal ‖deriv f x‖ ≤ localSlope f x := by
  by_cases hd : DifferentiableAt ℝ f x
  · rw [localSlope_eq_of_hasDerivAt hd.hasDerivAt]
  · simp [deriv_zero_of_not_differentiableAt hd]

end LogSobolev
