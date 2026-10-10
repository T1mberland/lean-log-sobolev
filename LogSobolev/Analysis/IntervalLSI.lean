import LogSobolev.Analysis.UnitIntervalLSI
import LogSobolev.Measure.IntervalIntegral

/-! # Scaled interval LSI for continuously differentiable observables

Normalized uniform measure on `[0,L]` has the proved bound
`Ent(f²) ≤ (L²/4) ∫ f'²` for restrictions of real C¹ functions.
This is constant `L²/8` in the `2C` convention. No locally Lipschitz extension
or sharp `L²/π²` bound is asserted in this module.
-/

open MeasureTheory Set

namespace LogSobolev

/-- C¹ logarithmic Sobolev inequality for actual normalized interval measure. -/
theorem intervalUniform_entropy_sq_le_of_hasDerivAt (L : ℝ) (hL : 0 < L)
    {f g : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g) :
    entropy (intervalUniform L) (fun t => f t ^ 2) ≤
      (L ^ 2 / 4) * ∫ t : Icc (0 : ℝ) L, g t ^ 2 ∂intervalUniform L := by
  have hd (x : ℝ) : HasDerivAt (fun t => f (L * t)) (L * g (L * x)) x := by
    simpa only [Function.comp_def, mul_one, mul_comm] using (hf (L * x)).comp x ((hasDerivAt_id x).const_mul L)
  have hc : Continuous (fun x => L * g (L * x)) :=
    continuous_const.mul (hg.comp (continuous_const.mul continuous_id))
  have h := unitInterval_entropy_sq_le_of_hasDerivAt hd hc
  rw [entropy_intervalUniform_eq_unit L hL (fun x => f x ^ 2)]
  calc
    _ ≤ (1 / 4 : ℝ) * ∫ x in (0 : ℝ)..1, (L * g (L * x)) ^ 2 := h
    _ = _ := by
      simp_rw [mul_pow]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_left (fun x => g x ^ 2) hL.ne',
        integral_intervalUniform L hL (fun x => g x ^ 2)]
      simp only [mul_zero, mul_one, smul_eq_mul]
      ring

end LogSobolev
