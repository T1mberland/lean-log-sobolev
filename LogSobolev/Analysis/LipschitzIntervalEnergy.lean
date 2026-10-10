module

public import LogSobolev.Analysis.IntervalSquareIncrement
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

/-! # Derivative energy for Lipschitz real functions

Absolute continuity supplies the fundamental theorem of calculus without a
C¹ assumption. The derivative is bounded by the Lipschitz constant even at
points where Lean's totalized derivative is zero. Its squared integral bounds
all uniform-grid squared increments.
-/

open MeasureTheory Finset
open scoped NNReal

namespace LogSobolev

/-- The squared derivative of a Lipschitz function is interval integrable. -/
theorem lipschitz_intervalIntegrable_deriv_sq {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (a b : ℝ) :
    IntervalIntegrable (fun x => deriv f x ^ 2) volume a b := by
  have hi := hf.lipschitzOnWith.absolutelyContinuousOnInterval.intervalIntegrable_deriv
    (a := a) (b := b)
  apply intervalIntegrable_iff.mpr
  apply (intervalIntegrable_const (c := (K : ℝ) ^ 2) (a := a) (b := b) (μ := volume)).def'.mono'
    (hi.def'.aestronglyMeasurable.pow 2)
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := norm_deriv_le_of_lipschitz (x₀ := x) hf
    have hs := pow_le_pow_left₀ (norm_nonneg (deriv f x)) h 2
    simpa only [Real.norm_eq_abs, sq_abs, Pi.pow_apply] using hs

/-- Lipschitz increments satisfy the same integral energy estimate as C¹ increments. -/
theorem sq_sub_le_interval_integral_deriv_sq_of_lipschitz {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {a b : ℝ} (hab : a ≤ b) :
    (f b - f a) ^ 2 ≤ (b - a) * ∫ x in a..b, deriv f x ^ 2 := by
  have hac : AbsolutelyContinuousOnInterval f a b :=
    hf.lipschitzOnWith.absolutelyContinuousOnInterval
  rw [← hac.integral_deriv_eq_sub]
  exact interval_integral_sq_le_of_integrable hac.intervalIntegrable_deriv
    (lipschitz_intervalIntegrable_deriv_sq hf a b) hab

/-- Uniform-grid squared increments of a Lipschitz function are bounded by derivative energy. -/
theorem sum_sq_uniform_increments_le_of_lipschitz (m : ℕ) (hm : 0 < m)
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    (∑ i ∈ range m, (f (((i + 1 : ℕ) : ℝ) / m) - f ((i : ℝ) / m)) ^ 2) ≤
      (1 / m) * ∫ x in (0 : ℝ)..1, deriv f x ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let a : ℕ → ℝ := fun i => (i : ℝ) / m
  have hstep (i : ℕ) : a (i + 1) - a i = 1 / m := by dsimp [a]; push_cast; ring
  have hsum : (∑ i ∈ range m, ∫ x in a i..a (i + 1), deriv f x ^ 2) =
      ∫ x in (0 : ℝ)..1, deriv f x ^ 2 := by
    simpa [a, hmR.ne'] using intervalIntegral.sum_integral_adjacent_intervals
      (a := a) (n := m) (fun i _ => lipschitz_intervalIntegrable_deriv_sq hf _ _ :
        ∀ i < m, IntervalIntegrable (fun x => deriv f x ^ 2) volume (a i) (a (i + 1)))
  calc
    _ ≤ ∑ i ∈ range m, (1 / m) * ∫ x in a i..a (i + 1), deriv f x ^ 2 := by
      apply sum_le_sum
      intro i _
      have hab : a i ≤ a (i + 1) := by linarith [hstep i, one_div_pos.mpr hmR]
      simpa only [hstep] using sq_sub_le_interval_integral_deriv_sq_of_lipschitz hf hab
    _ = _ := by rw [← mul_sum, hsum]

end LogSobolev
