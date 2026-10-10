module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! # Squared increments and one-dimensional energy

Cauchy–Schwarz on an interval is proved by integrating a nonnegative square.
The resulting estimate bounds sums of squared sample increments by the
ordinary integral of the squared derivative, with the exact mesh factor.
-/

open MeasureTheory Finset

namespace LogSobolev

/-- Scalar integral Cauchy–Schwarz with explicit first and second moment integrability. -/
theorem interval_integral_sq_le_of_integrable {g : ℝ → ℝ} {a b : ℝ}
    (hi : IntervalIntegrable g volume a b)
    (hsq : IntervalIntegrable (fun x => g x ^ 2) volume a b) (hab : a ≤ b) :
    (∫ x in a..b, g x) ^ 2 ≤ (b - a) * ∫ x in a..b, g x ^ 2 := by
  rcases hab.eq_or_lt with hab | hab
  · subst b
    simp
  let l := b - a
  let I := ∫ x in a..b, g x
  have hl : 0 < l := sub_pos.mpr hab
  have hnon := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab.le
    (fun x => sq_nonneg (l * g x - I))
  have he : (∫ x in a..b, (l * g x - I) ^ 2) =
      l ^ 2 * (∫ x in a..b, g x ^ 2) - l * I ^ 2 := by
    calc
      _ = ∫ x in a..b, (l ^ 2 * g x ^ 2 - (2 * l * I) * g x + I ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = _ := by
        have h1 : IntervalIntegrable (fun x => l ^ 2 * g x ^ 2) volume a b :=
          hsq.const_mul _
        have h2 : IntervalIntegrable (fun x => (2 * l * I) * g x) volume a b :=
          hi.const_mul _
        rw [intervalIntegral.integral_add (h1.sub h2) (continuous_const.intervalIntegrable _ _),
          intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        dsimp [l, I]
        ring
  rw [he] at hnon
  have hprod : 0 ≤ l * (l * (∫ x in a..b, g x ^ 2) - I ^ 2) := by nlinarith
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hprod hl)

/-- Scalar integral Cauchy–Schwarz on an interval for a continuous integrand. -/
theorem interval_integral_sq_le {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, g x) ^ 2 ≤ (b - a) * ∫ x in a..b, g x ^ 2 :=
  interval_integral_sq_le_of_integrable (hg.intervalIntegrable _ _)
    ((hg.pow 2).intervalIntegrable _ _) hab

/-- A continuously differentiable function's increment is bounded by derivative energy. -/
theorem sq_sub_le_interval_integral_deriv_sq {f g : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g) {a b : ℝ} (hab : a ≤ b) :
    (f b - f a) ^ 2 ≤ (b - a) * ∫ x in a..b, g x ^ 2 := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x) (hg.intervalIntegrable a b)
  rw [← he]
  exact interval_integral_sq_le hg hab

/-- The sum of squared increments on a uniform grid has the exact `1/m` energy bound. -/
theorem sum_sq_uniform_increments_le (m : ℕ) (hm : 0 < m) {f g : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g) :
    (∑ i ∈ range m, (f (((i + 1 : ℕ) : ℝ) / m) - f ((i : ℝ) / m)) ^ 2) ≤
      (1 / m) * ∫ x in (0 : ℝ)..1, g x ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let a : ℕ → ℝ := fun i => (i : ℝ) / m
  have hstep (i : ℕ) : a (i + 1) - a i = 1 / m := by dsimp [a]; push_cast; ring
  have hsum : (∑ i ∈ range m, ∫ x in a i..a (i + 1), g x ^ 2) =
      ∫ x in (0 : ℝ)..1, g x ^ 2 := by
    simpa [a, hmR.ne'] using intervalIntegral.sum_integral_adjacent_intervals
      (a := a) (n := m) (fun i _ => (hg.pow 2).intervalIntegrable _ _ :
        ∀ i < m, IntervalIntegrable (fun x => g x ^ 2) volume (a i) (a (i + 1)))
  calc
    _ ≤ ∑ i ∈ range m, (1 / m) * ∫ x in a i..a (i + 1), g x ^ 2 := by
      apply sum_le_sum
      intro i _
      have hab : a i ≤ a (i + 1) := by linarith [hstep i, one_div_pos.mpr hmR]
      simpa only [hstep] using sq_sub_le_interval_integral_deriv_sq hf hg hab
    _ = _ := by rw [← mul_sum, hsum]

end LogSobolev
