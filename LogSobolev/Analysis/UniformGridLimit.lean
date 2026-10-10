import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Uniform-grid averages on the unit interval

A direct modulus-of-continuity estimate proves convergence of dyadic sample
averages to the Lebesgue integral. This avoids assuming a quadrature convergence
result when passing discrete entropy bounds to a continuum inequality.
-/

open MeasureTheory Filter Finset
open scoped Topology

namespace LogSobolev

/-- Average of the left endpoints of the `m` equal subintervals of `[0,1]`. -/
noncomputable def uniformGridAverage (m : ℕ) (f : ℝ → ℝ) : ℝ :=
  (∑ i ∈ range m, f ((i : ℝ) / m)) / m

/-- Error bound for a uniform-grid average from a modulus of continuity. -/
theorem uniformGridAverage_error_le (m : ℕ) (hm : 0 < m) {f : ℝ → ℝ}
    (hf : Continuous f) {ε : ℝ}
    (hmod : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |x - y| ≤ 1 / m → |f x - f y| ≤ ε) :
    |uniformGridAverage m f - ∫ x in (0 : ℝ)..1, f x| ≤ ε := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let a : ℕ → ℝ := fun i => (i : ℝ) / m
  have hstep (i : ℕ) : a (i + 1) - a i = 1 / m := by dsimp [a]; push_cast; ring
  have hsum : (∑ i ∈ range m, ∫ x in a i..a (i + 1), f x) = ∫ x in (0 : ℝ)..1, f x := by
    simpa [a, hmR.ne'] using intervalIntegral.sum_integral_adjacent_intervals
      (a := a) (n := m) (fun i _ => hf.intervalIntegrable _ _ :
        ∀ i < m, IntervalIntegrable f volume (a i) (a (i + 1)))
  have heq : uniformGridAverage m f - ∫ x in (0 : ℝ)..1, f x =
      ∑ i ∈ range m, ∫ x in a i..a (i + 1), (f (a i) - f x) := by
    rw [uniformGridAverage, sum_div, ← hsum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) (hf.intervalIntegrable _ _),
      intervalIntegral.integral_const, hstep]
    simp only [smul_eq_mul]
    dsimp [a]
    ring
  have hb (i : ℕ) (hi : i ∈ range m) :
      ‖∫ x in a i..a (i + 1), (f (a i) - f x)‖ ≤ ε * (1 / m) := by
    have hmi : (i : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hi)
    have hai : 0 ≤ a i := by dsimp [a]; positivity
    have hbi : a (i + 1) ≤ 1 := by
      dsimp [a]
      rw [div_le_one hmR]
      exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hi)
    have hab : a i ≤ a (i + 1) := by linarith [hstep i, one_div_pos.mpr hmR]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a i) (b := a (i + 1)) (C := ε) (f := fun x => f (a i) - f x) (fun x hx => by
        rw [Set.uIoc_of_le hab] at hx
        rw [Real.norm_eq_abs]
        apply hmod (a i) ⟨hai, hab.trans hbi⟩ x ⟨hai.trans hx.1.le, hx.2.trans hbi⟩
        rw [abs_of_nonpos (sub_nonpos.mpr hx.1.le)]
        linarith [hstep i, hx.2])
    simpa [hstep, abs_of_pos (one_div_pos.mpr hmR)] using h
  rw [heq, ← Real.norm_eq_abs]
  calc
    _ ≤ ∑ i ∈ range m, ‖∫ x in a i..a (i + 1), (f (a i) - f x)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ range m, ε * (1 / m) := sum_le_sum hb
    _ = ε := by simp; field_simp

/-- Dyadic sample averages converge to the Lebesgue integral on `[0,1]`. -/
theorem tendsto_uniformGridAverage_pow_two {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto (fun n : ℕ => uniformGridAverage (2 ^ n) f) atTop
      (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hu : UniformContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / 2) (half_pos hε)
  have ht : Tendsto (fun n : ℕ => 1 / ((2 ^ n : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    simpa [div_pow] using h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  have he := uniformGridAverage_error_le (2 ^ n) (pow_pos (by decide) _) hf
    (ε := ε / 2) (fun x hx y hy hxy =>
      (hmod x hx y hy (by simpa [Real.dist_eq] using hxy.trans_lt (hN n hn))).le)
  rw [Real.dist_eq]
  exact he.trans_lt (half_lt_self hε)

end LogSobolev
