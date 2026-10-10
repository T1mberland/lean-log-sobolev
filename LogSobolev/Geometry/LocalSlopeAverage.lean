module

public import LogSobolev.Geometry.LocalSlopeDerivative
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # Derivatives of averages controlled by local slopes

Reverse Fatou for bounded difference quotients allows nonsmooth functions
inside an average. Only the averaged function is assumed differentiable.
This supplies the analytic comparison needed for polynomial regularization.
-/

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace LogSobolev

/-- Difference quotients along a convergent sequence are bounded in limsup by
the paper's upper local slope. No differentiability is needed. -/
theorem limsup_ofReal_norm_slope_le {f : ℝ → ℝ} {x : ℝ} {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝 x)) :
    limsup (fun j => ENNReal.ofReal ‖slope f x (t j)‖) atTop ≤ localSlope f x := by
  have he (y : ℝ) : ‖slope f x y‖ = dist (f y) (f x) / dist y x := by
    simp only [slope, vsub_eq_sub, smul_eq_mul, norm_mul, norm_inv,
      dist_eq_norm, div_eq_mul_inv, mul_comm]
  simp_rw [he]
  exact limsup_le_limsup_of_le (u := fun y => ENNReal.ofReal (dist (f y) (f x) / dist y x)) ht

/-- The same sequential bound for squared difference quotients. -/
theorem limsup_ofReal_slope_sq_le {f : ℝ → ℝ} {x : ℝ} {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝 x)) :
    limsup (fun j => ENNReal.ofReal ((slope f x (t j)) ^ 2)) atTop ≤ localSlope f x ^ 2 := by
  have hpow : Monotone (fun z : ℝ≥0∞ => z ^ 2) := fun _ _ h => pow_le_pow_left' h 2
  have he (j : ℕ) : ENNReal.ofReal ((slope f x (t j)) ^ 2) =
      (ENNReal.ofReal ‖slope f x (t j)‖) ^ 2 := by
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [Real.norm_eq_abs, sq_abs]
  simp_rw [he]
  have hmap := hpow.map_limsup_of_continuousAt
    (F := atTop) (fun j => ENNReal.ofReal ‖slope f x (t j)‖)
    (ENNReal.continuous_pow 2).continuousAt
  simp only [Function.comp_def] at hmap
  rw [← hmap]
  exact pow_le_pow_left' (limsup_ofReal_norm_slope_le ht) 2

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- The squared derivative of an average is bounded by the averaged squared
local slopes. The summands may be nonsmooth; a uniform time-Lipschitz bound
provides the integrable domination for reverse Fatou. -/
theorem ofReal_deriv_integral_sq_le_lintegral_localSlope_sq
    {g : ℝ → X → ℝ} (hg : ∀ t, Continuous (g t)) {K : ℝ≥0}
    (hK : ∀ x, LipschitzWith K (fun t => g t x)) {a : ℝ}
    (ha : HasDerivAt (fun t => ∫ x, g t x ∂μ) a 0) :
    ENNReal.ofReal (a ^ 2) ≤ ∫⁻ x, localSlope (fun t => g t x) 0 ^ 2 ∂μ := by
  let t : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htn (j : ℕ) : t j ≠ 0 := by dsimp [t]; positivity
  have ht' : Tendsto t atTop (𝓝[≠] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨ht, Eventually.of_forall (fun j => htn j)⟩
  let r : ℕ → X → ℝ := fun j x => slope (fun t => g t x) 0 (t j)
  have hr (j : ℕ) : Continuous (r j) := by
    change Continuous (fun x => (t j - 0)⁻¹ * (g (t j) x - g 0 x))
    exact continuous_const.mul ((hg _).sub (hg _))
  have hi (j : ℕ) : Integrable (r j) μ :=
    (hr j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 (j : ℕ) : Integrable (fun x => r j x ^ 2) μ :=
    ((hr j).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm (j : ℕ) : (∫ x, r j x ∂μ) = slope (fun t => ∫ x, g t x ∂μ) 0 (t j) := by
    simp only [r, slope, vsub_eq_sub, smul_eq_mul]
    rw [integral_const_mul, integral_sub
      ((hg _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((hg _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  have hb (j : ℕ) (x : X) : ‖r j x‖ ≤ (K : ℝ) := by
    have hd := (hK x).dist_le_mul (t j) 0
    have he : ‖r j x‖ = dist (g (t j) x) (g 0 x) / dist (t j) 0 := by
      simp only [r, slope, vsub_eq_sub, smul_eq_mul, norm_mul, norm_inv,
        dist_eq_norm, div_eq_mul_inv, mul_comm]
    rw [he]
    exact (div_le_iff₀ (dist_pos.mpr (htn j))).mpr hd
  have hj (j : ℕ) : ENNReal.ofReal ((∫ x, r j x ∂μ) ^ 2) ≤
      ∫⁻ x, ENNReal.ofReal (r j x ^ 2) ∂μ := by
    have h := (Even.convexOn_pow (𝕜 := ℝ) (by decide : Even 2)).map_integral_le
      (continuous_id.pow 2).continuousOn isClosed_univ
      (Eventually.of_forall (fun _ => Set.mem_univ _)) (hi j) (hi2 j)
    have he := ofReal_integral_eq_lintegral_ofReal (hi2 j)
      (Eventually.of_forall fun x => sq_nonneg (r j x))
    rw [← he]
    exact ENNReal.ofReal_le_ofReal h
  have hl : Tendsto (fun j => ENNReal.ofReal ((∫ x, r j x ∂μ) ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (a ^ 2))) := by
    simp_rw [hm]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((ha.tendsto_slope.comp ht').pow 2)
  calc
    _ = limsup (fun j => ENNReal.ofReal ((∫ x, r j x ∂μ) ^ 2)) atTop := hl.limsup_eq.symm
    _ ≤ limsup (fun j => ∫⁻ x, ENNReal.ofReal (r j x ^ 2) ∂μ) atTop :=
      limsup_le_limsup (Eventually.of_forall hj)
    _ ≤ ∫⁻ x, limsup (fun j => ENNReal.ofReal (r j x ^ 2)) atTop ∂μ := by
      apply limsup_lintegral_le (fun _ => (K : ℝ≥0∞) ^ 2)
      · intro j
        exact ((hr j).pow 2).measurable.ennreal_ofReal
      · intro j
        exact Eventually.of_forall fun x => by
          have h := pow_le_pow_left₀ (norm_nonneg (r j x)) (hb j x) 2
          have he : r j x ^ 2 = ‖r j x‖ ^ 2 := by simp [Real.norm_eq_abs]
          change ENNReal.ofReal (r j x ^ 2) ≤ (K : ℝ≥0∞) ^ 2
          rw [he]
          calc
            _ ≤ ENNReal.ofReal ((K : ℝ) ^ 2) := ENNReal.ofReal_le_ofReal h
            _ = (K : ℝ≥0∞) ^ 2 := by
              rw [ENNReal.ofReal_pow (show 0 ≤ (K : ℝ) from K.2) 2, ENNReal.ofReal_coe_nnreal]
      · simp
    _ ≤ _ := lintegral_mono fun x => limsup_ofReal_slope_sq_le ht

end LogSobolev
