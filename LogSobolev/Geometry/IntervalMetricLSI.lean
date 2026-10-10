module

public import LogSobolev.Analysis.LipschitzUnitIntervalLSI
public import LogSobolev.Measure.IntervalIntegral
public import LogSobolev.Geometry.LocalSlopeDerivative
public import LogSobolev.Geometry.CompactRegularity

@[expose] public section

/-! # Metric logarithmic Sobolev inequality on an interval

For every `L > 0`, the actual normalized uniform measure on the Euclidean
subtype `[0,L]` satisfies LSI with constant `L²/8` for all locally Lipschitz
real observables. The coefficient in the real entropy inequality is `L²/4`.
The constant is not optimal. The proof uses absolute continuity, the proved
dyadic entropy bound, and the paper's local metric slope.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace LogSobolev

/-- Real interval LSI for every locally Lipschitz observable, with all moments finite. -/
theorem intervalUniform_entropy_sq_le_of_locallyLipschitz (L : ℝ) (hL : 0 < L)
    {f : Icc (0 : ℝ) L → ℝ} (hf : LocallyLipschitz f) :
    entropy (intervalUniform L) (fun t => f t ^ 2) ≤
      (L ^ 2 / 4) * ∫ t, (localSlope f t).toReal ^ 2 ∂intervalUniform L := by
  letI : Fact (0 < L) := ⟨hL⟩
  obtain ⟨K, hK⟩ := hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_univ
  have hK' : LipschitzWith K f := lipschitzOnWith_univ.mp hK
  let c : ℝ≥0 := ⟨L, hL.le⟩
  let T : ℝ → Icc (0 : ℝ) L := fun x => projIcc 0 L hL.le (L * x)
  let q : ℝ → ℝ := f ∘ T
  have hmul : LipschitzWith c (fun x : ℝ => L * x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |L * x - L * y| ≤ L * |x - y|
    rw [← mul_sub, abs_mul, abs_of_pos hL]
  have hT : LipschitzWith c T := by
    simpa only [one_mul, Function.comp_def, T] using (LipschitzWith.projIcc hL.le).comp hmul
  have hq : LipschitzWith (K * c) q := hK'.comp hT
  have hpoint (x : ℝ) : deriv q x ^ 2 ≤ L ^ 2 * (localSlope f (T x)).toReal ^ 2 := by
    have he := (ofReal_norm_deriv_le_localSlope q x).trans (localSlope_comp_le hT f x)
    have hfin : (c : ℝ≥0∞) * localSlope f (T x) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (localSlope_lt_top hf (T x)).ne
    have hr := ENNReal.toReal_mono hfin he
    simp only [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_mul,
      ENNReal.coe_toReal] at hr
    change ‖deriv q x‖ ≤ L * (localSlope f (T x)).toReal at hr
    simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using
      pow_le_pow_left₀ (norm_nonneg (deriv q x)) hr 2
  have hsm : Measurable (fun x => (localSlope f (T x)).toReal ^ 2) :=
    ((measurable_localSlope hf.continuous).comp hT.continuous.measurable).ennreal_toReal.pow_const 2
  have hj : IntervalIntegrable (fun x => L ^ 2 * (localSlope f (T x)).toReal ^ 2)
      volume 0 1 := by
    apply intervalIntegrable_iff.mpr
    apply (intervalIntegrable_const (c := L ^ 2 * (K : ℝ) ^ 2)
      (μ := volume) (a := 0) (b := 1)).def'.mono'
      (measurable_const.mul hsm).aestronglyMeasurable.restrict
    exact Eventually.of_forall fun x => by
      have hb : (localSlope f (T x)).toReal ≤ (K : ℝ) := by
        simpa using ENNReal.toReal_mono ENNReal.coe_ne_top (localSlope_le_of_lipschitz hK' (T x))
      rw [Pi.mul_apply, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg L) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ENNReal.toReal_nonneg hb 2) (sq_nonneg L)
  have henergy : (∫ x in (0 : ℝ)..1, (localSlope f (T x)).toReal ^ 2) =
      ∫ t, (localSlope f t).toReal ^ 2 ∂intervalUniform L := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc]
    simpa [T] using (integral_intervalUniform_eq_unit L hL
      (fun x => (localSlope f (projIcc 0 L hL.le x)).toReal ^ 2)).symm
  have hent : entropy (intervalUniform L) (fun t => f t ^ 2) =
      entropy (volume.restrict (Icc (0 : ℝ) 1)) (fun x => q x ^ 2) := by
    simpa [q, T, Function.comp_def] using entropy_intervalUniform_eq_unit L hL
      (fun x => f (projIcc 0 L hL.le x) ^ 2)
  rw [hent]
  calc
    _ ≤ (1 / 4 : ℝ) * ∫ x in (0 : ℝ)..1, deriv q x ^ 2 :=
      unitInterval_entropy_sq_le_of_lipschitzWith hq
    _ ≤ (1 / 4 : ℝ) * ∫ x in (0 : ℝ)..1, L ^ 2 * (localSlope f (T x)).toReal ^ 2 :=
      mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono (by norm_num)
        (lipschitz_intervalIntegrable_deriv_sq hq 0 1) hj hpoint) (by norm_num)
    _ = _ := by rw [intervalIntegral.integral_const_mul, henergy]; ring

/-- Normalized uniform measure on `[0,L]` satisfies metric LSI with constant `L²/8`.
This is the full locally Lipschitz statement, with the ordinary Euclidean metric. -/
theorem intervalUniform_metricLSI (L : ℝ) (hL : 0 < L) :
    MetricLSI (intervalUniform L) (Real.toNNReal (L ^ 2 / 8)) := by
  letI : Fact (0 < L) := ⟨hL⟩
  intro f hf _ _
  have h := ENNReal.ofReal_le_ofReal (intervalUniform_entropy_sq_le_of_locallyLipschitz L hL hf)
  rw [ENNReal.ofReal_mul (by positivity), ← slopeEnergy_eq_ofReal_integral hf] at h
  have hc : ENNReal.ofReal (L ^ 2 / 4) = 2 * (Real.toNNReal (L ^ 2 / 8) : ℝ≥0∞) := by
    change ENNReal.ofReal (L ^ 2 / 4) = 2 * ENNReal.ofReal (L ^ 2 / 8)
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rwa [hc] at h

end LogSobolev
