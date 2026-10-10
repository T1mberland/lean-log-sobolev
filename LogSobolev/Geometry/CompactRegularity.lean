module

public import LogSobolev.Geometry.MetricLSI
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

/-! # Integrability on compact metric probability spaces

All square, log-moment and squared-slope integrability requirements are proved
for locally Lipschitz functions, including nonsmooth ones.
-/

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace LogSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- Squared locally Lipschitz observables are integrable on a compact space. -/
theorem integrable_sq_of_locallyLipschitz {f : X → ℝ} (hf : LocallyLipschitz f) :
    Integrable (fun x => f x ^ 2) μ :=
  (hf.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The log moment is integrable even where the function vanishes. -/
theorem integrable_sq_log_of_locallyLipschitz {f : X → ℝ} (hf : LocallyLipschitz f) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ :=
  (Real.continuous_mul_log.comp (hf.continuous.pow 2)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Local slope squared is integrable. Local Lipschitz bounds suffice; a
global Lipschitz constant is not assumed. -/
theorem integrable_localSlope_sq {f : X → ℝ} (hf : LocallyLipschitz f) :
    Integrable (fun x => (localSlope f x).toReal ^ 2) μ := by
  have hm : Measurable (fun x => (localSlope f x).toReal ^ 2) :=
    (measurable_localSlope hf.continuous).ennreal_toReal.pow_const 2
  have hloc : LocallyIntegrable (fun x => (localSlope f x).toReal ^ 2) μ := by
    intro x
    obtain ⟨K, s, hs, hK⟩ := hf x
    obtain ⟨t, hts, hto, hxt⟩ := mem_nhds_iff.mp hs
    refine ⟨t, hto.mem_nhds hxt, ?_⟩
    apply (integrable_const ((K : ℝ) ^ 2)).mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem hto.measurableSet] with y hy
    have hb := localSlope_le_of_lipschitzOn hK (mem_of_superset (hto.mem_nhds hy) hts)
    have hr : (localSlope f y).toReal ≤ (K : ℝ) := by
      simpa using ENNReal.toReal_mono ENNReal.coe_ne_top hb
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg hr 2
  simpa only [IntegrableOn, Measure.restrict_univ] using hloc.integrableOn_isCompact isCompact_univ

/-- The extended energy equals the finite real integral on compact spaces. -/
theorem slopeEnergy_eq_ofReal_integral {f : X → ℝ} (hf : LocallyLipschitz f) :
    slopeEnergy μ f = ENNReal.ofReal (∫ x, (localSlope f x).toReal ^ 2 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_localSlope_sq hf)
    (Eventually.of_forall (fun x => sq_nonneg _))]
  apply lintegral_congr
  intro x
  rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (localSlope_lt_top hf x).ne]

/-- Real-valued form of metric LSI for every locally Lipschitz observable on a
compact space. All its integrability side conditions have been discharged. -/
theorem MetricLSI.real_form {C : ℝ≥0} (h : MetricLSI μ C) {f : X → ℝ}
    (hf : LocallyLipschitz f) :
    entropy μ (fun x => f x ^ 2) ≤
      2 * (C : ℝ) * ∫ x, (localSlope f x).toReal ^ 2 ∂μ := by
  have he := h f hf (integrable_sq_of_locallyLipschitz hf)
    (integrable_sq_log_of_locallyLipschitz hf)
  rw [slopeEnergy_eq_ofReal_integral hf] at he
  have hn : 0 ≤ 2 * (C : ℝ) * ∫ x, (localSlope f x).toReal ^ 2 ∂μ := by
    positivity
  apply (ENNReal.ofReal_le_ofReal_iff hn).mp
  simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (C : ℝ)),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_coe_nnreal] using he

end LogSobolev
