import LogSobolev.Geometry.LocalSlope
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-! # Measurability of the local metric slope

For continuous real-valued functions the slope is a countable infimum of lower
semicontinuous local oscillations. No separability assumption is needed.
-/

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace LogSobolev

variable {X : Type*} [MetricSpace X]

/-- Difference quotient truncated to an open ball, zero outside. -/
noncomputable def slopeProbe (f : X → ℝ) (r : ℝ) (y x : X) : ℝ≥0∞ :=
  if dist y x < r then ENNReal.ofReal (dist (f y) (f x) / dist y x) else 0

/-- Each truncated probe is lower semicontinuous in its base point.
The value zero at the diagonal and at the ball boundary is essential. -/
theorem lowerSemicontinuous_slopeProbe {f : X → ℝ} (hf : Continuous f) (r : ℝ) (y : X) :
    LowerSemicontinuous (slopeProbe f r y) := by
  intro x a ha
  by_cases hr : dist y x < r
  · by_cases hy : y = x
    · subst y
      simp [slopeProbe] at ha
    · have hq : ContinuousAt
          (fun z => ENNReal.ofReal (dist (f y) (f z) / dist y z)) x :=
        ENNReal.continuous_ofReal.continuousAt.comp
          ((continuous_const.dist hf).continuousAt.div
            (continuous_const.dist continuous_id).continuousAt (dist_ne_zero.mpr hy))
      have hlt : ∀ᶠ z in 𝓝 x,
          a < ENNReal.ofReal (dist (f y) (f z) / dist y z) :=
        hq (Ioi_mem_nhds (by simpa [slopeProbe, hr] using ha))
      have hb : ∀ᶠ z in 𝓝 x, dist y z < r :=
        (continuous_const.dist continuous_id).continuousAt (Iio_mem_nhds hr)
      filter_upwards [hlt, hb] with z hz hzr
      simpa [slopeProbe, hzr] using hz
  · simp [slopeProbe, hr] at ha

/-- Countable-radius formula for the local slope. The supremum is over all points. -/
theorem localSlope_eq_iInf_iSup_probe (f : X → ℝ) (x : X) :
    localSlope f x = ⨅ k : ℕ, ⨆ y : X, slopeProbe f (1 / ((k : ℝ) + 1)) y x := by
  rw [localSlope, Metric.nhds_basis_ball_inv_nat_succ.limsup_eq_iInf_iSup]
  simp only [iInf_true]
  congr 1
  funext k
  apply le_antisymm
  · refine iSup_le fun y => iSup_le fun hy => ?_
    exact le_iSup_of_le y (by simp only [slopeProbe, if_pos (Metric.mem_ball.mp hy)]; exact le_rfl)
  · refine iSup_le fun y => ?_
    by_cases hy : dist y x < 1 / ((k : ℝ) + 1)
    · simp only [slopeProbe, if_pos hy]
      exact le_iSup_of_le y (le_iSup_of_le hy le_rfl)
    · simp only [slopeProbe, if_neg hy]; exact bot_le

/-- A continuous real-valued function has Borel measurable local slope. -/
theorem measurable_localSlope [MeasurableSpace X] [OpensMeasurableSpace X]
    {f : X → ℝ} (hf : Continuous f) : Measurable (localSlope f) := by
  have he : localSlope f = fun x => ⨅ k : ℕ, ⨆ y : X,
      slopeProbe f (1 / ((k : ℝ) + 1)) y x := funext (localSlope_eq_iInf_iSup_probe f)
  rw [he]
  apply Measurable.iInf
  intro k
  exact (lowerSemicontinuous_iSup (fun y => lowerSemicontinuous_slopeProbe hf _ y)).measurable

end LogSobolev
