import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Normalized interval measure

This constructs the measure in the proposed proof, but does not assert the
one-dimensional logarithmic Sobolev inequality.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LogSobolev

/-- Uniform probability on `[0,L]` when `L > 0`, with its usual subtype metric. -/
noncomputable def intervalUniform (L : ℝ) : Measure (Icc (0 : ℝ) L) :=
  (ENNReal.ofReal L)⁻¹ • Measure.comap Subtype.val volume

theorem intervalUniform_univ (L : ℝ) (hL : 0 < L) :
    intervalUniform L univ = 1 := by
  rw [intervalUniform, Measure.smul_apply, comap_subtype_coe_apply measurableSet_Icc]
  simp only [image_univ, Subtype.range_coe_subtype, setOf_mem_eq, Real.volume_Icc,
    sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hL) ENNReal.ofReal_ne_top

instance (L : ℝ) [hL : Fact (0 < L)] : IsProbabilityMeasure (intervalUniform L) :=
  ⟨intervalUniform_univ L hL.out⟩

/-- Embedding the interval into the line gives normalized restricted Lebesgue measure. -/
theorem map_intervalUniform (L : ℝ) :
    Measure.map (Subtype.val : Icc (0 : ℝ) L → ℝ) (intervalUniform L) =
      (ENNReal.ofReal L)⁻¹ • volume.restrict (Icc (0 : ℝ) L) := by
  rw [intervalUniform, Measure.map_smul, map_comap_subtype_coe measurableSet_Icc]

/-- Length of the interval in Meckes–Meckes. -/
noncomputable def phaseIntervalLength (N : ℕ) : ℝ := Real.pi * Real.sqrt (2 / (N : ℝ))

theorem phaseIntervalLength_pos (N : ℕ) (hN : 0 < N) : 0 < phaseIntervalLength N := by
  unfold phaseIntervalLength
  positivity

/-- The closed interval with its ordinary Euclidean metric. -/
abbrev PhaseInterval (N : ℕ) := Icc (0 : ℝ) (phaseIntervalLength N)

end LogSobolev
