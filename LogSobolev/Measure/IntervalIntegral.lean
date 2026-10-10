module

public import LogSobolev.Measure.Interval
public import LogSobolev.Measure.Entropy
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! # Integration and rescaling of normalized interval measure

The subtype uniform probability has the expected normalized Lebesgue integral.
Rescaling from the unit interval therefore transports entropy exactly.
-/

open MeasureTheory Set

namespace LogSobolev

/-- Integral formula for the actual normalized measure on the interval subtype. -/
theorem integral_intervalUniform (L : ℝ) (hL : 0 < L) (f : ℝ → ℝ) :
    (∫ t : Icc (0 : ℝ) L, f t ∂intervalUniform L) = L⁻¹ * ∫ x in (0 : ℝ)..L, f x := by
  rw [intervalUniform, integral_smul_measure,
    integral_subtype_comap measurableSet_Icc f, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hL.le]
  simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal hL.le]

/-- Rescaling the unit interval gives the normalized interval integral. -/
theorem integral_intervalUniform_eq_unit (L : ℝ) (hL : 0 < L) (f : ℝ → ℝ) :
    (∫ t : Icc (0 : ℝ) L, f t ∂intervalUniform L) =
      ∫ t in Icc (0 : ℝ) 1, f (L * t) := by
  rw [integral_intervalUniform L hL, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp [intervalIntegral.integral_comp_mul_left f hL.ne', smul_eq_mul]

/-- Entropy respects the exact rescaling to normalized interval probability. -/
theorem entropy_intervalUniform_eq_unit (L : ℝ) (hL : 0 < L) (f : ℝ → ℝ) :
    entropy (intervalUniform L) (fun t => f t) =
      entropy (volume.restrict (Icc (0 : ℝ) 1)) (fun t => f (L * t)) := by
  unfold entropy
  rw [integral_intervalUniform_eq_unit L hL (fun x => f x * Real.log (f x)),
    integral_intervalUniform_eq_unit L hL f]

end LogSobolev
