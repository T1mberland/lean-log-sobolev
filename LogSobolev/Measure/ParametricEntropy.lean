import LogSobolev.Measure.Entropy
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Continuous dependence of entropy on parameters

Continuous families on a compact integration space have continuously varying
entropy. Zeros and sign changes cause no difficulty because `x * log x` is
continuous with the real logarithm convention at zero.
-/

open MeasureTheory

namespace LogSobolev

variable {T X : Type*} [TopologicalSpace T] [FirstCountableTopology T]
  [LocallyCompactSpace T] [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasure μ]

/-- Entropy varies continuously in any jointly continuous compact-space family. -/
theorem continuous_parametric_entropy {g : T → X → ℝ}
    (hg : Continuous (Function.uncurry g)) :
    Continuous (fun t => entropy μ (g t)) := by
  have hm : Continuous (fun t => ∫ x, g t x ∂μ) := by
    simpa using continuous_parametric_integral_of_continuous (μ := μ) hg isCompact_univ
  have hl : Continuous (fun t => ∫ x, g t x * Real.log (g t x) ∂μ) := by
    simpa using continuous_parametric_integral_of_continuous (μ := μ)
      (f := fun t x => g t x * Real.log (g t x)) (Real.continuous_mul_log.comp hg) isCompact_univ
  exact hl.sub (Real.continuous_mul_log.comp hm)

end LogSobolev
