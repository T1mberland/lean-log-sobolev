import LogSobolev.Geometry.SlopeMeasurable
import LogSobolev.Measure.Entropy
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic.NormNum

/-! # Metric LSI and Lipschitz pushforward

The energy is the integral of the squared upper local metric slope, not a
chosen global Lipschitz constant. The extended-nonnegative formulation permits
infinite energy; finite-entropy test functions have explicit integrability
conditions. `MetricLSI.map` is a proved stability theorem, not an existence
claim for any particular source measure.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace LogSobolev

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

/-- Extended squared-slope energy. For locally Lipschitz functions the slope
is finite at every point and is Borel measurable. -/
noncomputable def slopeEnergy (μ : Measure X) (f : X → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, localSlope f x ^ 2 ∂μ

/-- Metric LSI in the convention `Ent(f²) ≤ 2C ∫ |∇f|²`.
Entropy integrability is explicit, while the energy may be infinite. -/
def MetricLSI (μ : Measure X) (C : ℝ≥0) : Prop :=
  ∀ f : X → ℝ, LocallyLipschitz f →
    Integrable (fun x => f x ^ 2) μ →
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ →
    ENNReal.ofReal (entropy μ (fun x => f x ^ 2)) ≤ 2 * (C : ℝ≥0∞) * slopeEnergy μ f

/-- Squared slope energy contracts under Lipschitz pullback, with factor `K²`. -/
theorem slopeEnergy_comp_le {μ : Measure X} {T : X → Y} {K : ℝ≥0}
    (hT : LipschitzWith K T) {f : Y → ℝ} (hf : Continuous f) :
    slopeEnergy μ (f ∘ T) ≤ (K : ℝ≥0∞) ^ 2 * slopeEnergy (Measure.map T μ) f := by
  calc
    _ ≤ ∫⁻ x, ((K : ℝ≥0∞) * localSlope f (T x)) ^ 2 ∂μ := by
      apply lintegral_mono
      intro x
      exact pow_le_pow_left' (localSlope_comp_le hT f x) 2
    _ = (K : ℝ≥0∞) ^ 2 * ∫⁻ x, localSlope f (T x) ^ 2 ∂μ := by
      simp_rw [mul_pow]
      exact lintegral_const_mul' _ _ (by simp)
    _ = _ := by
      rw [slopeEnergy, lintegral_map ((measurable_localSlope hf).pow_const 2)
        hT.continuous.measurable]

/-- Lipschitz pushforward multiplies the LSI constant by the square of the
Lipschitz constant. This applies to all locally Lipschitz finite-entropy tests. -/
theorem MetricLSI.map {μ : Measure X} {C K : ℝ≥0} (h : MetricLSI μ C)
    {T : X → Y} (hT : LipschitzWith K T) :
    MetricLSI (Measure.map T μ) (K ^ 2 * C) := by
  intro f hf hi hl
  have hs := h (f ∘ T) (hf.comp hT.locallyLipschitz)
    (hi.comp_measurable hT.continuous.measurable)
    (hl.comp_measurable hT.continuous.measurable)
  rw [entropy_map μ hT.continuous.measurable hi.aestronglyMeasurable]
  calc
    _ ≤ 2 * (C : ℝ≥0∞) * slopeEnergy μ (f ∘ T) := hs
    _ ≤ 2 * (C : ℝ≥0∞) * ((K : ℝ≥0∞) ^ 2 * slopeEnergy (Measure.map T μ) f) :=
      mul_le_mul_right (slopeEnergy_comp_le hT hf.continuous) _
    _ = _ := by simp only [ENNReal.coe_mul, ENNReal.coe_pow]; ring

/-- Isometric transport is the unit-Lipschitz case. -/
theorem MetricLSI.map_isometryEquiv {μ : Measure X} {C : ℝ≥0} (h : MetricLSI μ C)
    (e : X ≃ᵢ Y) : MetricLSI (Measure.map e μ) C := by
  simpa using h.map e.isometry.lipschitz

end LogSobolev
