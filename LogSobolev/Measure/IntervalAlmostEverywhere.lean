module

public import LogSobolev.Measure.Interval

@[expose] public section

/-! # Transferring almost-everywhere assertions to normalized intervals -/

open MeasureTheory

namespace LogSobolev

/-- Every Lebesgue-almost-everywhere assertion holds for the normalized interval measure. -/
theorem ae_intervalUniform_of_ae (L : ℝ) {P : ℝ → Prop} (hP : ∀ᵐ t ∂volume, P t) :
    ∀ᵐ t ∂intervalUniform L, P t.val := by
  apply ae_of_ae_map measurable_subtype_coe.aemeasurable
  rw [map_intervalUniform]
  exact Measure.ae_smul_measure (ae_restrict_of_ae hP) _

end LogSobolev
