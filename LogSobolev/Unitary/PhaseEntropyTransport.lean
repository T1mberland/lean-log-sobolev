import LogSobolev.Unitary.PhaseHaar
import LogSobolev.Measure.Entropy

/-! # Entropy transport through the actual Haar phase decomposition -/

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

/-- Continuous densities have identical entropy under Haar and the phase/SU product pullback. -/
theorem entropy_phase_decomposition (N : ℕ) (hN : 0 < N)
    {g : Matrix.unitaryGroup (Fin N) ℂ → ℝ} (hg : Continuous g) :
    entropy (unitaryHaar (Fin N)) g =
      entropy ((intervalUniform (phaseIntervalLength N)).prod (specialUnitaryHaar (Fin N)))
        (fun z => g (phaseMul (Real.sqrt (2 / (N : ℝ))) z.1.val (specialUnitaryInclusion z.2))) := by
  have hF := (intervalPhaseMap_lipschitz N hN).continuous
  rw [← map_intervalPhaseMap N hN, entropy_map _ hF.measurable hg.aestronglyMeasurable]
  unfold phaseDomainMeasure
  rw [entropy_map _ (WithLp.measurable_toLp 2 _)
    (hg.comp hF).aestronglyMeasurable]
  rfl

end LogSobolev
