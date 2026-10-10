import LogSobolev.Unitary.PhaseMap
import LogSobolev.Unitary.SpecialUnitary
import LogSobolev.Measure.Interval
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! # The exact interval × SU(N) domain

The probability measure and the Lipschitz map are constructed independently.
Its pushforward is identified with Haar in `LogSobolev.Unitary.PhaseHaar`.
-/

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

/-- The paper's domain with the L² product metric. -/
abbrev PhaseDomain (N : ℕ) := WithLp 2 (PhaseInterval N × Matrix.specialUnitaryGroup (Fin N) ℂ)

/-- Product of normalized interval measure and special unitary Haar probability,
transported through the measurable equivalence that installs the L² metric. -/
noncomputable def phaseDomainMeasure (N : ℕ) : Measure (PhaseDomain N) :=
  Measure.map (WithLp.toLp 2)
    ((intervalUniform (phaseIntervalLength N)).prod (specialUnitaryHaar (Fin N)))

theorem phaseDomainMeasure_probability (N : ℕ) (hN : 0 < N) :
    IsProbabilityMeasure (phaseDomainMeasure N) := by
  letI : Fact (0 < phaseIntervalLength N) := ⟨phaseIntervalLength_pos N hN⟩
  exact Measure.isProbabilityMeasure_map (WithLp.measurable_toLp 2 _).aemeasurable

/-- Isometric inclusion of the interval domain into the unrestricted domain. -/
def phaseDomainInclusion (N : ℕ) (p : PhaseDomain N) :
    WithLp 2 (ℝ × Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  WithLp.toLp 2 (p.fst.val, p.snd)

theorem phaseDomainInclusion_isometry (N : ℕ) : Isometry (phaseDomainInclusion N) := by
  apply Isometry.of_dist_eq
  intro p q
  simp only [WithLp.prod_dist_eq_add (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  rfl

/-- `F(t,V) = exp(i sqrt(2/N) t) V`, on the exact interval domain. -/
noncomputable def intervalPhaseMap (N : ℕ) : PhaseDomain N → Matrix.unitaryGroup (Fin N) ℂ :=
  phaseMap N ∘ phaseDomainInclusion N

/-- Restricting the phase map preserves its `sqrt(3)` Lipschitz constant. -/
theorem intervalPhaseMap_lipschitz (N : ℕ) (hN : 0 < N) :
    LipschitzWith ⟨Real.sqrt 3, Real.sqrt_nonneg 3⟩ (intervalPhaseMap N) := by
  simpa only [mul_one] using
    (phaseMap_lipschitz N hN).comp (phaseDomainInclusion_isometry N).lipschitz

end LogSobolev
