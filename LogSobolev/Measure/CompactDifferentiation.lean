module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

/-! # Differentiation of integrals on compact spaces

Joint continuity of a time-dependent integrand and its derivative supplies
local domination on a compact time interval times the compact measure space.
No domination hypothesis is left for the caller to establish.
-/

open MeasureTheory Set Filter Topology

namespace LogSobolev

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- Differentiate a jointly continuous family with jointly continuous time derivative
under a finite measure on a compact space. -/
theorem hasDerivAt_integral_of_compact
    {F Q : ℝ → X → ℝ} {s : Set ℝ}
    (hF : Continuous (Function.uncurry F))
    (hQ : Continuous (Function.uncurry Q))
    (hd : ∀ t ∈ s, ∀ x, HasDerivAt (fun r => F r x) (Q t x) t)
    (t : ℝ) (hs : s ∈ 𝓝 t) :
    HasDerivAt (fun s => ∫ x, F s x ∂μ) (∫ x, Q t x ∂μ) t := by
  have hc : IsCompact (Icc (t - 1) (t + 1) ×ˢ (univ : Set X)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn hQ.continuousOn
  have hFt (s : ℝ) : Continuous (F s) := hF.comp (continuous_const.prodMk continuous_id)
  have hQt (s : ℝ) : Continuous (Q s) := hQ.comp (continuous_const.prodMk continuous_id)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := s ∩ Ioo (t - 1) (t + 1)) (F := F) (F' := Q) (bound := fun _ => M)
    (inter_mem hs (Ioo_mem_nhds (by linarith) (by linarith)))
    (Eventually.of_forall fun s => (hFt s).aestronglyMeasurable)
    ((hFt t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hQt t).aestronglyMeasurable
    (Eventually.of_forall fun x s hs => hM (s, x) ⟨⟨hs.2.1.le, hs.2.2.le⟩, mem_univ x⟩)
    (integrable_const M) (Eventually.of_forall fun x r hr => hd r hr.1 x)).2

end LogSobolev
