module

public import LogSobolev.Measure.Entropy
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

/-! # Entropy and uniform limits

On a compact space with a finite measure, entropy is continuous in the uniform
norm on real continuous functions. No positive lower bound is required: the
continuous extension of `x * log x` handles zeros. In particular this applies
to squares of uniformly convergent observables of varying polynomial degree.
-/

open MeasureTheory Filter
open scoped Topology

namespace LogSobolev

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- Integration of continuous real functions is continuous for the uniform norm. -/
theorem continuous_integral_continuousMap_uniform :
    Continuous (fun f : C(X, ℝ) => ∫ x, f x ∂μ) := by
  let L : C(X, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c f => integral_smul c f }
  suffices h : ∀ f : C(X, ℝ), ‖L f‖ ≤ μ.real Set.univ * ‖f‖ from
    (L.mkContinuous (μ.real Set.univ) h).continuous
  intro f
  change ‖∫ x, f x ∂μ‖ ≤ μ.real Set.univ * ‖f‖
  calc
    _ ≤ ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _, ‖f‖ ∂μ := integral_mono
      (f.continuous.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (integrable_const _) (fun x => ContinuousMap.norm_coe_le_norm f x)
    _ = _ := by simp [integral_const, smul_eq_mul]

/-- Entropy is continuous under uniform convergence, including at functions with zeros. -/
theorem continuous_entropy_continuousMap :
    Continuous (fun f : C(X, ℝ) => entropy μ f) := by
  have h := (continuous_integral_continuousMap_uniform μ).comp
    (ContinuousMap.continuous_postcomp
      (⟨fun x : ℝ => x * Real.log x, Real.continuous_mul_log⟩ : C(ℝ, ℝ)))
  exact h.sub (Real.continuous_mul_log.comp (continuous_integral_continuousMap_uniform μ))

/-- The entropy of the square is continuous in the uniform norm. -/
theorem continuous_entropy_sq_continuousMap :
    Continuous (fun f : C(X, ℝ) => entropy μ (fun x => f x ^ 2)) := by
  convert (continuous_entropy_continuousMap μ).comp
    (ContinuousMap.continuous_postcomp
      (⟨fun x : ℝ => x ^ 2, continuous_id.pow 2⟩ : C(ℝ, ℝ))) using 1 <;> rfl

/-- Uniform limits preserve squared entropy; the index filter is arbitrary. -/
theorem tendsto_entropy_sq_of_tendsto_continuousMap {ι : Type*} {l : Filter ι}
    {f : ι → C(X, ℝ)} {g : C(X, ℝ)} (h : Tendsto f l (𝓝 g)) :
    Tendsto (fun i => entropy μ (fun x => f i x ^ 2)) l
      (𝓝 (entropy μ (fun x => g x ^ 2))) :=
  (continuous_entropy_sq_continuousMap μ).continuousAt.tendsto.comp h

end LogSobolev
