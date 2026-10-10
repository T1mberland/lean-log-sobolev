/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
Adapted for Lean 4.28.0; transport API added in this project.
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Entropy and transport

The entropy convention is equation (6) of Meckes–Meckes, arXiv:1210.2681.
The definition and elementary API follow `LogSobolev.entropy` in
Lean-MoDS/StatsMLlib (`Probability/Entropy/Basic.lean`) and YuanheZ's
lean-stat-learning-theory (`SLT/GaussianLSI/Entropy.lean`). This small compatibility
port avoids importing their newer, incompatible Lean toolchains.

The Bochner integral is totalized: applications must establish integrability.
In particular, this definition alone makes no assertion about infinite entropy.
-/

open MeasureTheory

namespace LogSobolev

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- `Ent_μ(g) = ∫ g log g − (∫ g) log (∫ g)`, with `0 log 0 = 0`.
Intended for nonnegative integrable functions with integrable `g log g`. -/
noncomputable def entropy (μ : Measure X) (g : X → ℝ) : ℝ :=
  (∫ x, g x * Real.log (g x) ∂μ) -
    (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ)

@[simp] theorem entropy_const (μ : Measure X) [IsProbabilityMeasure μ] (c : ℝ) :
    entropy μ (fun _ => c) = 0 := by
  simp [entropy]

theorem entropy_congr {μ : Measure X} {f g : X → ℝ} (h : f =ᵐ[μ] g) :
    entropy μ f = entropy μ g := by
  unfold entropy
  rw [integral_congr_ae h]
  congr 1
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

/-- Jensen's inequality gives nonnegative entropy; integrability is explicit. -/
theorem entropy_nonneg {μ : Measure X} [IsProbabilityMeasure μ] {g : X → ℝ}
    (hg : 0 ≤ᵐ[μ] g) (hi : Integrable g μ)
    (hl : Integrable (fun x => g x * Real.log (g x)) μ) :
    0 ≤ entropy μ g := by
  exact sub_nonneg.mpr (Real.convexOn_mul_log.map_integral_le
    Real.continuous_mul_log.continuousOn isClosed_Ici hg hi hl)

/-- Entropy commutes with a measurable pushforward. This is independent of any LSI. -/
theorem entropy_map (μ : Measure X) {T : X → Y} (hT : Measurable T)
    {g : Y → ℝ} (hg : AEStronglyMeasurable g (Measure.map T μ)) :
    entropy (Measure.map T μ) g = entropy μ (g ∘ T) := by
  unfold entropy
  have hl : AEStronglyMeasurable (fun y => g y * Real.log (g y)) (Measure.map T μ) :=
    hg.mul (Real.measurable_log.comp_aemeasurable hg.aemeasurable).aestronglyMeasurable
  rw [integral_map hT.aemeasurable hl, integral_map hT.aemeasurable hg]
  rfl

end LogSobolev
