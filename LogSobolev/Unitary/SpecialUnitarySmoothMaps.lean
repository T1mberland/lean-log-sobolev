module

public import LogSobolev.Unitary.SpecialUnitaryManifold
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Smooth maps into and out of the actual SU group

The inclusion into Frobenius matrices is smooth. Conversely, an SU-valued map
whose ambient matrix map is smooth is smooth for the verified exponential
atlas. This criterion supports the proofs of smooth group operations.
-/

open Matrix Set Filter Topology
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

@[simp] theorem specialUnitary_extChartAt_apply (U V : Matrix.specialUnitaryGroup n ℂ) :
    extChartAt 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) U V =
      specialUnitaryLocalLog (U⁻¹ * V) := rfl

@[simp] theorem specialUnitary_extChartAt_symm_val (U : Matrix.specialUnitaryGroup n ℂ)
    (A : specialUnitaryLieAlgebra (n := n)) :
    ((extChartAt 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) U).symm A).val =
      U.val * NormedSpace.exp A.val := by
  change ((specialUnitaryChartAt U).symm A).val = _
  rw [specialUnitaryChartAt_symm_apply]
  change U.val * NormedSpace.exp ((1 : ℝ) • A.val) = _
  rw [one_smul]

/-- Inclusion of the original matrix SU group into its Frobenius ambient space is smooth. -/
theorem specialUnitary_val_contMDiff :
    ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ, Matrix n n ℂ) ∞
      (Subtype.val : Matrix.specialUnitaryGroup n ℂ → Matrix n n ℂ) := by
  intro U
  apply contMDiffAt_iff.mpr
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have hg (A : specialUnitaryLieAlgebra (n := n)) :
      ContDiffAt ℝ ∞ (fun X : specialUnitaryLieAlgebra (n := n) =>
        U.val * NormedSpace.exp X.val) A :=
    contDiffAt_const.mul ((NormedSpace.exp_analytic (𝕂 := ℝ) A.val).contDiffAt.comp A
      (specialUnitaryAlgebraInclusion (n := n)).contDiff.contDiffAt)
  have heq : (extChartAt 𝓘(ℝ, Matrix n n ℂ) U.val ∘ Subtype.val ∘
      (extChartAt 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) U).symm) =
      fun A : specialUnitaryLieAlgebra (n := n) => U.val * NormedSpace.exp A.val := by
    funext A
    simpa using specialUnitary_extChartAt_symm_val U A
  rw [heq]
  exact (hg _).contDiffWithinAt

/-- Projected local logarithm is smooth on its proved ambient target. -/
theorem specialUnitary_projected_log_contDiffAt (P B : Matrix n n ℂ)
    (hB : P * B ∈ specialUnitaryAmbientChart.target) :
    ContDiffAt ℝ ∞ (fun X : Matrix n n ℂ =>
      specialUnitaryAlgebraProjection (specialUnitaryAmbientChart.symm (P * X))) B := by
  have hm : ContDiffAt ℝ ∞ (fun X : Matrix n n ℂ => P * X) B :=
    contDiffAt_const.mul contDiffAt_id
  have hl := (specialUnitaryAmbientChart_spec.2.2.2.2 _ hB).contDiffAt.comp B hm
  exact specialUnitaryAlgebraProjection.contDiff.contDiffAt.comp B hl

section Maps

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

/-- Smoothness into SU follows from smoothness of the actual ambient matrix map. -/
theorem contMDiffAt_specialUnitary_of_val {f : M → Matrix.specialUnitaryGroup n ℂ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, Matrix n n ℂ) ∞ (fun y => (f y).val) x) :
    ContMDiffAt I 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) ∞ f x := by
  have hc : ContinuousAt f x := Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hf.continuousAt
  apply contMDiffAt_iff_target.mpr
  refine ⟨hc, ?_⟩
  have ht : ((f x)⁻¹).val * (f x).val ∈ specialUnitaryAmbientChart.target := by
    change ((f x)⁻¹ * f x).val ∈ specialUnitaryAmbientChart.target
    simpa only [inv_mul_cancel, Submonoid.coe_one] using (specialUnitaryAmbientChart_spec (n := n)).2.2.1
  have hF := (specialUnitary_projected_log_contDiffAt ((f x)⁻¹).val (f x).val ht).contMDiffAt.comp x hf
  apply hF.congr_of_eventuallyEq
  have hs := hc.preimage_mem_nhds ((specialUnitaryChartAt (f x)).open_source.mem_nhds
    (specialUnitary_mem_chart_source (f x)))
  filter_upwards [hs] with y hy
  simp only [Function.comp_apply, specialUnitary_extChartAt_apply]
  have h := specialUnitaryAlgebraProjection_val (specialUnitaryLocalLog ((f x)⁻¹ * f y))
  rw [specialUnitaryLocalLog_val ((f x)⁻¹ * f y) hy.2] at h
  exact h.symm

/-- The constructed atlas has exactly the expected ambient smooth-map criterion. -/
theorem contMDiffAt_specialUnitary_iff {f : M → Matrix.specialUnitaryGroup n ℂ} {x : M} :
    ContMDiffAt I 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) ∞ f x ↔
      ContMDiffAt I 𝓘(ℝ, Matrix n n ℂ) ∞ (fun y => (f y).val) x := by
  constructor
  · intro hf
    exact specialUnitary_val_contMDiff.contMDiffAt.comp x hf
  · exact contMDiffAt_specialUnitary_of_val

/-- Global version of the ambient smooth-map criterion. -/
theorem contMDiff_specialUnitary_iff {f : M → Matrix.specialUnitaryGroup n ℂ} :
    ContMDiff I 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) ∞ f ↔
      ContMDiff I 𝓘(ℝ, Matrix n n ℂ) ∞ (fun y => (f y).val) := by
  exact forall_congr' fun _ => contMDiffAt_specialUnitary_iff

end Maps

end LogSobolev
