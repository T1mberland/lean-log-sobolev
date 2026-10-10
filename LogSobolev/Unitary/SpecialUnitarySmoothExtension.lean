import LogSobolev.Unitary.SpecialUnitaryLieGroup
import LogSobolev.Unitary.SpecialUnitaryTangent

/-! # Local ambient extensions of smooth SU functions

A logarithm chart and the proved linear retraction onto su give a locally smooth
retraction from ambient matrices to SU near each point. Consequently every
smooth SU function has a smooth ambient extension locally. No global extension
or globally defined smooth matrix logarithm is asserted.
-/

open Matrix Filter Topology
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Totalized retraction; it is a smooth retraction only near its center `U`. -/
noncomputable def specialUnitaryLocalRetraction (U : Matrix.specialUnitaryGroup n ℂ)
    (X : Matrix n n ℂ) : Matrix.specialUnitaryGroup n ℂ :=
  U * specialUnitaryExpCurve
    (specialUnitaryAlgebraProjection (specialUnitaryAmbientChart.symm ((U⁻¹).val * X))) 1

/-- On the translated chart's source, the ambient retraction fixes SU points. -/
theorem specialUnitaryLocalRetraction_val (U V : Matrix.specialUnitaryGroup n ℂ)
    (hV : V ∈ (specialUnitaryChartAt U).source) :
    specialUnitaryLocalRetraction U V.val = V := by
  have h := specialUnitaryAlgebraProjection_val (specialUnitaryLocalLog (U⁻¹ * V))
  rw [specialUnitaryLocalLog_val (U⁻¹ * V) hV.2] at h
  change U * specialUnitaryExpCurve
    (specialUnitaryAlgebraProjection (specialUnitaryAmbientChart.symm (U⁻¹ * V).val)) 1 = V
  rw [h]
  rw [← specialUnitaryChartAt_symm_apply]
  exact (specialUnitaryChartAt U).left_inv hV

@[simp] theorem specialUnitaryLocalRetraction_self (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryLocalRetraction U U.val = U :=
  specialUnitaryLocalRetraction_val U U (specialUnitary_mem_chart_source U)

/-- Smoothness is proved near the center, using the analytic logarithm neighborhood. -/
theorem specialUnitaryLocalRetraction_contMDiffAt (U : Matrix.specialUnitaryGroup n ℂ) :
    ContMDiffAt 𝓘(ℝ, Matrix n n ℂ) 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) ∞
      (specialUnitaryLocalRetraction U) U.val := by
  have ht : (U⁻¹).val * U.val ∈ specialUnitaryAmbientChart.target := by
    change (U⁻¹ * U).val ∈ specialUnitaryAmbientChart.target
    simpa only [inv_mul_cancel] using (specialUnitaryAmbientChart_spec (n := n)).2.2.1
  have hl := (specialUnitary_projected_log_contDiffAt (U⁻¹).val U.val ht).contMDiffAt
  exact contMDiffAt_const.mul (specialUnitary_exp_contMDiff.contMDiffAt.comp U.val hl)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every smooth SU function admits a smooth ambient extension in a neighborhood of each point. -/
theorem specialUnitary_exists_local_smooth_extension
    {f : Matrix.specialUnitaryGroup n ℂ → F} {U : Matrix.specialUnitaryGroup n ℂ}
    (hf : ContMDiffAt 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ, F) ∞ f U) :
    ∃ g : Matrix n n ℂ → F, ContDiffAt ℝ ∞ g U.val ∧
      f =ᶠ[𝓝 U] (fun V => g V.val) := by
  refine ⟨f ∘ specialUnitaryLocalRetraction U, ?_, ?_⟩
  · have hf' : ContMDiffAt 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ, F) ∞ f
        (specialUnitaryLocalRetraction U U.val) := by simpa using hf
    exact (hf'.comp U.val (specialUnitaryLocalRetraction_contMDiffAt U)).contDiffAt
  · filter_upwards [(specialUnitaryChartAt U).open_source.mem_nhds
      (specialUnitary_mem_chart_source U)] with V hV
    simp only [Function.comp_apply, specialUnitaryLocalRetraction_val U V hV]

end LogSobolev
