module

public import LogSobolev.Unitary.SpecialUnitaryChart
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

/-! # Smooth manifold structure on the actual matrix SU group

Transition maps of translated exponential charts are restrictions of
`A ↦ log(U⁻¹ V exp A)`. A continuous linear retraction to su supplies a smooth
ambient expression without assuming a differentiable subtype structure.
-/

open Matrix Set
open scoped Matrix.Norms.Frobenius ContDiff Manifold

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Inclusion of the real special unitary algebra in Frobenius matrices. -/
noncomputable def specialUnitaryAlgebraInclusion :
    specialUnitaryLieAlgebra (n := n) →L[ℝ] Matrix n n ℂ :=
  specialUnitaryLieAlgebra.toSubmodule.subtypeL

/-- A continuous linear retraction to su; only its left-inverse property is used. -/
noncomputable def specialUnitaryAlgebraProjection :
    Matrix n n ℂ →L[ℝ] specialUnitaryLieAlgebra (n := n) :=
  LinearMap.toContinuousLinearMap specialUnitaryLieAlgebra.toSubmodule.subtype.leftInverse

@[simp] theorem specialUnitaryAlgebraProjection_val
    (A : specialUnitaryLieAlgebra (n := n)) : specialUnitaryAlgebraProjection A.val = A :=
  LinearMap.leftInverse_apply_of_inj specialUnitaryLieAlgebra.toSubmodule.ker_subtype A

/-- A smooth ambient representative of a chart transition into su. -/
theorem specialUnitary_log_mul_exp_contDiffAt (P : Matrix n n ℂ)
    (A : specialUnitaryLieAlgebra (n := n))
    (hA : P * NormedSpace.exp A.val ∈ specialUnitaryAmbientChart.target) :
    ContDiffAt ℝ ∞ (fun X : specialUnitaryLieAlgebra (n := n) =>
      specialUnitaryAlgebraProjection
        (specialUnitaryAmbientChart.symm (P * NormedSpace.exp X.val))) A := by
  have hi : ContDiffAt ℝ ∞ (fun X : specialUnitaryLieAlgebra (n := n) => X.val) A :=
    (specialUnitaryAlgebraInclusion (n := n)).contDiff.contDiffAt
  have he : ContDiffAt ℝ ∞ (fun X : specialUnitaryLieAlgebra (n := n) =>
      NormedSpace.exp X.val) A :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) A.val).contDiffAt.comp A hi
  have hm : ContDiffAt ℝ ∞ (fun X : specialUnitaryLieAlgebra (n := n) =>
      P * NormedSpace.exp X.val) A := contDiffAt_const.mul he
  have hl := (specialUnitaryAmbientChart_spec.2.2.2.2 _ hA).contDiffAt.comp A hm
  exact specialUnitaryAlgebraProjection.contDiff.contDiffAt.comp A hl

@[simp] theorem specialUnitaryChartAt_apply (U V : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryChartAt U V = specialUnitaryLocalLog (U⁻¹ * V) := rfl

@[simp] theorem specialUnitaryChartAt_symm_apply (U : Matrix.specialUnitaryGroup n ℂ)
    (A : specialUnitaryLieAlgebra (n := n)) :
    (specialUnitaryChartAt U).symm A = U * specialUnitaryExpCurve A 1 := by
  change U⁻¹⁻¹ * specialUnitaryExpCurve A 1 = _
  rw [inv_inv]

/-- All translated exponential chart transitions are smooth on their actual domains. -/
theorem specialUnitary_chart_transition_contDiffOn (U V : Matrix.specialUnitaryGroup n ℂ) :
    ContDiffOn ℝ ∞ ((specialUnitaryChartAt U).symm.trans (specialUnitaryChartAt V))
      ((specialUnitaryChartAt U).symm.trans (specialUnitaryChartAt V)).source := by
  let P : Matrix n n ℂ := (V⁻¹).val * U.val
  let F : specialUnitaryLieAlgebra (n := n) → specialUnitaryLieAlgebra (n := n) :=
    fun A => specialUnitaryAlgebraProjection
      (specialUnitaryAmbientChart.symm (P * NormedSpace.exp A.val))
  have ht (A : specialUnitaryLieAlgebra (n := n))
      (hA : A ∈ ((specialUnitaryChartAt U).symm.trans (specialUnitaryChartAt V)).source) :
      P * NormedSpace.exp A.val ∈ specialUnitaryAmbientChart.target := by
    have h := hA.2.2
    change (V⁻¹ * ((specialUnitaryChartAt U).symm A)).val ∈ specialUnitaryAmbientChart.target at h
    simpa only [P, Submonoid.coe_mul, specialUnitaryChartAt_symm_apply, specialUnitaryExpCurve, unitaryExpCurve,
      one_smul, mul_assoc] using h
  have hF : ContDiffOn ℝ ∞ F
      ((specialUnitaryChartAt U).symm.trans (specialUnitaryChartAt V)).source :=
    fun A hA => (specialUnitary_log_mul_exp_contDiffAt P A (ht A hA)).contDiffWithinAt
  apply hF.congr
  intro A hA
  have hlog := specialUnitaryLocalLog_val
    (V⁻¹ * ((specialUnitaryChartAt U).symm A)) hA.2.2
  have hp := specialUnitaryAlgebraProjection_val
    (specialUnitaryLocalLog (V⁻¹ * ((specialUnitaryChartAt U).symm A)))
  rw [hlog] at hp
  simpa only [F, P, OpenPartialHomeomorph.trans_apply, specialUnitaryChartAt_apply,
    specialUnitaryChartAt_symm_apply, specialUnitaryExpCurve, unitaryExpCurve,
    one_smul, Submonoid.coe_mul, mul_assoc] using hp.symm

/-- The existing matrix SU group is a smooth real manifold modeled on its
verified traceless skew-Hermitian algebra, with its existing Frobenius topology. -/
instance specialUnitaryIsManifold :
    IsManifold 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) ∞ (Matrix.specialUnitaryGroup n ℂ) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨U, rfl⟩ := he
  obtain ⟨V, rfl⟩ := he'
  simpa using specialUnitary_chart_transition_contDiffOn U V

end LogSobolev
