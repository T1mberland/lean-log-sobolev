module

public import LogSobolev.Unitary.SpecialUnitaryAnalyticNeighborhood
public import LogSobolev.Unitary.SpecialUnitaryInner
public import LogSobolev.Unitary.SpecialUnitaryCurves
public import LogSobolev.Unitary.SpecialUnitary
public import Mathlib.Geometry.Manifold.ChartedSpace

@[expose] public section

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

/-! # A chart at identity on the actual special unitary group

An ambient exponential chart with analytic inverse is restricted to su and SU.
The inverse is totalized outside its target only to satisfy the existing
`OpenPartialHomeomorph` interface. All inverse and regularity claims retain
explicit source/target membership.
-/

open Matrix Set
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Choose one of the already proved SU-compatible analytic ambient charts. -/
noncomputable def specialUnitaryAmbientChart :
    OpenPartialHomeomorph (Matrix n n ℂ) (Matrix n n ℂ) :=
  Classical.choose (exists_specialUnitary_analytic_exp (n := n))

theorem specialUnitaryAmbientChart_spec :
    (∀ A : Matrix n n ℂ, specialUnitaryAmbientChart A = NormedSpace.exp A) ∧
    (0 : Matrix n n ℂ) ∈ specialUnitaryAmbientChart.source ∧
    (1 : Matrix n n ℂ) ∈ specialUnitaryAmbientChart.target ∧
    (∀ A ∈ specialUnitaryAmbientChart.source,
      specialUnitaryAmbientChart A ∈ Matrix.specialUnitaryGroup n ℂ ↔
      A ∈ (specialUnitaryLieAlgebra : LieSubalgebra ℝ (Matrix n n ℂ))) ∧
    (∀ B ∈ specialUnitaryAmbientChart.target,
      AnalyticAt ℝ (specialUnitaryAmbientChart (n := n)).symm B) :=
  Classical.choose_spec (exists_specialUnitary_analytic_exp (n := n))

@[simp] theorem specialUnitaryAmbientChart_apply (A : Matrix n n ℂ) :
    specialUnitaryAmbientChart A = NormedSpace.exp A :=
  specialUnitaryAmbientChart_spec.1 A

/-- On the ambient target, the inverse sends actual SU elements into su. -/
theorem specialUnitaryAmbientChart_symm_mem (V : Matrix.specialUnitaryGroup n ℂ)
    (hV : V.val ∈ specialUnitaryAmbientChart.target) :
    (specialUnitaryAmbientChart (n := n)).symm V.val ∈
      (specialUnitaryLieAlgebra : LieSubalgebra ℝ (Matrix n n ℂ)) := by
  apply (specialUnitaryAmbientChart_spec.2.2.2.1 _
    (specialUnitaryAmbientChart.map_target hV)).1
  rw [specialUnitaryAmbientChart.right_inv hV]
  exact V.prop

/-- The SU local logarithm, with value zero outside its proved target. -/
noncomputable def specialUnitaryLocalLog (V : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryLieAlgebra (n := n) := by
  classical
  exact if hV : V.val ∈ specialUnitaryAmbientChart.target then
    ⟨specialUnitaryAmbientChart.symm V.val, specialUnitaryAmbientChart_symm_mem V hV⟩
  else 0

theorem specialUnitaryLocalLog_val (V : Matrix.specialUnitaryGroup n ℂ)
    (hV : V.val ∈ specialUnitaryAmbientChart.target) :
    (specialUnitaryLocalLog V).val = specialUnitaryAmbientChart.symm V.val := by
  simp [specialUnitaryLocalLog, hV]

/-- Exponential and local logarithm form an actual partial homeomorphism
between the real matrix algebra su and the original matrix group SU. -/
noncomputable def specialUnitaryExpChart :
    OpenPartialHomeomorph (specialUnitaryLieAlgebra (n := n))
      (Matrix.specialUnitaryGroup n ℂ) where
  toFun A := specialUnitaryExpCurve A 1
  invFun := specialUnitaryLocalLog
  source := Subtype.val ⁻¹' specialUnitaryAmbientChart.source
  target := Subtype.val ⁻¹' specialUnitaryAmbientChart.target
  map_source' A hA := by
    simpa [specialUnitaryExpCurve, unitaryExpCurve, Function.comp_def] using specialUnitaryAmbientChart.map_source hA
  map_target' V hV := by
    change (specialUnitaryLocalLog V).val ∈ specialUnitaryAmbientChart.source
    rw [specialUnitaryLocalLog_val V hV]
    exact specialUnitaryAmbientChart.map_target hV
  left_inv' A hA := by
    apply Subtype.ext
    have ht : (specialUnitaryExpCurve A 1).val ∈ specialUnitaryAmbientChart.target := by
      simpa [specialUnitaryExpCurve, unitaryExpCurve, Function.comp_def] using specialUnitaryAmbientChart.map_source hA
    rw [specialUnitaryLocalLog_val _ ht]
    simpa [specialUnitaryExpCurve, unitaryExpCurve, Function.comp_def] using specialUnitaryAmbientChart.left_inv hA
  right_inv' V hV := by
    apply Subtype.ext
    change (specialUnitaryExpCurve (specialUnitaryLocalLog V) 1).val = V.val
    simp only [specialUnitaryExpCurve, unitaryExpCurve, one_smul]
    rw [specialUnitaryLocalLog_val V hV, ← specialUnitaryAmbientChart_apply]
    exact specialUnitaryAmbientChart.right_inv hV
  open_source := specialUnitaryAmbientChart.open_source.preimage continuous_subtype_val
  open_target := specialUnitaryAmbientChart.open_target.preimage continuous_subtype_val
  continuousOn_toFun := by
    have h : Continuous (fun A : specialUnitaryLieAlgebra (n := n) =>
        specialUnitaryExpCurve A 1) := by
      apply Continuous.subtype_mk
      simpa [specialUnitaryExpCurve, unitaryExpCurve, Function.comp_def] using
        NormedSpace.exp_continuous.comp (continuous_subtype_val : Continuous
          (Subtype.val : specialUnitaryLieAlgebra (n := n) → Matrix n n ℂ))
    exact h.continuousOn
  continuousOn_invFun := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    exact (specialUnitaryAmbientChart.symm.continuousOn.comp
      continuous_subtype_val.continuousOn (fun V hV => hV)).congr
        (fun V hV => specialUnitaryLocalLog_val V hV)

theorem zero_mem_specialUnitaryExpChart_source :
    (0 : specialUnitaryLieAlgebra (n := n)) ∈ specialUnitaryExpChart.source :=
  specialUnitaryAmbientChart_spec.2.1

theorem one_mem_specialUnitaryExpChart_target :
    (1 : Matrix.specialUnitaryGroup n ℂ) ∈ specialUnitaryExpChart.target :=
  specialUnitaryAmbientChart_spec.2.2.1

/-- Translate the identity logarithm chart to an arbitrary actual SU element. -/
noncomputable def specialUnitaryChartAt (U : Matrix.specialUnitaryGroup n ℂ) :
    OpenPartialHomeomorph (Matrix.specialUnitaryGroup n ℂ)
      (specialUnitaryLieAlgebra (n := n)) :=
  (Homeomorph.mulLeft U⁻¹).toOpenPartialHomeomorph.trans specialUnitaryExpChart.symm

theorem specialUnitary_mem_chart_source (U : Matrix.specialUnitaryGroup n ℂ) :
    U ∈ (specialUnitaryChartAt U).source := by
  change U ∈ Set.univ ∩ (fun V => U⁻¹ * V) ⁻¹' specialUnitaryExpChart.target
  exact ⟨Set.mem_univ _, by simpa using one_mem_specialUnitaryExpChart_target (n := n)⟩

/-- A genuine topological atlas on the original SU group, using its original topology.
Smooth compatibility is a separate obligation. -/
noncomputable instance specialUnitaryChartedSpace :
    ChartedSpace (specialUnitaryLieAlgebra (n := n)) (Matrix.specialUnitaryGroup n ℂ) where
  atlas := Set.range specialUnitaryChartAt
  chartAt := specialUnitaryChartAt
  mem_chart_source := specialUnitary_mem_chart_source
  chart_mem_atlas U := ⟨U, rfl⟩

end LogSobolev
