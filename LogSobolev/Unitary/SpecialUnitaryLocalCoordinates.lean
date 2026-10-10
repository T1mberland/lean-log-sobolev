module

public import LogSobolev.Unitary.MatrixLocalExponential
public import LogSobolev.Unitary.SpecialUnitaryInner
public import LogSobolev.Unitary.SpecialUnitary

@[expose] public section

attribute [local instance 100] LieRing.ofAssociativeRing

/-! # Exponential local coordinates on the actual SU group

This constructs a homeomorphism between open neighborhoods of zero in the
verified real special unitary algebra and identity in the actual matrix SU
group. The forward map is matrix exponential. A smooth atlas, Riemannian
connection, curvature, and LSI are not asserted by this topological step.
-/

open Matrix Set
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Actual exponential local coordinates, with open domain and target and no
replacement of the matrix SU group by an abstract model. -/
theorem exists_specialUnitary_exp_homeomorph :
    ∃ s : Set (specialUnitaryLieAlgebra (n := n)),
    ∃ t : Set (Matrix.specialUnitaryGroup n ℂ),
      IsOpen s ∧ (0 : specialUnitaryLieAlgebra (n := n)) ∈ s ∧
      IsOpen t ∧ (1 : Matrix.specialUnitaryGroup n ℂ) ∈ t ∧
      ∃ e : s ≃ₜ t, ∀ A : s, (e A).val.val = NormedSpace.exp A.val.val := by
  obtain ⟨U, hU, hU0, hUs, _, hiff⟩ := exists_specialUnitary_exp_neighborhood (n := n)
  let e := (matrixExpLocalHomeomorph (n := n)).restrOpen U hU
  have he0 : (0 : Matrix n n ℂ) ∈ e.source := ⟨hUs hU0, hU0⟩
  have hexp (A : Matrix n n ℂ) : e A = NormedSpace.exp A := rfl
  have he1 : (1 : Matrix n n ℂ) ∈ e.target := by
    simpa only [hexp, NormedSpace.exp_zero] using e.map_source he0
  let s : Set (specialUnitaryLieAlgebra (n := n)) := Subtype.val ⁻¹' e.source
  let t : Set (Matrix.specialUnitaryGroup n ℂ) := Subtype.val ⁻¹' e.target
  have hforward (A : s) : e A.val.val ∈ Matrix.specialUnitaryGroup n ℂ := by
    rw [hexp]
    exact (hiff A.val.val A.prop.2).2 A.val.prop
  have hback (V : t) : e.symm V.val.val ∈
      (specialUnitaryLieAlgebra : LieSubalgebra ℝ (Matrix n n ℂ)) := by
    apply (hiff _ (e.map_target V.prop).2).1
    rw [← hexp, e.right_inv V.prop]
    exact V.val.prop
  refine ⟨s, t, e.open_source.preimage continuous_subtype_val, he0,
    e.open_target.preimage continuous_subtype_val, he1, ?_⟩
  let chart : s ≃ₜ t :=
    { toFun := fun A => ⟨⟨e A.val.val, hforward A⟩, e.map_source A.prop⟩
      invFun := fun V => ⟨⟨e.symm V.val.val, hback V⟩, e.map_target V.prop⟩
      left_inv := fun A => by
        apply Subtype.ext
        apply Subtype.ext
        exact e.left_inv A.prop
      right_inv := fun V => by
        apply Subtype.ext
        apply Subtype.ext
        exact e.right_inv V.prop
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact e.continuousOn.comp_continuous
          (continuous_subtype_val.comp continuous_subtype_val) (fun A => A.prop)
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact e.symm.continuousOn.comp_continuous
          (continuous_subtype_val.comp continuous_subtype_val) (fun V => V.prop) }
  exact ⟨chart, fun _ => rfl⟩

end LogSobolev
