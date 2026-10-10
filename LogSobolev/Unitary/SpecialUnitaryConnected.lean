module

public import LogSobolev.Unitary.UnitaryConnected
public import LogSobolev.Unitary.SpecialUnitary

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Connectedness of the actual special unitary group

Multiply one row of a unitary matrix by the conjugate of its determinant. This
is a continuous retraction onto SU(N), proving connectedness from that of U(N).
No exponential surjectivity for traceless generators or connectedness axiom is
assumed. All topologies are the original finite matrix/subspace topologies.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A diagonal unitary correcting the determinant in one selected row. -/
noncomputable def unitaryDetCorrection (i : n) (U : Matrix.unitaryGroup n ℂ) :
    Matrix n n ℂ := Matrix.diagonal (fun j => if j = i then star U.val.det else 1)

theorem unitaryDetCorrection_mem (i : n) (U : Matrix.unitaryGroup n ℂ) :
    unitaryDetCorrection i U ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  simp only [unitaryDetCorrection, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext j
  by_cases h : j = i
  · simpa [h] using Unitary.mul_star_self_of_mem (Matrix.det_of_mem_unitary U.prop)
  · simp [h]

theorem det_unitaryDetCorrection (i : n) (U : Matrix.unitaryGroup n ℂ) :
    (unitaryDetCorrection i U).det = star U.val.det := by
  simp [unitaryDetCorrection, Matrix.det_diagonal]

/-- Continuous determinant correction, as a map from U(N) into actual SU(N). -/
noncomputable def unitaryToSpecialUnitary (i : n) (U : Matrix.unitaryGroup n ℂ) :
    Matrix.specialUnitaryGroup n ℂ :=
  ⟨unitaryDetCorrection i U * U.val,
    (Matrix.unitaryGroup n ℂ).mul_mem (unitaryDetCorrection_mem i U) U.prop, by
      change (unitaryDetCorrection i U * U.val).det = 1
      rw [Matrix.det_mul, det_unitaryDetCorrection]
      exact Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary U.prop)⟩

theorem unitaryToSpecialUnitary_continuous (i : n) :
    Continuous (unitaryToSpecialUnitary (n := n) i) := by
  apply Continuous.subtype_mk
  apply Continuous.mul _ continuous_subtype_val
  apply Continuous.matrix_diagonal
  apply continuous_pi
  intro j
  exact (continuous_subtype_val.matrix_det.star).if_const _ continuous_const

/-- Determinant correction fixes every SU matrix. -/
theorem unitaryToSpecialUnitary_inclusion (i : n) (U : Matrix.specialUnitaryGroup n ℂ) :
    unitaryToSpecialUnitary i (specialUnitaryInclusion U) = U := by
  apply Subtype.ext
  change Matrix.diagonal (fun j => if j = i then star U.val.det else 1) * U.val = U.val
  have hd : U.val.det = 1 := U.prop.2
  simp [hd]

/-- The determinant correction is surjective; its right inverse is the canonical inclusion. -/
theorem unitaryToSpecialUnitary_surjective (i : n) :
    Function.Surjective (unitaryToSpecialUnitary (n := n) i) := fun U =>
  ⟨specialUnitaryInclusion U, unitaryToSpecialUnitary_inclusion i U⟩

/-- Every actual SU(N) is connected, including the zero-dimensional singleton case. -/
instance specialUnitaryConnectedSpace : ConnectedSpace (Matrix.specialUnitaryGroup n ℂ) := by
  cases isEmpty_or_nonempty n with
  | inl h =>
      letI := h
      haveI : Subsingleton (Matrix.specialUnitaryGroup n ℂ) := inferInstance
      exact { isPreconnected_univ := Set.subsingleton_univ.isPreconnected, toNonempty := inferInstance }
  | inr h =>
      letI := h
      exact (unitaryToSpecialUnitary_surjective (Classical.arbitrary n)).connectedSpace
        (unitaryToSpecialUnitary_continuous _)

end LogSobolev
