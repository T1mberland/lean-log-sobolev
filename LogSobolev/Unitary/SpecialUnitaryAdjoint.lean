module

public import LogSobolev.Unitary.SpecialUnitaryInner
public import LogSobolev.Unitary.SpecialUnitaryCurves

@[expose] public section

attribute [local instance 100] LieRing.ofAssociativeRing

/-! # Unitary conjugation on the real special unitary algebra

Conjugation by an actual unitary matrix preserves the traceless skew-Hermitian
algebra and acts by a real linear isometry for its unnormalized Hilbert–Schmidt
inner product. These are group-level metric invariance results, not an assumed
Riemannian or LSI structure.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Unitary conjugation preserves the real special unitary algebra. -/
theorem unitary_conj_mem_specialUnitaryLieAlgebra (U : Matrix.unitaryGroup n ℂ)
    (A : specialUnitaryLieAlgebra (n := n)) :
    U.val * A.val * star U.val ∈
      (specialUnitaryLieAlgebra : LieSubalgebra ℝ (Matrix n n ℂ)) := by
  constructor
  · simp only [Matrix.star_mul, star_star, A.prop.1, mul_neg, neg_mul, mul_assoc]
  · rw [Matrix.trace_mul_comm, ← mul_assoc, U.prop.1, one_mul]
    exact A.prop.2

/-- The adjoint action as a real linear map, with no change of matrix norm. -/
noncomputable def specialUnitaryAdjoint (U : Matrix.unitaryGroup n ℂ) :
    specialUnitaryLieAlgebra (n := n) →ₗ[ℝ] specialUnitaryLieAlgebra (n := n) where
  toFun A := ⟨U.val * A.val * star U.val, unitary_conj_mem_specialUnitaryLieAlgebra U A⟩
  map_add' A B := by
    apply Subtype.ext
    change U.val * (A.val + B.val) * star U.val = _
    simp only [mul_add, add_mul]
    rfl
  map_smul' r A := by
    apply Subtype.ext
    change U.val * (r • A.val) * star U.val = r • (U.val * A.val * star U.val)
    simp

@[simp] theorem specialUnitaryAdjoint_apply_val (U : Matrix.unitaryGroup n ℂ)
    (A : specialUnitaryLieAlgebra (n := n)) :
    (specialUnitaryAdjoint U A).val = U.val * A.val * star U.val := rfl

/-- Conjugation is an isometry for the actual Frobenius norm. -/
theorem specialUnitaryAdjoint_norm (U : Matrix.unitaryGroup n ℂ)
    (A : specialUnitaryLieAlgebra (n := n)) :
    ‖specialUnitaryAdjoint U A‖ = ‖A‖ := by
  change ‖U.val * A.val * star U.val‖ = ‖A.val‖
  exact (norm_mul_unitary (U.val * A.val) U⁻¹).trans (norm_unitary_mul U A.val)

@[simp] theorem specialUnitaryAdjoint_one
    (A : specialUnitaryLieAlgebra (n := n)) : specialUnitaryAdjoint 1 A = A := by
  apply Subtype.ext
  simp

/-- The conjugation action respects group multiplication. -/
theorem specialUnitaryAdjoint_mul (U V : Matrix.unitaryGroup n ℂ)
    (A : specialUnitaryLieAlgebra (n := n)) :
    specialUnitaryAdjoint (U * V) A = specialUnitaryAdjoint U (specialUnitaryAdjoint V A) := by
  apply Subtype.ext
  change (U.val * V.val) * A.val * star (U.val * V.val) =
    U.val * (V.val * A.val * star V.val) * star U.val
  simp only [Matrix.star_mul, mul_assoc]

/-- The actual conjugation action as a linear isometric equivalence. -/
noncomputable def specialUnitaryAdjointIsometry (U : Matrix.unitaryGroup n ℂ) :
    specialUnitaryLieAlgebra (n := n) ≃ₗᵢ[ℝ] specialUnitaryLieAlgebra (n := n) where
  toLinearEquiv :=
    { specialUnitaryAdjoint U with
      invFun := specialUnitaryAdjoint U⁻¹
      left_inv := fun A => by
        change specialUnitaryAdjoint U⁻¹ (specialUnitaryAdjoint U A) = A
        rw [← specialUnitaryAdjoint_mul, inv_mul_cancel, specialUnitaryAdjoint_one]
      right_inv := fun A => by
        change specialUnitaryAdjoint U (specialUnitaryAdjoint U⁻¹ A) = A
        rw [← specialUnitaryAdjoint_mul, mul_inv_cancel, specialUnitaryAdjoint_one] }
  norm_map' := specialUnitaryAdjoint_norm U

/-- Invariance of the HS inner product under actual unitary conjugation. -/
theorem specialUnitaryAdjoint_inner (U : Matrix.unitaryGroup n ℂ)
    (A B : specialUnitaryLieAlgebra (n := n)) :
    inner ℝ (specialUnitaryAdjoint U A) (specialUnitaryAdjoint U B) = inner ℝ A B :=
  (specialUnitaryAdjointIsometry U).inner_map_map A B

/-- Conjugation also preserves the actual matrix Lie bracket. -/
theorem specialUnitaryAdjoint_lie (U : Matrix.unitaryGroup n ℂ)
    (A B : specialUnitaryLieAlgebra (n := n)) :
    specialUnitaryAdjoint U ⁅A, B⁆ = ⁅specialUnitaryAdjoint U A, specialUnitaryAdjoint U B⁆ := by
  apply Subtype.ext
  change U.val * (A.val * B.val - B.val * A.val) * star U.val =
    (U.val * A.val * star U.val) * (U.val * B.val * star U.val) -
      (U.val * B.val * star U.val) * (U.val * A.val * star U.val)
  have h (C D : Matrix n n ℂ) :
      (U.val * C * star U.val) * (U.val * D * star U.val) =
        U.val * (C * D) * star U.val := by
    simp only [mul_assoc]
    rw [← mul_assoc (star U.val) U.val, U.prop.1, one_mul]
  rw [h, h, mul_sub, sub_mul]

/-- Differentiating actual conjugation along an SU exponential curve gives
its matrix commutator. This links the algebraic adjoint action to group curves. -/
theorem specialUnitaryAdjoint_exp_derivative
    (A B : specialUnitaryLieAlgebra (n := n)) :
    HasDerivAt (fun t => (specialUnitaryAdjoint
      (specialUnitaryInclusion (specialUnitaryExpCurve A t)) B).val)
      ⁅A.val, B.val⁆ 0 := by
  have h := specialUnitaryExpCurve_hasDerivAt_zero A
  have hd := (h.mul_const B.val).mul h.star
  convert hd using 1 <;> try rfl
  simp only [specialUnitaryExpCurve_zero]
  symm
  change A.val * B.val * star (1 : Matrix n n ℂ) +
      (1 : Matrix n n ℂ) * B.val * star A.val = ⁅A.val, B.val⁆
  simp only [star_one, mul_one, one_mul, A.prop.1, mul_neg]
  rfl

end LogSobolev
