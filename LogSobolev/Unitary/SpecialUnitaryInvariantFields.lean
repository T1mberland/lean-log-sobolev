module

public import LogSobolev.Unitary.SpecialUnitaryLieGroup
public import LogSobolev.Unitary.SpecialUnitaryTangent
public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Left-invariant tangent fields on SU

We connect Mathlib's geometric left-invariant vector fields with their actual
matrix velocities. This is a prerequisite for identifying the geometric bracket
with the matrix commutator in the Ricci step of Meckes–Meckes, Theorem 15.
-/

open Matrix
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual inclusion derivative is injective, at every SU matrix. -/
theorem specialUnitaryTangentInclusion_injective (U : Matrix.specialUnitaryGroup n ℂ) :
    Function.Injective (specialUnitaryTangentInclusion U) := by
  intro A B h
  apply Subtype.ext
  have h' := congrArg (fun X : Matrix n n ℂ => (U⁻¹).val * X) h
  change (U⁻¹).val * (U.val * A.val) = (U⁻¹).val * (U.val * B.val) at h'
  have hU : (U⁻¹).val * U.val = 1 := congrArg Subtype.val (inv_mul_cancel U)
  simpa only [← mul_assoc, hU, one_mul] using h'

/-- In the translated exponential coordinates, left multiplication preserves tangent coordinates. -/
theorem specialUnitary_mfderiv_mul_left_apply (U V : Matrix.specialUnitaryGroup n ℂ)
    (A : specialUnitaryLieAlgebra (n := n)) :
    mfderiv 𝓘(ℝ, specialUnitaryLieAlgebra (n := n))
      𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) (fun W => U * W) V A = A := by
  have hL : MDifferentiableAt 𝓘(ℝ, specialUnitaryLieAlgebra (n := n))
      𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) (fun W => U * W) V :=
    (contMDiff_mul_left (n := ∞)).mdifferentiableAt (by simp)
  have h₁ := (specialUnitary_val_hasMFDerivAt (U * V)).comp V hL.hasMFDerivAt
  have h₂ := ((ContinuousLinearMap.mul ℝ (Matrix n n ℂ)) U.val).hasFDerivAt.hasMFDerivAt.comp V
    (specialUnitary_val_hasMFDerivAt V)
  have he := hasMFDerivAt_unique h₁ h₂
  have heA := DFunLike.congr_fun he A
  apply specialUnitaryTangentInclusion_injective (U * V)
  change (U * V).val * (mfderiv 𝓘(ℝ, specialUnitaryLieAlgebra (n := n))
    𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) (fun W => U * W) V A).val =
      (U * V).val * A.val
  change (U * V).val * (mfderiv 𝓘(ℝ, specialUnitaryLieAlgebra (n := n))
    𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) (fun W => U * W) V A).val =
      U.val * (V.val * A.val) at heA
  exact heA.trans (mul_assoc U.val V.val A.val).symm

/-- Mathlib's geometric invariant field has constant coordinates in the chosen translated atlas. -/
theorem specialUnitary_mulInvariantVectorField (A : specialUnitaryLieAlgebra (n := n))
    (U : Matrix.specialUnitaryGroup n ℂ) :
    mulInvariantVectorField (I := 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)))
      (G := Matrix.specialUnitaryGroup n ℂ) A U = A :=
  specialUnitary_mfderiv_mul_left_apply U 1 A

/-- Its ambient matrix velocity is exactly `U A`. -/
theorem specialUnitary_mulInvariantVectorField_val (A : specialUnitaryLieAlgebra (n := n))
    (U : Matrix.specialUnitaryGroup n ℂ) :
    mfderiv 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ, Matrix n n ℂ)
      (Subtype.val : Matrix.specialUnitaryGroup n ℂ → Matrix n n ℂ) U
      (mulInvariantVectorField (I := 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)))
        (G := Matrix.specialUnitaryGroup n ℂ) A U) = U.val * A.val := by
  rw [specialUnitary_mulInvariantVectorField, (specialUnitary_val_hasMFDerivAt U).mfderiv]
  rfl

end LogSobolev
