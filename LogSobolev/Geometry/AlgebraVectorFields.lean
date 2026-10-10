module

public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

/-! # Invariant vector fields in an ambient real normed algebra

The linear fields `X_A(x) = x * A` have Lie bracket `X_[A,B]`. Their differentiation
operators therefore have the same commutator. These are statements about
Mathlib's derivative and Lie bracket, with no curvature or diffusion assumptions.
They apply in particular to the ambient Frobenius matrices for SU.
-/

open scoped ContDiff

namespace LogSobolev

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- The bracket of right-multiplication fields is the matrix/algebra commutator field. -/
theorem rightMul_lieBracket (A B x : R) :
    VectorField.lieBracket ℝ (fun y : R => y * A) (fun y : R => y * B) x =
      x * (A * B - B * A) := by
  have hB := ((hasFDerivAt_id (𝕜 := ℝ) x).mul_const' B).fderiv
  have hA := ((hasFDerivAt_id (𝕜 := ℝ) x).mul_const' A).fderiv
  simp only [id_eq] at hA hB
  rw [VectorField.lieBracket, hB, hA]
  change (x * A) * B - (x * B) * A = x * (A * B - B * A)
  simp only [mul_sub, mul_assoc]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Differentiation along the ambient field `x ↦ x A`. -/
noncomputable def rightMulDeriv (A : R) (f : R → F) (x : R) : F :=
  fderiv ℝ f x (x * A)

/-- The commutator of differentiation operators along invariant algebra fields.
The second derivative terms cancel by the proved symmetry theorem in Mathlib. -/
theorem rightMulDeriv_commutator (A B x : R) {f : R → F}
    (hf : ContDiffAt ℝ 2 f x) :
    rightMulDeriv A (rightMulDeriv B f) x - rightMulDeriv B (rightMulDeriv A f) x =
      rightMulDeriv (A * B - B * A) f x := by
  have h := VectorField.fderiv_apply_lieBracket hf (by simp)
    ((hasFDerivAt_id (𝕜 := ℝ) x).mul_const' B).differentiableAt
    ((hasFDerivAt_id (𝕜 := ℝ) x).mul_const' A).differentiableAt
  simp only [id_eq] at h
  rw [rightMul_lieBracket] at h
  exact h.symm

end LogSobolev
