module

public import LogSobolev.Unitary.SpecialUnitaryCasimir
public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Trace

@[expose] public section

attribute [local instance 100] LieRing.ofAssociativeRing

/-! # Traces of matrix adjoint operators

Trace calculations for matrix commutators, as linear maps on the full matrix
space, prepare the restriction to the real special unitary algebra.
-/

open Matrix Module

open scoped Matrix.Norms.Frobenius

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem matrix_basis_repr {ι : Type*} (b : Basis ι ℝ ℂ)
    (A : Matrix n n ℂ) (i j : n) (k : ι) :
    (b.matrix n n).repr A (i, j, k) = b.repr (A i j) k := by
  simp only [Basis.matrix, Basis.map_repr, LinearEquiv.trans_apply, Basis.repr_reindex_apply]
  rfl

/-- Real trace of a complex-linear matrix operator, in real matrix coordinates. -/
theorem matrix_real_trace (T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    LinearMap.trace ℝ (Matrix n n ℂ) (T.restrictScalars ℝ) =
      2 * ∑ i, ∑ j, (T (Matrix.single i j (1 : ℂ)) i j).re := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.matrix n n)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    LinearMap.restrictScalars_apply, Basis.matrix_apply, matrix_basis_repr,
    Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Complex.coe_basisOneI, Matrix.cons_val_zero,
    Matrix.cons_val_one, Complex.coe_basisOneI_repr]
  have hi (i j : n) : Matrix.single i j Complex.I =
      Complex.I • Matrix.single i j (1 : ℂ) := by simp
  simp only [hi, map_smul, Matrix.smul_apply, smul_eq_mul, Complex.I_mul]
  simp [two_mul, Finset.sum_add_distrib]

/-- A diagonal coordinate of the double adjoint operator on a matrix unit. -/
theorem matrix_double_ad_coordinate (A : Matrix n n ℂ) (hA : star A = -A) (i j : n) :
    (⁅A, ⁅A, Matrix.single i j (1 : ℂ)⁆⁆ i j).re =
      -‖⁅Matrix.single i j (1 : ℂ), A⁆‖ ^ 2 := by
  have hs : star (Matrix.single i j (1 : ℂ)) = Matrix.single j i (1 : ℂ) := by
    exact (Matrix.conjTranspose_single i j (1 : ℂ)).trans (by simp)
  have h : negTracePair (Matrix.single j i (1 : ℂ)) ⁅A, ⁅A, Matrix.single i j (1 : ℂ)⁆⁆ =
      negTracePair A ⁅Matrix.single i j (1 : ℂ), ⁅Matrix.single j i (1 : ℂ), A⁆⁆ := by
    rw [← negTracePair_lie, ← negTracePair_lie,
      negTracePair_comm _ (Matrix.single i j (1 : ℂ)), ← negTracePair_lie, negTracePair_comm]
  rw [← hs, negTracePair_double_lie A _ hA] at h
  simpa [negTracePair, hs, Matrix.trace_single_mul] using congrArg Neg.neg h

/-- The full real matrix-space trace has twice the special-unitary coefficient;
restriction to the real skew-adjoint subspace is a separate step. -/
theorem matrix_real_trace_ad_sq (A : Matrix n n ℂ)
    (hA : star A = -A) (htr : Matrix.trace A = 0) :
    LinearMap.trace ℝ (Matrix n n ℂ)
      (((LieAlgebra.ad ℂ (Matrix n n ℂ) A).comp
        (LieAlgebra.ad ℂ (Matrix n n ℂ) A)).restrictScalars ℝ) =
      -(4 * (Fintype.card n : ℝ)) * ‖A‖ ^ 2 := by
  rw [matrix_real_trace]
  change 2 * (∑ i, ∑ j, (⁅A, ⁅A, Matrix.single i j (1 : ℂ)⁆⁆ i j).re) = _
  simp_rw [matrix_double_ad_coordinate A hA]
  simp_rw [Finset.sum_neg_distrib]
  rw [sum_matrixUnits_lie_norm_sq A hA htr]
  ring

end LogSobolev
