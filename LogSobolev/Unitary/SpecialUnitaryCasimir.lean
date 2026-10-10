import LogSobolev.Unitary.SpecialUnitaryAlgebra
import LogSobolev.Unitary.MatrixCasimir

/-! # Hilbert–Schmidt commutator energy on the matrix special unitary algebra

The sum over complex matrix units is exactly `2N` times the squared norm.
Matrix units are not a real orthonormal basis of the special unitary algebra;
identifying this expression with the Riemannian Ricci contraction is a further
proof obligation. In particular, this module asserts neither Ricci curvature
nor a logarithmic Sobolev inequality.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Linearity in the second slot, in finite-sum form. -/
theorem negTracePair_sum_right {ι : Type*} (s : Finset ι)
    (A : Matrix n n ℂ) (B : ι → Matrix n n ℂ) :
    negTracePair A (∑ i ∈ s, B i) = ∑ i ∈ s, negTracePair A (B i) := by
  simp [negTracePair, Matrix.mul_sum, Matrix.trace_sum]

/-- The exact commutator-energy identity for any traceless skew-Hermitian
matrix. The Frobenius norm in this statement is unnormalized. -/
theorem sum_matrixUnits_lie_norm_sq (A : Matrix n n ℂ)
    (hA : star A = -A) (htr : Matrix.trace A = 0) :
    (∑ i : n, ∑ j : n, ‖⁅Matrix.single i j (1 : ℂ), A⁆‖ ^ 2) =
      (2 * (Fintype.card n : ℝ)) * ‖A‖ ^ 2 := by
  have hs (i j : n) : star (Matrix.single i j (1 : ℂ)) = Matrix.single j i 1 := by
    exact (Matrix.conjTranspose_single i j (1 : ℂ)).trans (by simp)
  calc
    _ = ∑ i : n, ∑ j : n,
        negTracePair A ⁅Matrix.single i j (1 : ℂ), ⁅Matrix.single j i (1 : ℂ), A⁆⁆ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← hs i j, negTracePair_double_lie A _ hA]
    _ = negTracePair A
        (∑ i : n, ∑ j : n, ⁅Matrix.single i j (1 : ℂ), ⁅Matrix.single j i (1 : ℂ), A⁆⁆) := by
      simp only [negTracePair_sum_right]
    _ = (2 * (Fintype.card n : ℝ)) * ‖A‖ ^ 2 := by
      rw [sum_matrixUnits_double_lie_of_trace_zero A htr, ← negTracePair_self A hA]
      simp [negTracePair, Matrix.trace_smul, smul_eq_mul, Complex.mul_re]

/-- The same identity on the actual traceless skew-Hermitian Lie subalgebra. -/
theorem specialUnitary_commutator_energy
    (A : specialUnitaryLieAlgebra (n := n)) :
    (∑ i : n, ∑ j : n, ‖⁅Matrix.single i j (1 : ℂ), A.val⁆‖ ^ 2) =
      (2 * (Fintype.card n : ℝ)) * ‖A.val‖ ^ 2 :=
  sum_matrixUnits_lie_norm_sq A.val A.prop.1 A.prop.2

end LogSobolev
