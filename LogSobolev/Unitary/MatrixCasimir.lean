module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Tactic.Abel

@[expose] public section

attribute [local instance 100] LieRing.ofAssociativeRing

/-! # Double commutators with matrix units

The exact dimension factor in the matrix Casimir identity is `2 * card n`.
This algebraic identity is an ingredient of the SU Ricci calculation. It is
not itself a Ricci theorem: no tangent identification, connection, curvature,
or analytic criterion is asserted by this module.
-/

open Matrix

namespace LogSobolev

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The sum of products of paired matrix units is dimension times identity. -/
theorem sum_matrixUnits_mul_swap :
    (∑ i : n, ∑ j : n, (Matrix.single i j (1 : R)) * Matrix.single j i (1 : R)) =
      (Fintype.card n : R) • (1 : Matrix n n R) := by
  simp only [Matrix.single_mul_single_same, one_mul, Finset.sum_const,
    Finset.card_univ, ← Finset.smul_sum, Matrix.sum_single_one]
  simp [Nat.cast_smul_eq_nsmul R]

/-- Averaging all matrix-unit sandwiches extracts the trace. -/
theorem sum_matrixUnits_sandwich (A : Matrix n n R) :
    (∑ i : n, ∑ j : n, Matrix.single i j (1 : R) * A * Matrix.single j i (1 : R)) =
      Matrix.trace A • (1 : Matrix n n R) := by
  simp only [Matrix.single_mul_mul_single, one_mul, mul_one]
  ext a b
  by_cases h : a = b
  · subst b
    simp [Matrix.sum_apply, Matrix.single_apply, Matrix.trace]
  · have hne (i : n) : ¬(i = a ∧ i = b) := fun hi => h (hi.1.symm.trans hi.2)
    simp [Matrix.sum_apply, hne, h]

/-- The full matrix double-commutator identity, with its scalar kernel visible. -/
theorem sum_matrixUnits_double_lie (A : Matrix n n R) :
    (∑ i : n, ∑ j : n, ⁅Matrix.single i j (1 : R), ⁅Matrix.single j i (1 : R), A⁆⁆) =
      (2 * (Fintype.card n : R)) • A - (2 * Matrix.trace A) • (1 : Matrix n n R) := by
  simp only [LieRing.of_associative_ring_bracket, mul_sub, sub_mul,
    Finset.sum_sub_distrib]
  have hleft : (∑ i : n, ∑ j : n,
      Matrix.single i j (1 : R) * (Matrix.single j i (1 : R) * A)) = (Fintype.card n : R) • A := by
    simp only [← mul_assoc, ← Matrix.sum_mul, sum_matrixUnits_mul_swap, smul_mul_assoc,
      one_mul]
  have hright : (∑ i : n, ∑ j : n,
      (A * Matrix.single j i (1 : R)) * Matrix.single i j (1 : R)) = (Fintype.card n : R) • A := by
    rw [Finset.sum_comm]
    simp only [mul_assoc, ← Matrix.mul_sum, sum_matrixUnits_mul_swap, mul_smul_comm,
      mul_one]
  have hmid : (∑ i : n, ∑ j : n,
      (Matrix.single j i (1 : R) * A) * Matrix.single i j (1 : R)) = Matrix.trace A • (1 : Matrix n n R) := by
    rw [Finset.sum_comm]
    exact sum_matrixUnits_sandwich A
  rw [hleft, hright, hmid]
  simp only [← mul_assoc, sum_matrixUnits_sandwich]
  simp only [two_mul, add_smul]
  abel

/-- On traceless matrices the Casimir expression is exactly `2N` times the matrix. -/
theorem sum_matrixUnits_double_lie_of_trace_zero (A : Matrix n n R)
    (hA : Matrix.trace A = 0) :
    (∑ i : n, ∑ j : n, ⁅Matrix.single i j (1 : R), ⁅Matrix.single j i (1 : R), A⁆⁆) =
      (2 * (Fintype.card n : R)) • A := by
  rw [sum_matrixUnits_double_lie, hA, mul_zero, zero_smul, sub_zero]

end LogSobolev
