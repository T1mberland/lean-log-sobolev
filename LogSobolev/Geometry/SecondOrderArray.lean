module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # The antisymmetric part of a real second-derivative array

The squared norm of an antisymmetrized array is at most four times the squared
norm of the original array. This elementary estimate converts commutator energy
into a lower bound on second derivatives, without defining curvature by fiat.
-/

namespace LogSobolev

/-- Antisymmetrization has squared operator norm at most four. -/
theorem sum_sq_sub_transpose_le {ι : Type*} [Fintype ι] (H : ι → ι → ℝ) :
    (∑ i, ∑ j, (H i j - H j i) ^ 2) ≤ 4 * ∑ i, ∑ j, H i j ^ 2 := by
  classical
  have hs : (∑ i, ∑ j, H j i ^ 2) = ∑ i, ∑ j, H i j ^ 2 := Finset.sum_comm
  calc
    (∑ i, ∑ j, (H i j - H j i) ^ 2) ≤
        ∑ i, ∑ j, (2 * H i j ^ 2 + 2 * H j i ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      nlinarith [sq_nonneg (H i j + H j i)]
    _ = 2 * (∑ i, ∑ j, H i j ^ 2) + 2 * (∑ i, ∑ j, H j i ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = 4 * ∑ i, ∑ j, H i j ^ 2 := by rw [hs]; ring

end LogSobolev
