module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NoncommRing

@[expose] public section

/-! # A finite Casimir commutation calculation

If commutation with `v` acts on a finite family by a skew coefficient matrix,
then its sum of squares commutes with `v`. This purely algebraic lemma applies
to the actual invariant differential operators on smooth SU functions.
-/

namespace LogSobolev

/-- A sum of squares commutes with an element acting by skew coefficients on its directions. -/
theorem sum_squares_commute_of_skew_coefficients
    {K R ι : Type*} [CommRing K] [Ring R] [Algebra K R] [Fintype ι]
    (u : ι → R) (v : R) (c : ι → ι → K)
    (hcomm : ∀ i, u i * v - v * u i = ∑ j, c i j • u j)
    (hskew : ∀ i j, c j i = -c i j) :
    (∑ i, u i * u i) * v = v * (∑ i, u i * u i) := by
  classical
  have hswap : (∑ i, ∑ j, c i j • (u j * u i)) =
      -(∑ i, ∑ j, c i j • (u i * u j)) := by
    rw [Finset.sum_comm]
    calc
      (∑ j, ∑ i, c i j • (u j * u i)) =
          ∑ j, ∑ i, (-c j i) • (u j * u i) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        rw [hskew j i]
      _ = _ := by simp only [neg_smul, Finset.sum_neg_distrib]
  apply sub_eq_zero.mp
  calc
    (∑ i, u i * u i) * v - v * (∑ i, u i * u i) =
        ∑ i, (u i * (u i * v - v * u i) + (u i * v - v * u i) * u i) := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      noncomm_ring
    _ = (∑ i, ∑ j, c i j • (u i * u j)) +
        (∑ i, ∑ j, c i j • (u j * u i)) := by
      simp only [hcomm, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
        smul_mul_assoc, Finset.sum_add_distrib]
    _ = 0 := by rw [hswap, add_neg_cancel]

end LogSobolev
