import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-! # Weighted path energies on dyadic grids

The weight on edge `(i,i+1)` of a grid of size `m` is `(i+1)(m-i-1)`.
Interleaving the even and odd subgrids contracts their combined energy,
including the binary-coordinate energy. This finite algebraic estimate is
used to pass a two-point entropy inequality to an interval.
-/

namespace LogSobolev

open Finset

/-- Unnormalized weighted nearest-neighbor energy of a finite sequence. -/
noncomputable def discreteWeightedEnergy (m : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range m, ((i : ℝ) + 1) * ((m : ℝ) - (i + 1)) * (f (i + 1) - f i) ^ 2

/-- Split a finite real sum into its even and odd terms. -/
theorem sum_range_double_real (m : ℕ) (h : ℕ → ℝ) :
    (∑ i ∈ range (m * 2), h i) = ∑ i ∈ range m, (h (i * 2) + h (i * 2 + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, show m * 2 + 2 = (m * 2 + 1) + 1 from rfl,
      sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ring

private theorem sum_shift_eq_of_endpoints (m : ℕ) (h : ℕ → ℝ) (he : h m = h 0) :
    (∑ i ∈ range m, h (i + 1)) = ∑ i ∈ range m, h i := by
  have hs := sum_range_succ' h m
  rw [sum_range_succ, he] at hs
  linarith

private theorem sq_sub_le_twice (a b c : ℝ) :
    (a - c) ^ 2 ≤ 2 * ((a - b) ^ 2 + (b - c) ^ 2) := by
  nlinarith [sq_nonneg (a - 2 * b + c)]

/-- The exact weighted path energy absorbs the binary entropy-recursion cost. -/
theorem discreteWeightedEnergy_double_le (m : ℕ) (f : ℕ → ℝ) :
    discreteWeightedEnergy m (fun i => f (i * 2)) +
      discreteWeightedEnergy m (fun i => f (i * 2 + 1)) +
      (∑ i ∈ range m, (f (i * 2) - f (i * 2 + 1)) ^ 2) ≤
        discreteWeightedEnergy (m * 2) f := by
  let w : ℕ → ℝ := fun i => (i : ℝ) * ((m : ℝ) - i)
  let d : ℕ → ℝ := fun i => (f (i + 1) - f i) ^ 2
  have hw (i : ℕ) (hi : i ∈ range m) : 0 ≤ w (i + 1) := by
    have him : (i : ℝ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_of_lt (mem_range.mp hi))
    dsimp [w]
    push_cast
    exact mul_nonneg (by positivity) (sub_nonneg.mpr him)
  have hshift : (∑ i ∈ range m, w (i + 1) * d (i * 2 + 2)) =
      ∑ i ∈ range m, w i * d (i * 2) := by
    simpa only [Nat.add_mul, Nat.one_mul] using
      sum_shift_eq_of_endpoints m (fun i => w i * d (i * 2)) (by simp [w])
  have hcoarse : discreteWeightedEnergy m (fun i => f (i * 2)) +
      discreteWeightedEnergy m (fun i => f (i * 2 + 1)) ≤
      2 * (∑ i ∈ range m, w (i + 1) * d (i * 2)) +
      4 * (∑ i ∈ range m, w (i + 1) * d (i * 2 + 1)) +
      2 * (∑ i ∈ range m, w (i + 1) * d (i * 2 + 2)) := by
    unfold discreteWeightedEnergy
    rw [← sum_add_distrib]
    calc
      _ ≤ ∑ i ∈ range m,
          (2 * (w (i + 1) * d (i * 2)) +
            4 * (w (i + 1) * d (i * 2 + 1)) +
            2 * (w (i + 1) * d (i * 2 + 2))) := by
        apply sum_le_sum
        intro i hi
        have hA := sq_sub_le_twice (f (i * 2 + 2)) (f (i * 2 + 1)) (f (i * 2))
        have hB := sq_sub_le_twice (f (i * 2 + 3)) (f (i * 2 + 2)) (f (i * 2 + 1))
        have h1 := mul_le_mul_of_nonneg_left hA (hw i hi)
        have h2 := mul_le_mul_of_nonneg_left hB (hw i hi)
        dsimp [w, d] at *
        simp only [Nat.add_mul, Nat.one_mul, Nat.cast_add, Nat.cast_one,
          Nat.add_assoc] at *
        nlinarith
      _ = _ := by simp only [sum_add_distrib, mul_sum]
  rw [hshift] at hcoarse
  have hfine : discreteWeightedEnergy (m * 2) f =
      2 * (∑ i ∈ range m, w (i + 1) * d (i * 2)) +
      4 * (∑ i ∈ range m, w (i + 1) * d (i * 2 + 1)) +
      2 * (∑ i ∈ range m, w i * d (i * 2)) +
      (∑ i ∈ range m, (f (i * 2) - f (i * 2 + 1)) ^ 2) := by
    rw [discreteWeightedEnergy, sum_range_double_real]
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    dsimp [w, d]
    push_cast
    simp only [Nat.add_assoc]
    ring
  rw [hfine]
  linarith

end LogSobolev
