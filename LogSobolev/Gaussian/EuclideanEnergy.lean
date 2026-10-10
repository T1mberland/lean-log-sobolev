import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Euclidean gradient energy

The sum of squared coordinate derivatives is the squared operator norm of the
Fréchet derivative when the domain carries the Euclidean norm. This identity
is the geometry bridge for Gaussian tensorization.
-/

open scoped RealInnerProductSpace

namespace LogSobolev

/-- Parseval's identity for a real linear functional on Euclidean space. -/
theorem sum_sq_apply_single_eq_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : EuclideanSpace ℝ ι →L[ℝ] ℝ) :
    ∑ i, (L (EuclideanSpace.single i 1)) ^ 2 = ‖L‖ ^ 2 := by
  let v := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm L
  have h (i : ι) : L (EuclideanSpace.single i 1) = v i := by
    calc
      L (EuclideanSpace.single i 1) = ⟪v, EuclideanSpace.single i 1⟫ :=
        InnerProductSpace.toDual_symm_apply.symm
      _ = v i := by rw [EuclideanSpace.inner_single_right]; simp
  calc
    ∑ i, (L (EuclideanSpace.single i 1)) ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
      simp [h, Real.norm_eq_abs, sq_abs]
    _ = ‖v‖ ^ 2 := (EuclideanSpace.norm_sq_eq v).symm
    _ = ‖L‖ ^ 2 := by rw [LinearIsometryEquiv.norm_map]

end LogSobolev
