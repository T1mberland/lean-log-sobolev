import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! # The unnormalized Hilbert–Schmidt metric

We use Mathlib's actual `Matrix.unitaryGroup` and its existing Frobenius norm.
Open `Matrix.Norms.Frobenius` wherever metric statements about these groups
are elaborated. In particular, neither the operator norm nor the default
supremum product norm is used in the statements below.
-/

open scoped Matrix.Norms.Frobenius ComplexOrder
open Matrix

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hilbert–Schmidt norm squared is the sum of squared entry norms. -/
theorem frobenius_norm_sq (A : Matrix n n ℂ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
  positivity

/-- Exact normalization: there is no division by the dimension. -/
theorem frobenius_norm_sq_eq_trace (A : Matrix n n ℂ) :
    ((‖A‖ ^ 2 : ℝ) : ℂ) = Matrix.trace (star A * A) := by
  rw [frobenius_norm_sq, Matrix.trace]
  simp only [Complex.ofReal_sum, Complex.ofReal_pow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rfl

/-- A unitary matrix has Hilbert–Schmidt norm `sqrt(card n)`. -/
theorem unitary_norm (U : Matrix.unitaryGroup n ℂ) :
    ‖(U : Matrix n n ℂ)‖ = Real.sqrt (Fintype.card n) := by
  have h := congrArg Complex.re (frobenius_norm_sq_eq_trace (U : Matrix n n ℂ))
  have hs : ‖(U : Matrix n n ℂ)‖ ^ 2 = (Fintype.card n : ℝ) := by
    simpa only [U.prop.1, Matrix.trace_one, Complex.ofReal_re, Complex.natCast_re] using h
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

/-- Left multiplication by a unitary preserves Hilbert–Schmidt norms. -/
theorem norm_unitary_mul (U : Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    ‖(U : Matrix n n ℂ) * A‖ = ‖A‖ := by
  have h : ((‖(U : Matrix n n ℂ) * A‖ ^ 2 : ℝ) : ℂ) = ((‖A‖ ^ 2 : ℝ) : ℂ) := by
    simp only [frobenius_norm_sq_eq_trace, Matrix.star_mul, mul_assoc]
    rw [← mul_assoc (star (U : Matrix n n ℂ)), U.prop.1, one_mul]
  have hr : ‖(U : Matrix n n ℂ) * A‖ ^ 2 = ‖A‖ ^ 2 := by exact_mod_cast h
  nlinarith [norm_nonneg ((U : Matrix n n ℂ) * A), norm_nonneg A]

/-- Right multiplication by a unitary preserves Hilbert–Schmidt norms. -/
theorem norm_mul_unitary (A : Matrix n n ℂ) (U : Matrix.unitaryGroup n ℂ) :
    ‖A * (U : Matrix n n ℂ)‖ = ‖A‖ := by
  have h : ((‖A * (U : Matrix n n ℂ)‖ ^ 2 : ℝ) : ℂ) = ((‖A‖ ^ 2 : ℝ) : ℂ) := by
    simp only [frobenius_norm_sq_eq_trace, Matrix.star_mul]
    rw [Matrix.trace_mul_cycle, mul_assoc, mul_assoc,
      ← mul_assoc (U : Matrix n n ℂ), U.prop.2, one_mul, Matrix.trace_mul_comm]
  have hr : ‖A * (U : Matrix n n ℂ)‖ ^ 2 = ‖A‖ ^ 2 := by exact_mod_cast h
  nlinarith [norm_nonneg (A * (U : Matrix n n ℂ)), norm_nonneg A]

end LogSobolev
