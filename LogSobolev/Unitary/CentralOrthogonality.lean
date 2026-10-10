import LogSobolev.Unitary.SpecialUnitaryAlgebra

/-! # Central and traceless directions are Hilbert–Schmidt orthogonal

This is the exact quadratic identity needed when combining phase and SU
energies. The norm is the unnormalized Frobenius norm, so the central term
contains the full dimension.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A traceless matrix is HS-orthogonal to every scalar matrix. -/
theorem frobenius_norm_sq_add_scalar (A : Matrix n n ℂ) (hA : Matrix.trace A = 0)
    (z : ℂ) :
    ‖A + z • (1 : Matrix n n ℂ)‖ ^ 2 = ‖A‖ ^ 2 + ‖z‖ ^ 2 * Fintype.card n := by
  have hs : Matrix.trace (star A) = 0 := by
    change Matrix.trace Aᴴ = 0
    rw [Matrix.trace_conjTranspose, hA, star_zero]
  have hz : ‖z • (1 : Matrix n n ℂ)‖ ^ 2 = ‖z‖ ^ 2 * Fintype.card n := by
    rw [norm_smul, mul_pow]
    have hi := unitary_norm (1 : Matrix.unitaryGroup n ℂ)
    change ‖(1 : Matrix n n ℂ)‖ = Real.sqrt (Fintype.card n) at hi
    rw [hi, Real.sq_sqrt (by positivity)]
  have h : ((‖A + z • (1 : Matrix n n ℂ)‖ ^ 2 : ℝ) : ℂ) =
      ((‖A‖ ^ 2 : ℝ) : ℂ) + ((‖z • (1 : Matrix n n ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    simp only [frobenius_norm_sq_eq_trace, star_add, add_mul, mul_add, Matrix.trace_add]
    simp only [star_smul, star_one, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul,
      Matrix.trace_smul, hs, hA, smul_zero, zero_add, add_zero]
  have hr : ‖A + z • (1 : Matrix n n ℂ)‖ ^ 2 = ‖A‖ ^ 2 + ‖z • (1 : Matrix n n ℂ)‖ ^ 2 := by
    exact_mod_cast h
  rwa [hz] at hr

/-- The phase direction in Theorem 15 contributes exactly `2 c²` to squared speed. -/
theorem specialUnitary_phase_velocity_norm_sq (N : ℕ) (hN : 0 < N)
    (A : specialUnitaryLieAlgebra (n := Fin N)) (c : ℝ) :
    ‖A.val + (Complex.I * ((Real.sqrt (2 / (N : ℝ)) * c : ℝ) : ℂ)) •
      (1 : Matrix (Fin N) (Fin N) ℂ)‖ ^ 2 = ‖A.val‖ ^ 2 + 2 * c ^ 2 := by
  rw [frobenius_norm_sq_add_scalar A.val A.prop.2]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, mul_pow, Real.sq_sqrt (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hNr.le), Fintype.card_fin]
  congr 1
  field_simp

end LogSobolev
