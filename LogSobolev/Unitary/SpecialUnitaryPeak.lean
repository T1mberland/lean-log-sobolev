import LogSobolev.Unitary.SpecialUnitaryPolynomialNorm
import LogSobolev.Unitary.SpecialUnitaryPolynomialFunctionals

/-! # A polynomial peaked at the identity of SU

The affine observable `(N + Re Tr U)/(2N)` lies in `[0,1]`, with equality to
one only at the identity. The proof uses the actual unnormalized
Hilbert–Schmidt norm, via the exact squared distance trace identity.
-/

open Matrix
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Squared HS distance to the identity, with no dimension normalization. -/
theorem specialUnitary_norm_sub_one_sq (U : Matrix.specialUnitaryGroup n ℂ) :
    ‖U.val - 1‖ ^ 2 = 2 * (Fintype.card n : ℝ) - 2 * U.val.trace.re := by
  have h := congrArg Complex.re (frobenius_norm_sq_eq_trace (U.val - 1))
  have hu : star U.val * U.val = 1 := U.prop.1.1
  simp only [star_sub, star_one, sub_mul, mul_sub, mul_one, one_mul] at h
  rw [hu] at h
  simp only [Matrix.trace_sub, Matrix.trace_one, Matrix.star_eq_conjTranspose,
    Matrix.trace_conjTranspose, Complex.sub_re, Complex.natCast_re,
    Complex.star_def, Complex.conj_re, Complex.ofReal_re] at h
  linarith

/-- The corresponding identity for distance to minus the identity. -/
theorem specialUnitary_norm_add_one_sq (U : Matrix.specialUnitaryGroup n ℂ) :
    ‖U.val + 1‖ ^ 2 = 2 * (Fintype.card n : ℝ) + 2 * U.val.trace.re := by
  have h := congrArg Complex.re (frobenius_norm_sq_eq_trace (U.val + 1))
  have hu : star U.val * U.val = 1 := U.prop.1.1
  simp only [star_add, star_one, add_mul, mul_add, mul_one, one_mul] at h
  rw [hu] at h
  simp only [Matrix.trace_add, Matrix.trace_one, Matrix.star_eq_conjTranspose,
    Matrix.trace_conjTranspose, Complex.add_re, Complex.natCast_re,
    Complex.star_def, Complex.conj_re, Complex.ofReal_re] at h
  linarith

/-- A degree-one real polynomial on SU, peaked at identity for positive dimension. -/
noncomputable def specialUnitaryPeak : specialUnitaryPolynomialSpace (n := n) 1 :=
  ⟨specialUnitaryAffineMap
    ((Fintype.card n : ℝ) / (2 * Fintype.card n),
      (2 * (Fintype.card n : ℝ))⁻¹ •
        (Complex.reCLM.comp (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap)), by
    change specialUnitaryAffineMap _ ∈ specialUnitaryAffineSpace ^ 1
    rw [pow_one (specialUnitaryAffineSpace (n := n))]
    exact ⟨_, rfl⟩⟩

/-- Explicit trace formula for the peak polynomial. -/
theorem specialUnitaryPeak_apply (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryPeak.val U =
      ((Fintype.card n : ℝ) + U.val.trace.re) / (2 * Fintype.card n) := by
  change (Fintype.card n : ℝ) / (2 * Fintype.card n) +
    (2 * (Fintype.card n : ℝ))⁻¹ * U.val.trace.re = _
  ring

/-- The peak is nonnegative in the exact HS normalization. -/
theorem specialUnitaryPeak_nonneg (U : Matrix.specialUnitaryGroup n ℂ) : 0 ≤ specialUnitaryPeak.val U := by
  rw [specialUnitaryPeak_apply]
  apply div_nonneg
  · nlinarith [specialUnitary_norm_add_one_sq U, sq_nonneg ‖U.val + 1‖]
  · positivity

/-- Its value at identity is one. -/
theorem specialUnitaryPeak_one (hN : 0 < Fintype.card n) :
    (specialUnitaryPeak (n := n)).val 1 = 1 := by
  rw [specialUnitaryPeak_apply]
  change ((Fintype.card n : ℝ) + (Matrix.trace (1 : Matrix n n ℂ)).re) / _ = _
  simp only [Matrix.trace_one, Complex.natCast_re]
  rw [← two_mul]
  exact div_self (by positivity)

/-- Away from identity the peak is strictly less than one. -/
theorem specialUnitaryPeak_lt_one (hN : 0 < Fintype.card n)
    (U : Matrix.specialUnitaryGroup n ℂ) (hU : U ≠ 1) : specialUnitaryPeak.val U < 1 := by
  have hn : U.val - 1 ≠ 0 := by
    intro h
    apply hU
    exact Subtype.ext (sub_eq_zero.mp h)
  have hp : 0 < ‖U.val - 1‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hn)
  rw [specialUnitaryPeak_apply, div_lt_one (by positivity)]
  nlinarith [specialUnitary_norm_sub_one_sq U]

end LogSobolev
