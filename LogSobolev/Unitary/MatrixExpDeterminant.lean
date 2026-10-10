module

public import LogSobolev.Unitary.UnitaryCurves
public import LogSobolev.Unitary.DeterminantDerivative
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Determinant of the matrix exponential

The identity is proved by differentiating the determinant along a real
exponential curve and using an integrating factor. It applies to all complex
matrices and will identify the determinant-one constraint in local coordinates.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant of a real matrix exponential curve satisfies its scalar ODE. -/
theorem hasDerivAt_det_exp_smul (A : Matrix n n ℂ) (r : ℝ) :
    HasDerivAt (fun t : ℝ => Matrix.det (NormedSpace.exp (t • A)))
      (Matrix.det (NormedSpace.exp (r • A)) * Matrix.trace A) r := by
  let f : ℝ → ℂ := fun s => Matrix.det (NormedSpace.exp (s • A))
  have hmat : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A)) A 0 := by
    simpa using hasDerivAt_exp_smul_const A (0 : ℝ)
  have hf0 : HasDerivAt f (Matrix.trace A) 0 :=
    hasDerivAt_det_at_one _ A 0 (by simp) (hasDerivAt_matrix_entry hmat)
  have hmul (t s : ℝ) : f (t + s) = f t * f s := by
    dsimp [f]
    rw [add_smul, NormedSpace.exp_add_of_commute
      (((Commute.refl A).smul_left t).smul_right s), Matrix.det_mul]
  have hshift : HasDerivAt f (Matrix.trace A) (r - r) := by simpa using hf0
  have hd := (hshift.comp_sub_const r r).const_mul (f r)
  have he : (fun s => f r * f (s - r)) = f := by
    funext s
    rw [← hmul]
    congr 1
    abel
  simpa only [he] using hd

/-- The determinant of the matrix exponential is the scalar exponential of trace. -/
theorem det_exp_smul (A : Matrix n n ℂ) (t : ℝ) :
    Matrix.det (NormedSpace.exp (t • A)) = Complex.exp (t • Matrix.trace A) := by
  let f : ℝ → ℂ := fun s => Matrix.det (NormedSpace.exp (s • A))
  let g : ℝ → ℂ := fun s => f s * Complex.exp (s • (-Matrix.trace A))
  have hg (r : ℝ) : HasDerivAt g 0 r := by
    have he := ((hasDerivAt_id r).smul_const (-Matrix.trace A)).cexp
    have hd := (hasDerivAt_det_exp_smul A r).mul he
    convert hd using 1
    · funext s
      rfl
    · simp only [id_eq, one_smul]
      ring
  have he := is_const_of_deriv_eq_zero (fun r => (hg r).differentiableAt)
    (fun r => (hg r).deriv) t 0
  have hprod : f t * Complex.exp (-(t • Matrix.trace A)) = 1 := by
    simpa [g, f, smul_neg] using he
  have h := congrArg (fun z : ℂ => z * Complex.exp (t • Matrix.trace A)) hprod
  simpa only [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
    mul_one, one_mul] using h

/-- Determinant-exponential identity, without a real parameter. -/
theorem det_matrix_exp (A : Matrix n n ℂ) :
    Matrix.det (NormedSpace.exp A) = Complex.exp (Matrix.trace A) := by
  simpa using det_exp_smul A 1

end LogSobolev
