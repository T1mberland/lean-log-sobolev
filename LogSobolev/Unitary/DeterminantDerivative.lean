import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Differentiating the determinant at the identity

The theorem is stated using scalar entry derivatives, so it is independent of
which equivalent norm is used on finite matrices. Multilinearity reduces the
derivative to row replacements, whose determinants are the diagonal entries.
-/

open Matrix

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Replacing one row of the identity extracts its diagonal entry. -/
theorem det_updateRow_one (v : n → ℂ) (i : n) :
    Matrix.det (Matrix.updateRow (1 : Matrix n n ℂ) i v) = v i := by
  simpa only [← Matrix.vecMul_eq_sum, Matrix.vecMul_one, Matrix.det_one,
    smul_eq_mul, mul_one] using Matrix.det_updateRow_sum (1 : Matrix n n ℂ) i v

/-- The determinant derivative at the identity is the trace, for a curve
specified by its entry derivatives. -/
theorem hasDerivAt_det_at_one (γ : ℝ → Matrix n n ℂ) (A : Matrix n n ℂ) (x : ℝ)
    (hx : γ x = 1) (hγ : ∀ i j, HasDerivAt (fun t => γ t i j) (A i j) x) :
    HasDerivAt (fun t => Matrix.det (γ t)) (Matrix.trace A) x := by
  let D : ContinuousMultilinearMap ℝ (fun _ : n => n → ℂ) ℂ :=
    { (Matrix.detRowAlternating : (n → ℂ) [⋀^n]→ₗ[ℂ] ℂ).toMultilinearMap.restrictScalars ℝ with
      cont := continuous_id.matrix_det }
  have h : HasDerivAt (fun t i j => γ t i j) (fun i j => A i j) x := by
    convert (hasFDerivAt_pi.mpr fun i =>
      hasFDerivAt_pi.mpr fun j => (hγ i j).hasFDerivAt).hasDerivAt using 1
    simp
  have hd := (D.hasFDerivAt (γ x)).comp_hasDerivAt x h
  have hd' : HasDerivAt (fun t => Matrix.det (γ t))
      (∑ i, Matrix.det (Matrix.updateRow (γ x) i (A i))) x := by
    simpa only [ContinuousMultilinearMap.linearDeriv_apply] using hd
  simpa only [hx, det_updateRow_one, Matrix.trace] using hd'

end LogSobolev
