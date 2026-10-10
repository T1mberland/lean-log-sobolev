module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

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

set_option backward.isDefEq.respectTransparency false in
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
  have hD (m : n → n → ℂ) : D m = Matrix.det (Matrix.of m) := rfl
  have hd := (D.hasFDerivAt (γ x)).comp_hasDerivAt x h
  have hd' : HasDerivAt (fun t => Matrix.det (γ t))
      (∑ i, Matrix.det (Matrix.updateRow (γ x) i (A i))) x := by
    rw [ContinuousMultilinearMap.linearDeriv_apply] at hd
    simp only [Function.comp_def, hD] at hd
    convert hd using 1 <;> rfl
  simpa only [hx, det_updateRow_one, Matrix.trace, Matrix.diag_apply] using hd'

end LogSobolev
