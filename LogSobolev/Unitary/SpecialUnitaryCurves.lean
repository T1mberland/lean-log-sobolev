module

public import LogSobolev.Unitary.UnitaryCurves
public import LogSobolev.Unitary.MatrixExpDeterminant
public import LogSobolev.Unitary.SpecialUnitary
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

/-! # Curve velocities and exponentials in SU

The matrix special unitary algebra is characterized by differentiable curves
in the actual matrix SU group. Trace-zero exponentials have determinant one,
proved by differentiating their determinant and using the exponential group
law. This is not yet a manifold atlas or a curvature/LSI theorem.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Velocities at the identity of actual SU curves are traceless and
skew-Hermitian. Differentiability is for the unnormalized Frobenius norm. -/
theorem specialUnitary_curve_derivative_mem
    (γ : ℝ → Matrix.specialUnitaryGroup n ℂ) {x : ℝ} {A : Matrix n n ℂ}
    (hγ : HasDerivAt (fun t => (γ t).val) A x) (hx : γ x = 1) :
    A ∈ (specialUnitaryLieAlgebra : LieSubalgebra ℝ (Matrix n n ℂ)) := by
  constructor
  · exact unitary_curve_derivative_skew (fun t => specialUnitaryInclusion (γ t)) hγ
      (by simp [hx])
  · have hd := hasDerivAt_det_at_one (fun t => (γ t).val) A x
      (by simp [hx]) (hasDerivAt_matrix_entry hγ)
    have he : (fun t => Matrix.det (γ t).val) = fun _ => (1 : ℂ) :=
      funext fun t => (γ t).prop.2
    rw [he] at hd
    exact hd.unique (hasDerivAt_const x (1 : ℂ))

/-- The real exponential curve of any trace-zero complex matrix has determinant
one. This specializes the proved determinant-exponential identity. -/
theorem det_exp_smul_eq_one_of_trace_zero (A : Matrix n n ℂ)
    (hA : Matrix.trace A = 0) (t : ℝ) :
    Matrix.det (NormedSpace.exp (t • A)) = 1 := by
  rw [det_exp_smul, hA, smul_zero, Complex.exp_zero]

/-- Exponentiating a real multiple of a matrix in su gives an actual SU element. -/
noncomputable def specialUnitaryExpCurve
    (A : specialUnitaryLieAlgebra (n := n)) (t : ℝ) : Matrix.specialUnitaryGroup n ℂ :=
  ⟨(unitaryExpCurve A.val A.prop.1 t).val,
    (unitaryExpCurve A.val A.prop.1 t).prop,
    det_exp_smul_eq_one_of_trace_zero A.val A.prop.2 t⟩

@[simp] theorem specialUnitaryExpCurve_zero (A : specialUnitaryLieAlgebra (n := n)) :
    specialUnitaryExpCurve A 0 = 1 := by
  apply Subtype.ext
  simp [specialUnitaryExpCurve]

theorem specialUnitaryExpCurve_hasDerivAt_zero
    (A : specialUnitaryLieAlgebra (n := n)) :
    HasDerivAt (fun t => (specialUnitaryExpCurve A t).val) A.val 0 :=
  unitaryExpCurve_hasDerivAt_zero A.val A.prop.1

/-- The algebraic conditions are equivalent to being an actual SU-curve
velocity at the identity. This does not assume a manifold tangent identification. -/
theorem mem_specialUnitaryLieAlgebra_iff_curve_velocity (A : Matrix n n ℂ) :
    A ∈ (specialUnitaryLieAlgebra : LieSubalgebra ℝ (Matrix n n ℂ)) ↔
      ∃ γ : ℝ → Matrix.specialUnitaryGroup n ℂ,
        γ 0 = 1 ∧ HasDerivAt (fun t => (γ t).val) A 0 := by
  constructor
  · intro hA
    exact ⟨specialUnitaryExpCurve ⟨A, hA⟩, specialUnitaryExpCurve_zero _,
      specialUnitaryExpCurve_hasDerivAt_zero _⟩
  · rintro ⟨γ, hγ0, hγ⟩
    exact specialUnitary_curve_derivative_mem γ hγ hγ0

/-- The full exponential-curve derivative, in ambient Frobenius coordinates. -/
theorem specialUnitaryExpCurve_hasDerivAt
    (A : specialUnitaryLieAlgebra (n := n)) (t : ℝ) :
    HasDerivAt (fun s => (specialUnitaryExpCurve A s).val)
      ((specialUnitaryExpCurve A t).val * A.val) t :=
  hasDerivAt_exp_smul_const A.val t

/-- The exponential curve has constant speed equal to the unnormalized
Hilbert–Schmidt norm of its generator. -/
theorem specialUnitaryExpCurve_speed
    (A : specialUnitaryLieAlgebra (n := n)) (t : ℝ) :
    ‖deriv (fun s => (specialUnitaryExpCurve A s).val) t‖ = ‖A.val‖ := by
  rw [(specialUnitaryExpCurve_hasDerivAt A t).deriv]
  exact norm_unitary_mul (specialUnitaryInclusion (specialUnitaryExpCurve A t)) A.val

/-- Left translation of a curve velocity to the identity puts it in the
verified traceless skew-Hermitian algebra. -/
theorem specialUnitary_curve_velocity_leftTranslate
    (γ : ℝ → Matrix.specialUnitaryGroup n ℂ) {x : ℝ} {A : Matrix n n ℂ}
    (hγ : HasDerivAt (fun t => (γ t).val) A x) :
    ((γ x)⁻¹).val * A ∈
      (specialUnitaryLieAlgebra : LieSubalgebra ℝ (Matrix n n ℂ)) := by
  exact specialUnitary_curve_derivative_mem (fun t => (γ x)⁻¹ * γ t)
    (hγ.const_mul ((γ x)⁻¹).val) (by simp)

/-- Left trivialization of velocities preserves the Frobenius norm. -/
theorem specialUnitary_velocity_leftTranslate_norm
    (U : Matrix.specialUnitaryGroup n ℂ) (A : Matrix n n ℂ) :
    ‖(U⁻¹).val * A‖ = ‖A‖ :=
  norm_unitary_mul (specialUnitaryInclusion U⁻¹) A

/-- Exponential curves are globally Lipschitz for the actual SU Frobenius metric,
with constant the Hilbert–Schmidt norm of their generator. -/
theorem specialUnitaryExpCurve_lipschitz
    (A : specialUnitaryLieAlgebra (n := n)) :
    LipschitzWith ‖A.val‖₊ (specialUnitaryExpCurve A) := by
  have h : LipschitzWith ‖A.val‖₊ (fun t => (specialUnitaryExpCurve A t).val) :=
    lipschitzWith_of_nnnorm_deriv_le
      (fun t => (specialUnitaryExpCurve_hasDerivAt A t).differentiableAt)
      (fun t => by
        change ‖deriv (fun s => (specialUnitaryExpCurve A s).val) t‖ ≤ ‖A.val‖
        exact (specialUnitaryExpCurve_speed A t).le)
  exact h

end LogSobolev
