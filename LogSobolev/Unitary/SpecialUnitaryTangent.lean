import LogSobolev.Unitary.SpecialUnitarySmoothMaps
import LogSobolev.Unitary.SpecialUnitary
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-! # Tangent vectors of the matrix special unitary group

For the translated exponential atlas, the derivative of matrix inclusion at `U`
is `A ↦ U A`. It preserves the unnormalized Hilbert–Schmidt norm. This identifies
actual manifold tangent vectors with ambient matrix velocities; it does not yet
construct a Riemannian connection or prove a curvature formula.
-/

open Matrix
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

@[simp] theorem specialUnitaryLocalLog_one :
    specialUnitaryLocalLog (1 : Matrix.specialUnitaryGroup n ℂ) = 0 := by
  have h := (specialUnitaryExpChart (n := n)).left_inv
    zero_mem_specialUnitaryExpChart_source
  change specialUnitaryLocalLog (specialUnitaryExpCurve 0 1) = 0 at h
  have h0 : specialUnitaryExpCurve (0 : specialUnitaryLieAlgebra (n := n)) 1 = 1 := by
    apply Subtype.ext
    simp [specialUnitaryExpCurve, unitaryExpCurve]
  rwa [h0] at h

@[simp] theorem specialUnitary_extChartAt_self (U : Matrix.specialUnitaryGroup n ℂ) :
    extChartAt 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) U U = 0 := by
  rw [specialUnitary_extChartAt_apply, inv_mul_cancel, specialUnitaryLocalLog_one]

/-- The ambient matrix velocity corresponding to a tangent coordinate at `U`. -/
noncomputable def specialUnitaryTangentInclusion (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryLieAlgebra (n := n) →L[ℝ] Matrix n n ℂ :=
  U.val • specialUnitaryAlgebraInclusion

@[simp] theorem specialUnitaryTangentInclusion_apply (U : Matrix.specialUnitaryGroup n ℂ)
    (A : specialUnitaryLieAlgebra (n := n)) :
    specialUnitaryTangentInclusion U A = U.val * A.val := rfl

/-- The derivative in exponential coordinates is left multiplication by `U`. -/
theorem specialUnitary_parametrization_hasFDerivAt (U : Matrix.specialUnitaryGroup n ℂ) :
    HasFDerivAt (fun A : specialUnitaryLieAlgebra (n := n) => U.val * NormedSpace.exp A.val)
      (specialUnitaryTangentInclusion U) 0 := by
  have he : HasFDerivAt (fun A : specialUnitaryLieAlgebra (n := n) => NormedSpace.exp A.val)
      specialUnitaryAlgebraInclusion 0 := by
    simpa using (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix n n ℂ)).comp
      (0 : specialUnitaryLieAlgebra (n := n))
      (specialUnitaryAlgebraInclusion (n := n)).hasFDerivAt
  exact he.const_mul U.val

/-- Matrix inclusion has the expected derivative on the actual manifold tangent space. -/
theorem specialUnitary_val_hasMFDerivAt (U : Matrix.specialUnitaryGroup n ℂ) :
    HasMFDerivAt 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ, Matrix n n ℂ)
      (Subtype.val : Matrix.specialUnitaryGroup n ℂ → Matrix n n ℂ) U
      (specialUnitaryTangentInclusion U) := by
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have heq : writtenInExtChartAt 𝓘(ℝ, specialUnitaryLieAlgebra (n := n))
      𝓘(ℝ, Matrix n n ℂ) U Subtype.val =
      fun A : specialUnitaryLieAlgebra (n := n) => U.val * NormedSpace.exp A.val := by
    funext A
    simpa [writtenInExtChartAt] using specialUnitary_extChartAt_symm_val U A
  rw [heq, specialUnitary_extChartAt_self]
  exact (specialUnitary_parametrization_hasFDerivAt U).hasFDerivWithinAt

/-- No dimension normalization occurs in the manifold-to-matrix tangent map. -/
theorem specialUnitary_mfderiv_val_norm (U : Matrix.specialUnitaryGroup n ℂ)
    (A : specialUnitaryLieAlgebra (n := n)) :
    @norm (Matrix n n ℂ) _ (mfderiv 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ, Matrix n n ℂ)
      (Subtype.val : Matrix.specialUnitaryGroup n ℂ → Matrix n n ℂ) U A) = ‖A‖ := by
  rw [(specialUnitary_val_hasMFDerivAt U).mfderiv]
  change ‖U.val * A.val‖ = ‖A‖
  exact norm_unitary_mul (specialUnitaryInclusion U) A.val

end LogSobolev
