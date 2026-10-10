import LogSobolev.Unitary.SpecialUnitarySmoothMaps
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Topology.Algebra.Module.Star

/-! # The actual matrix special unitary group as a Lie group

Multiplication and inversion are proved smooth for the constructed atlas by
the ambient smooth-map criterion. No Lie-group structure is assumed. The
exponential map is also smooth.
-/

open Matrix
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix multiplication is smooth for the actual SU atlas. -/
theorem specialUnitary_mul_contMDiff :
    ContMDiff (𝓘(ℝ, specialUnitaryLieAlgebra (n := n)).prod
      𝓘(ℝ, specialUnitaryLieAlgebra (n := n)))
      𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) ∞
      (fun p : Matrix.specialUnitaryGroup n ℂ × Matrix.specialUnitaryGroup n ℂ => p.1 * p.2) := by
  apply contMDiff_specialUnitary_iff.mpr
  have hf : ContMDiff (𝓘(ℝ, specialUnitaryLieAlgebra (n := n)).prod
      𝓘(ℝ, specialUnitaryLieAlgebra (n := n))) 𝓘(ℝ, Matrix n n ℂ) ∞
      (fun p : Matrix.specialUnitaryGroup n ℂ × Matrix.specialUnitaryGroup n ℂ => p.1.val) :=
    (specialUnitary_val_contMDiff (n := n)).comp contMDiff_fst
  have hg : ContMDiff (𝓘(ℝ, specialUnitaryLieAlgebra (n := n)).prod
      𝓘(ℝ, specialUnitaryLieAlgebra (n := n))) 𝓘(ℝ, Matrix n n ℂ) ∞
      (fun p : Matrix.specialUnitaryGroup n ℂ × Matrix.specialUnitaryGroup n ℂ => p.2.val) :=
    (specialUnitary_val_contMDiff (n := n)).comp contMDiff_snd
  exact ContDiff.comp_contMDiff
    (g := fun p : Matrix n n ℂ × Matrix n n ℂ => p.1 * p.2)
    (contDiff_mul (𝕜 := ℝ)) (hf.prodMk_space hg)

/-- Smooth multiplication uses the previously proved smooth atlas. -/
instance specialUnitaryContMDiffMul :
    ContMDiffMul 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) ∞ (Matrix.specialUnitaryGroup n ℂ) where
  toIsManifold := specialUnitaryIsManifold
  contMDiff_mul := specialUnitary_mul_contMDiff

/-- Inversion is smooth because its matrix value is adjoint, a real linear map. -/
theorem specialUnitary_inv_contMDiff :
    ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n))
      𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) ∞
      (fun U : Matrix.specialUnitaryGroup n ℂ => U⁻¹) := by
  apply contMDiff_specialUnitary_iff.mpr
  exact (starL' ℝ : Matrix n n ℂ ≃L[ℝ] Matrix n n ℂ).toContinuousLinearMap.contMDiff.comp
    specialUnitary_val_contMDiff

/-- The original finite-dimensional matrix SU group is a verified smooth Lie group. -/
instance specialUnitaryLieGroup :
    LieGroup 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) ∞ (Matrix.specialUnitaryGroup n ℂ) where
  toContMDiffMul := specialUnitaryContMDiffMul
  contMDiff_inv := specialUnitary_inv_contMDiff

/-- The actual matrix exponential from su into SU is globally smooth. -/
theorem specialUnitary_exp_contMDiff :
    ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n))
      𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) ∞
      (fun A : specialUnitaryLieAlgebra (n := n) => specialUnitaryExpCurve A 1) := by
  apply contMDiff_specialUnitary_iff.mpr
  apply ContDiff.contMDiff
  apply contDiff_iff_contDiffAt.mpr
  intro A
  simpa [specialUnitaryExpCurve, unitaryExpCurve] using
    (NormedSpace.exp_analytic (𝕂 := ℝ) A.val).contDiffAt.comp A
      (specialUnitaryAlgebraInclusion (n := n)).contDiff.contDiffAt

end LogSobolev
