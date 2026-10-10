import LogSobolev.Unitary.SpecialUnitaryGenerator
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

/-! # Invariant differentiation as actual linear endomorphisms

The space here consists of genuine smooth real functions on the verified SU
manifold. Its endomorphisms below are constructed from `mfderiv`; linearity and
the operator commutator are proved, not supplied as representation assumptions.
-/

open Matrix
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The existing Mathlib space of smooth real functions on the actual SU manifold. -/
abbrev specialUnitarySmoothFunctions :=
  C^∞⟮𝓘(ℝ, specialUnitaryLieAlgebra (n := n)), Matrix.specialUnitaryGroup n ℂ; ℝ⟯

variable {n}

/-- Invariant differentiation as a real linear endomorphism of smooth functions. -/
noncomputable def specialUnitaryDerivEnd (A : specialUnitaryLieAlgebra (n := n)) :
    Module.End ℝ (specialUnitarySmoothFunctions n) where
  toFun f := ⟨specialUnitaryDeriv A f, specialUnitaryDeriv_contMDiff A f.contMDiff⟩
  map_add' f g := by
    ext U
    exact congrFun (specialUnitaryDeriv_add A f.contMDiff g.contMDiff) U
  map_smul' r f := by
    ext U
    exact DFunLike.congr_fun
      ((f.contMDiff.mdifferentiableAt (by decide)).hasMFDerivAt.const_smul r).mfderiv A

@[simp] theorem specialUnitaryDerivEnd_apply (A : specialUnitaryLieAlgebra (n := n))
    (f : specialUnitarySmoothFunctions n) (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryDerivEnd A f U = specialUnitaryDeriv A f U := rfl

/-- Linearity in the differentiating direction is inherited from the actual differential. -/
noncomputable def specialUnitaryDerivRepresentation :
    specialUnitaryLieAlgebra (n := n) →ₗ[ℝ] Module.End ℝ (specialUnitarySmoothFunctions n) where
  toFun := specialUnitaryDerivEnd
  map_add' A B := by
    ext f U
    exact map_add (mfderiv 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) f U) A B
  map_smul' r A := by
    ext f U
    exact map_smul (mfderiv 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) f U) r A

/-- The representation obeys the matrix Lie bracket on all smooth tests. -/
theorem specialUnitaryDerivEnd_commutator (A B : specialUnitaryLieAlgebra (n := n)) :
    specialUnitaryDerivEnd A * specialUnitaryDerivEnd B -
      specialUnitaryDerivEnd B * specialUnitaryDerivEnd A = specialUnitaryDerivEnd ⁅A, B⁆ := by
  ext f U
  exact specialUnitaryDeriv_commutator A B f.contMDiff.contMDiffAt

end LogSobolev
