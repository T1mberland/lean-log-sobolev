module

public import LogSobolev.Unitary.SpecialUnitaryPolynomialSpace
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Supremum norm on finite-degree SU polynomial observables

The norm is induced by the injective map to actual continuous functions on the
compact SU group. Finite dimensionality makes the polynomial space complete and
every restricted linear operator continuous. This norm is on the function space;
the group's Hilbert–Schmidt metric is unchanged.
-/

open Matrix
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Forget spatial smoothness while retaining the same pointwise observable. -/
noncomputable def specialUnitaryPolynomialToContinuous (d : ℕ) :
    specialUnitaryPolynomialSpace (n := n) d →ₗ[ℝ] C(Matrix.specialUnitaryGroup n ℂ, ℝ) where
  toFun f := ⟨f.val, f.val.contMDiff.continuous⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem specialUnitaryPolynomialToContinuous_injective (d : ℕ) :
    Function.Injective (specialUnitaryPolynomialToContinuous (n := n) d) := by
  intro f g h
  apply Subtype.ext
  ext U
  exact DFunLike.congr_fun h U

/-- Polynomial observables carry the actual uniform norm on the compact SU group. -/
noncomputable instance specialUnitaryPolynomialNormedAddCommGroup (d : ℕ) :
    NormedAddCommGroup (specialUnitaryPolynomialSpace (n := n) d) :=
  NormedAddCommGroup.induced _ _ (specialUnitaryPolynomialToContinuous d)
    (specialUnitaryPolynomialToContinuous_injective d)

noncomputable instance specialUnitaryPolynomialNormedSpace (d : ℕ) :
    NormedSpace ℝ (specialUnitaryPolynomialSpace (n := n) d) :=
  NormedSpace.induced ℝ _ _ (specialUnitaryPolynomialToContinuous d)

/-- Pointwise inclusion as a continuous linear map into continuous functions. -/
noncomputable def specialUnitaryPolynomialToContinuousCLM (d : ℕ) :
    specialUnitaryPolynomialSpace (n := n) d →L[ℝ] C(Matrix.specialUnitaryGroup n ℂ, ℝ) :=
  (specialUnitaryPolynomialToContinuous d).toContinuousLinearMap

/-- Evaluation at an actual SU matrix is a continuous linear functional. -/
noncomputable def specialUnitaryPolynomialEval (d : ℕ) (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryPolynomialSpace (n := n) d →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ U).comp (specialUnitaryPolynomialToContinuousCLM d)

@[simp] theorem specialUnitaryPolynomialEval_apply (d : ℕ) (U : Matrix.specialUnitaryGroup n ℂ)
    (f : specialUnitaryPolynomialSpace (n := n) d) :
    specialUnitaryPolynomialEval d U f = f.val U := rfl

/-- The actual restricted generator is continuous by finite dimensionality. -/
noncomputable def specialUnitaryPolynomialLaplacianCLM {ι : Type*} [Fintype ι]
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ) :
    specialUnitaryPolynomialSpace (n := n) d →L[ℝ] specialUnitaryPolynomialSpace (n := n) d :=
  LinearMap.toContinuousLinearMap (specialUnitaryPolynomialLaplacian b d)

/-- Invariant differentiation on each polynomial space is a continuous linear map. -/
noncomputable def specialUnitaryPolynomialDerivCLM
    (A : specialUnitaryLieAlgebra (n := n)) (d : ℕ) :
    specialUnitaryPolynomialSpace (n := n) d →L[ℝ] specialUnitaryPolynomialSpace (n := n) d :=
  LinearMap.toContinuousLinearMap ((specialUnitaryDerivEnd A).restrict
    (fun _ h => specialUnitaryDerivEnd_mem_polynomial A d h))

@[simp] theorem specialUnitaryPolynomialDerivCLM_apply
    (A : specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) (U : Matrix.specialUnitaryGroup n ℂ) :
    (specialUnitaryPolynomialDerivCLM A d f).val U = specialUnitaryDeriv A f.val U := rfl

end LogSobolev
