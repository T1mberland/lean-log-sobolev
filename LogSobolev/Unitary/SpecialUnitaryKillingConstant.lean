import LogSobolev.Unitary.MatrixRealForm
import LogSobolev.Unitary.SpecialUnitaryKilling
import Mathlib.LinearAlgebra.PID

/-! # Exact Killing coefficient of the real matrix special unitary algebra

The full real matrix trace splits into two identical skew-adjoint traces.
Commutators have traceless range, so restricting further to su preserves the
trace. Together with the matrix-unit computation this gives the exact `2N`
coefficient for the unnormalized Hilbert–Schmidt metric. This is an algebraic
identity; the geometric Ricci formula and the LSI criterion remain separate.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The traceless submodule inside the skew-adjoint real form. -/
noncomputable def tracelessSkewSubmodule : Submodule ℝ (skewAdjoint (Matrix n n ℂ)) :=
  ((Matrix.traceLinearMap n ℝ ℂ).comp
    (skewAdjoint.submodule ℝ (Matrix n n ℂ)).subtype).ker

/-- The nested submodule is the already constructed real special unitary algebra. -/
noncomputable def specialUnitaryTracelessSkewEquiv :
    specialUnitaryLieAlgebra (n := n) ≃ₗ[ℝ] tracelessSkewSubmodule (n := n) where
  toFun A := ⟨⟨A.val, A.prop.1⟩, A.prop.2⟩
  invFun A := ⟨A.val.val, A.val.prop, A.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The double adjoint operator of a skew-Hermitian matrix commutes with star. -/
theorem matrix_double_ad_star (A : Matrix n n ℂ) (hA : star A = -A) (X : Matrix n n ℂ) :
    ((LieAlgebra.ad ℂ (Matrix n n ℂ) A).comp
      (LieAlgebra.ad ℂ (Matrix n n ℂ) A)) (star X) =
    star (((LieAlgebra.ad ℂ (Matrix n n ℂ) A).comp
      (LieAlgebra.ad ℂ (Matrix n n ℂ) A)) X) := by
  have h (Y : Matrix n n ℂ) : ⁅A, star Y⁆ = star ⁅A, Y⁆ := by
    change A * star Y - star Y * A = star (A * Y - Y * A)
    simp only [star_sub, Matrix.star_mul, hA, mul_neg, neg_mul, neg_sub_neg]
  change ⁅A, ⁅A, star X⁆⁆ = star ⁅A, ⁅A, X⁆⁆
  rw [h X, h ⁅A, X⁆]

/-- Restricting double adjoint from the skew-adjoint space to su preserves trace. -/
theorem specialUnitary_killing_eq_skew_trace
    (A : specialUnitaryLieAlgebra (n := n)) :
    killingForm ℝ (specialUnitaryLieAlgebra (n := n)) A A =
      LinearMap.trace ℝ (skewAdjoint (Matrix n n ℂ))
        (matrixSkewMap ((LieAlgebra.ad ℂ (Matrix n n ℂ) A.val).comp
          (LieAlgebra.ad ℂ (Matrix n n ℂ) A.val)) (matrix_double_ad_star A.val A.prop.1)) := by
  let f := matrixSkewMap ((LieAlgebra.ad ℂ (Matrix n n ℂ) A.val).comp
    (LieAlgebra.ad ℂ (Matrix n n ℂ) A.val)) (matrix_double_ad_star A.val A.prop.1)
  have hf : ∀ X, f X ∈ tracelessSkewSubmodule (n := n) := by
    intro X
    change Matrix.trace ⁅A.val, ⁅A.val, X.val⁆⁆ = 0
    change Matrix.trace (A.val * ⁅A.val, X.val⁆ - ⁅A.val, X.val⁆ * A.val) = 0
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  let e := specialUnitaryTracelessSkewEquiv (n := n)
  have he : e.conj ((LieAlgebra.ad ℝ (specialUnitaryLieAlgebra (n := n)) A).comp
      (LieAlgebra.ad ℝ (specialUnitaryLieAlgebra (n := n)) A)) =
      f.restrict (p := tracelessSkewSubmodule) (q := tracelessSkewSubmodule)
        (fun X _ => hf X) := by
    apply LinearMap.ext
    intro X
    rfl
  rw [killingForm_apply_apply, ← LinearMap.trace_conj' _ e, he,
    LinearMap.trace_restrict_eq_of_forall_mem _ f hf]

/-- The exact negative Killing coefficient for the unnormalized HS norm. -/
theorem specialUnitary_killing_self_eq
    (A : specialUnitaryLieAlgebra (n := n)) :
    killingForm ℝ (specialUnitaryLieAlgebra (n := n)) A A =
      -(2 * (Fintype.card n : ℝ)) * ‖A‖ ^ 2 := by
  have h := matrix_real_trace_eq_twice_skew
    ((LieAlgebra.ad ℂ (Matrix n n ℂ) A.val).comp
      (LieAlgebra.ad ℂ (Matrix n n ℂ) A.val)) (matrix_double_ad_star A.val A.prop.1)
  rw [matrix_real_trace_ad_sq A.val A.prop.1 A.prop.2,
    ← specialUnitary_killing_eq_skew_trace A] at h
  rw [specialUnitaryAlgebra_norm]
  linarith

/-- The full real Killing form is exactly `-2N` times the HS inner product. -/
theorem specialUnitary_killing_eq_inner
    (A B : specialUnitaryLieAlgebra (n := n)) :
    killingForm ℝ (specialUnitaryLieAlgebra (n := n)) A B =
      -(2 * (Fintype.card n : ℝ)) * inner ℝ A B := by
  have h (X : specialUnitaryLieAlgebra (n := n)) :
      killingForm ℝ (specialUnitaryLieAlgebra (n := n)) X X =
        -(2 * (Fintype.card n : ℝ)) * inner ℝ X X := by
    rw [real_inner_self_eq_norm_sq]
    exact specialUnitary_killing_self_eq X
  have hab := h (A + B)
  simp only [map_add, LinearMap.add_apply, inner_add_left, inner_add_right] at hab
  have hc : inner ℝ B A = inner ℝ A B := real_inner_comm _ _
  rw [h A, h B, LieModule.traceForm_comm ℝ (specialUnitaryLieAlgebra (n := n))
    (specialUnitaryLieAlgebra (n := n)) B A, hc] at hab
  dsimp only [killingForm] at hab ⊢
  linarith

/-- Real orthonormal commutator energy has coefficient `2N`. -/
theorem specialUnitary_orthonormal_commutator_energy {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    (A : specialUnitaryLieAlgebra (n := n)) :
    (∑ i, ‖⁅A, b i⁆‖ ^ 2) = (2 * (Fintype.card n : ℝ)) * ‖A‖ ^ 2 := by
  have h := specialUnitary_killing_self b A
  rw [specialUnitary_killing_self_eq] at h
  linarith

end LogSobolev
