import LogSobolev.Unitary.SpecialUnitaryAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # The Hilbert–Schmidt inner product on su

The real negative trace pairing is an inner product inducing exactly the
ambient Frobenius norm. This equips the verified matrix Lie algebra with the
metric structure needed for orthonormal contractions, without asserting any
manifold or curvature identification.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable instance specialUnitaryAlgebraNormedAddCommGroup :
    NormedAddCommGroup (specialUnitaryLieAlgebra (n := n)) :=
  inferInstanceAs (NormedAddCommGroup specialUnitaryLieAlgebra.toSubmodule)

noncomputable instance specialUnitaryAlgebraNormedSpace :
    NormedSpace ℝ (specialUnitaryLieAlgebra (n := n)) :=
  inferInstanceAs (NormedSpace ℝ specialUnitaryLieAlgebra.toSubmodule)

instance specialUnitaryAlgebraFiniteDimensional :
    FiniteDimensional ℝ (specialUnitaryLieAlgebra (n := n)) :=
  inferInstanceAs (FiniteDimensional ℝ specialUnitaryLieAlgebra.toSubmodule)

/-- The real trace inner product with the existing unnormalized Frobenius norm. -/
noncomputable instance specialUnitaryAlgebraInnerProductSpace :
    InnerProductSpace ℝ (specialUnitaryLieAlgebra (n := n)) where
  inner A B := negTracePair A.val B.val
  norm_sq_eq_re_inner A := (specialUnitary_negTracePair_self A).symm
  conj_inner_symm A B := negTracePair_comm B.val A.val
  add_left A B C := by
    change negTracePair (A.val + B.val) C.val = _
    simp [negTracePair, add_mul, Matrix.trace_add, add_comm]
  smul_left A B r := by
    change negTracePair (r • A.val) B.val = r * negTracePair A.val B.val
    simp [negTracePair, Matrix.trace_smul]

@[simp] theorem specialUnitaryAlgebra_inner
    (A B : specialUnitaryLieAlgebra (n := n)) :
    inner ℝ A B = negTracePair A.val B.val := rfl

@[simp] theorem specialUnitaryAlgebra_norm
    (A : specialUnitaryLieAlgebra (n := n)) : ‖A‖ = ‖A.val‖ := rfl

/-- The inner product is invariant under the Lie bracket. -/
theorem specialUnitary_inner_lie
    (A B C : specialUnitaryLieAlgebra (n := n)) :
    inner ℝ ⁅A, B⁆ C = inner ℝ A ⁅B, C⁆ :=
  negTracePair_lie A.val B.val C.val

/-- The infinitesimal adjoint action is skew-symmetric for the exact HS metric. -/
theorem specialUnitary_ad_skew
    (A B C : specialUnitaryLieAlgebra (n := n)) :
    inner ℝ ⁅A, B⁆ C = -inner ℝ B ⁅A, C⁆ := by
  rw [← specialUnitary_inner_lie B A C, ← lie_skew A B, inner_neg_left]

end LogSobolev
