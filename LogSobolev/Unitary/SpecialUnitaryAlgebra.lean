module

public import LogSobolev.Unitary.HilbertSchmidt
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Star.Module

@[expose] public section

attribute [local instance] LieRing.ofAssociativeRing

/-! # The matrix special unitary Lie algebra

The real Lie algebra of traceless skew-Hermitian matrices, with the negative
real trace pairing. Its diagonal agrees exactly with the unnormalized
Hilbert–Schmidt norm squared. These are algebraic results: identification with
the manifold tangent space of SU, curvature, and LSI are not asserted here.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Traceless skew-Hermitian matrices, using the existing associative Lie bracket. -/
def specialUnitaryLieAlgebra : LieSubalgebra ℝ (Matrix n n ℂ) where
  carrier := {A | star A = -A ∧ Matrix.trace A = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro A B ⟨hA, hAt⟩ ⟨hB, hBt⟩
    constructor
    · simp [star_add, hA, hB, add_comm]
    · simp [Matrix.trace_add, hAt, hBt]
  smul_mem' := by
    rintro r A ⟨hA, hAt⟩
    constructor
    · simp [star_smul, hA]
    · simp [Matrix.trace_smul, hAt]
  lie_mem' := by
    rintro A B ⟨hA, hAt⟩ ⟨hB, hBt⟩
    change star (A * B - B * A) = -(A * B - B * A) ∧ _
    constructor
    · simp only [star_sub, Matrix.star_mul, hA, hB, neg_mul_neg, neg_sub]
    · change Matrix.trace (A * B - B * A) = 0
      rw [Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self]

@[simp] theorem mem_specialUnitaryLieAlgebra (A : Matrix n n ℂ) :
    A ∈ (specialUnitaryLieAlgebra : LieSubalgebra ℝ (Matrix n n ℂ)) ↔
      star A = -A ∧ Matrix.trace A = 0 := Iff.rfl

/-- The real trace pairing used for the Hilbert–Schmidt metric on skew-Hermitian
matrices. In particular there is no factor of `1/N`. -/
noncomputable def negTracePair (A B : Matrix n n ℂ) : ℝ := -(Matrix.trace (A * B)).re

omit [DecidableEq n] in
theorem negTracePair_comm (A B : Matrix n n ℂ) : negTracePair A B = negTracePair B A := by
  unfold negTracePair
  rw [Matrix.trace_mul_comm]

/-- Ad-invariance of the trace pairing, stated directly with matrix commutators. -/
theorem negTracePair_lie (A B C : Matrix n n ℂ) :
    negTracePair ⁅A, B⁆ C = negTracePair A ⁅B, C⁆ := by
  unfold negTracePair
  change -(Matrix.trace ((A * B - B * A) * C)).re =
    -(Matrix.trace (A * (B * C - C * B))).re
  rw [sub_mul, mul_sub, Matrix.trace_sub, Matrix.trace_sub, mul_assoc,
    Matrix.trace_mul_cycle B A C, Matrix.trace_mul_comm (C * B) A]

/-- The trace pairing has precisely the Frobenius normalization on every
skew-Hermitian matrix, including the traceless subalgebra. -/
theorem negTracePair_self (A : Matrix n n ℂ) (hA : star A = -A) :
    negTracePair A A = ‖A‖ ^ 2 := by
  have h := congrArg Complex.re (frobenius_norm_sq_eq_trace A)
  change -(Matrix.trace (A * A)).re = _
  simpa only [hA, neg_mul, Matrix.trace_neg, Complex.neg_re, Complex.ofReal_re] using h.symm

theorem specialUnitary_negTracePair_self
    (A : specialUnitaryLieAlgebra (n := n)) :
    negTracePair A.val A.val = ‖A.val‖ ^ 2 :=
  negTracePair_self A.val A.prop.1

/-- Positive definiteness on the real matrix special unitary Lie algebra. -/
theorem specialUnitary_negTracePair_pos
    (A : specialUnitaryLieAlgebra (n := n)) (hA : A ≠ 0) :
    0 < negTracePair A.val A.val := by
  rw [specialUnitary_negTracePair_self]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  apply hA
  exact Subtype.ext hz

/-- The commutator adjoint identity needed to convert the matrix Casimir
calculation into a sum of Hilbert–Schmidt norms. -/
theorem star_lie_of_skewAdjoint (A E : Matrix n n ℂ) (hA : star A = -A) :
    star ⁅E, A⁆ = ⁅star E, A⁆ := by
  change star (E * A - A * E) = star E * A - A * star E
  simp only [star_sub, Matrix.star_mul, hA, neg_mul, mul_neg, neg_sub_neg]

/-- A double-commutator contraction is a squared Frobenius norm. -/
theorem negTracePair_double_lie (A E : Matrix n n ℂ) (hA : star A = -A) :
    negTracePair A ⁅E, ⁅star E, A⁆⁆ = ‖⁅E, A⁆‖ ^ 2 := by
  rw [← negTracePair_lie, ← lie_skew A E]
  unfold negTracePair
  rw [neg_mul, Matrix.trace_neg, Complex.neg_re, neg_neg, Matrix.trace_mul_comm,
    ← star_lie_of_skewAdjoint A E hA, ← frobenius_norm_sq_eq_trace, Complex.ofReal_re]

end LogSobolev
