module

public import LogSobolev.Unitary.SpecialUnitaryInner
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Algebra.Lie.TraceForm

@[expose] public section

attribute [local instance 100] LieRing.ofAssociativeRing

/-! # The real Killing form and orthonormal commutator energy

This relates Mathlib's Killing form on the actual real matrix special unitary
algebra to a sum over any real Hilbert–Schmidt orthonormal basis. Unlike the
matrix-unit identity, this is a real orthonormal contraction. Its value as a
multiple of the metric and its interpretation as Ricci curvature still require
separate proofs.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Negative Killing form is the real orthonormal commutator-energy contraction. -/
theorem specialUnitary_killing_self {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    (A : specialUnitaryLieAlgebra (n := n)) :
    killingForm ℝ (specialUnitaryLieAlgebra (n := n)) A A =
      -(∑ i, ‖⁅A, b i⁆‖ ^ 2) := by
  rw [killingForm_apply_apply, LinearMap.trace_eq_sum_inner _ b, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ (b i) ⁅A, ⁅A, b i⁆⁆ = -‖⁅A, b i⁆‖ ^ 2
  have h := specialUnitary_ad_skew A (b i) ⁅A, b i⁆
  rw [real_inner_self_eq_norm_sq] at h
  linarith

/-- The contraction is independent of the choice or index type of real
orthonormal basis. No complex matrix units are used as a real basis. -/
theorem specialUnitary_commutator_energy_basis_independent
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    (c : OrthonormalBasis κ ℝ (specialUnitaryLieAlgebra (n := n)))
    (A : specialUnitaryLieAlgebra (n := n)) :
    (∑ i, ‖⁅A, b i⁆‖ ^ 2) = ∑ j, ‖⁅A, c j⁆‖ ^ 2 := by
  have h := (specialUnitary_killing_self b A).symm.trans (specialUnitary_killing_self c A)
  exact neg_injective h

/-- Nonpositivity follows from the proved ad-invariant positive metric. -/
theorem specialUnitary_killing_self_nonpos
    (A : specialUnitaryLieAlgebra (n := n)) :
    killingForm ℝ (specialUnitaryLieAlgebra (n := n)) A A ≤ 0 := by
  rw [specialUnitary_killing_self (stdOrthonormalBasis ℝ _) A]
  exact neg_nonpos.mpr (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end LogSobolev
