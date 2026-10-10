module

public import LogSobolev.Geometry.SecondOrderArray
public import LogSobolev.Unitary.SpecialUnitaryKillingConstant
public import LogSobolev.Unitary.SpecialUnitaryDifferentialOperators
public import Mathlib.Analysis.InnerProductSpace.Dual

@[expose] public section

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

/-! # The dimension-dependent second-derivative estimate on SU

The exact Killing contraction, duality, and the proved differential-operator
commutator yield the `N/2` lower bound on second-derivative energy. Identifying
this energy with the carré du champ iteration of the sum-of-squares generator
is a separate obligation; no Γ₂ identity or LSI is assumed here.
-/

open Matrix
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

/-- Dual form of the real orthonormal Killing contraction, with exact coefficient `2N`. -/
theorem specialUnitary_dual_commutator_energy
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    (l : specialUnitaryLieAlgebra (n := n) →L[ℝ] ℝ) :
    (∑ i, ∑ j, (l ⁅b i, b j⁆) ^ 2) =
      (2 * (Fintype.card n : ℝ)) * ∑ i, (l (b i)) ^ 2 := by
  let Z := (InnerProductSpace.toDual ℝ (specialUnitaryLieAlgebra (n := n))).symm l
  have hZ (A : specialUnitaryLieAlgebra (n := n)) : inner ℝ Z A = l A :=
    InnerProductSpace.toDual_symm_apply
  calc
    (∑ i, ∑ j, (l ⁅b i, b j⁆) ^ 2) =
        ∑ i, ∑ j, (inner ℝ ⁅Z, b i⁆ (b j)) ^ 2 := by
      simp_rw [specialUnitary_inner_lie, hZ]
    _ = ∑ i, ‖⁅Z, b i⁆‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact b.sum_sq_inner_left ⁅Z, b i⁆
    _ = (2 * (Fintype.card n : ℝ)) * ‖Z‖ ^ 2 :=
      specialUnitary_orthonormal_commutator_energy b Z
    _ = (2 * (Fintype.card n : ℝ)) * ∑ i, (l (b i)) ^ 2 := by
      rw [← b.sum_sq_inner_left Z]
      simp_rw [hZ]

/-- The commutator derivatives of any real test have energy `2N` times its first derivatives. -/
theorem specialUnitaryDeriv_commutator_energy
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    (f : Matrix.specialUnitaryGroup n ℂ → ℝ) (U : Matrix.specialUnitaryGroup n ℂ) :
    (∑ i, ∑ j, (specialUnitaryDeriv ⁅b i, b j⁆ f U) ^ 2) =
      (2 * (Fintype.card n : ℝ)) * ∑ i, (specialUnitaryDeriv (b i) f U) ^ 2 :=
  specialUnitary_dual_commutator_energy b
    (mfderiv 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) f U)

/-- The `N/2` second-derivative bound for every smooth real test on the actual SU manifold. -/
theorem specialUnitary_second_derivative_energy_lower_bound
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ} {U : Matrix.specialUnitaryGroup n ℂ}
    (hf : ContMDiffAt 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f U) :
    (Fintype.card n : ℝ) / 2 * (∑ i, (specialUnitaryDeriv (b i) f U) ^ 2) ≤
      ∑ i, ∑ j, (specialUnitaryDeriv (b i) (specialUnitaryDeriv (b j) f) U) ^ 2 := by
  have h := sum_sq_sub_transpose_le
    (fun i j => specialUnitaryDeriv (b i) (specialUnitaryDeriv (b j) f) U)
  simp_rw [specialUnitaryDeriv_commutator _ _ hf] at h
  rw [specialUnitaryDeriv_commutator_energy b f U] at h
  linarith

end LogSobolev
