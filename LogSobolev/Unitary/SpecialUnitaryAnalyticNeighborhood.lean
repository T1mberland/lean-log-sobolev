module

public import LogSobolev.Unitary.MatrixLocalExponential
public import Mathlib.Analysis.Analytic.ChangeOrigin

@[expose] public section

attribute [local instance 100] LieRing.ofAssociativeRing

/-! # Analytic exponential neighborhoods for SU

The ambient inverse is analytic throughout an open identity neighborhood.
Shrinking the proved exponential coordinates to this neighborhood preserves
both inverse identities and the exact correspondence between su and SU.
-/

open Matrix Set
open scoped Matrix.Norms.Frobenius ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual local inverse supplied by the inverse function theorem is analytic. -/
theorem matrixLog_analyticAt_one :
    AnalyticAt ℝ (matrixExpLocalHomeomorph (n := n)).symm 1 :=
  (matrixLog_contDiffAt_one ω).analyticAt

/-- An open set on which the actual ambient local logarithm is analytic. -/
def matrixLogDomain : Set (Matrix n n ℂ) :=
  {B | AnalyticAt ℝ (matrixExpLocalHomeomorph (n := n)).symm B}

theorem isOpen_matrixLogDomain : IsOpen (matrixLogDomain (n := n)) :=
  isOpen_analyticAt ℝ _

theorem one_mem_matrixLogDomain : (1 : Matrix n n ℂ) ∈ matrixLogDomain :=
  matrixLog_analyticAt_one

/-- Ambient chart transition expressions are analytic wherever their logarithm
argument lies in the proved analytic domain. -/
theorem matrixLog_mul_exp_analyticAt (P A : Matrix n n ℂ)
    (h : P * NormedSpace.exp A ∈ matrixLogDomain) :
    AnalyticAt ℝ (fun X : Matrix n n ℂ =>
      (matrixExpLocalHomeomorph (n := n)).symm (P * NormedSpace.exp X)) A := by
  have hg : AnalyticAt ℝ (fun X : Matrix n n ℂ => P * NormedSpace.exp X) A :=
    analyticAt_const.mul (NormedSpace.exp_analytic (𝕂 := ℝ) A)
  exact (show AnalyticAt ℝ (matrixExpLocalHomeomorph (n := n)).symm
    (P * NormedSpace.exp A) from h).comp
      (f := fun X : Matrix n n ℂ => P * NormedSpace.exp X) (x := A) hg

/-- The SU-compatible ambient exponential coordinates can be chosen with
analytic inverse everywhere on their target, not just at identity. -/
theorem exists_specialUnitary_analytic_exp :
    ∃ e : OpenPartialHomeomorph (Matrix n n ℂ) (Matrix n n ℂ),
      (∀ A, e A = NormedSpace.exp A) ∧ (0 : Matrix n n ℂ) ∈ e.source ∧
      (1 : Matrix n n ℂ) ∈ e.target ∧
      (∀ A ∈ e.source, e A ∈ Matrix.specialUnitaryGroup n ℂ ↔
        A ∈ (specialUnitaryLieAlgebra : LieSubalgebra ℝ (Matrix n n ℂ))) ∧
      (∀ B ∈ e.target, AnalyticAt ℝ e.symm B) := by
  obtain ⟨U, hU, hU0, hUs, _, hiff⟩ := exists_specialUnitary_exp_neighborhood (n := n)
  let V := U ∩ (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) ⁻¹' matrixLogDomain
  have hV : IsOpen V := hU.inter (isOpen_matrixLogDomain.preimage NormedSpace.exp_continuous)
  let e := (matrixExpLocalHomeomorph (n := n)).restrOpen V hV
  have he (A : Matrix n n ℂ) : e A = NormedSpace.exp A := rfl
  have h0 : (0 : Matrix n n ℂ) ∈ e.source := by
    refine ⟨hUs hU0, hU0, ?_⟩
    simpa only [mem_preimage, NormedSpace.exp_zero] using one_mem_matrixLogDomain (n := n)
  refine ⟨e, he, h0, ?_, ?_, ?_⟩
  · simpa only [he, NormedSpace.exp_zero] using e.map_source h0
  · intro A hA
    exact hiff A hA.2.1
  · intro B hB
    have h := hB.2.2
    change AnalyticAt ℝ (matrixExpLocalHomeomorph (n := n)).symm
      ((matrixExpLocalHomeomorph (n := n)) ((matrixExpLocalHomeomorph (n := n)).symm B)) at h
    rw [matrixExpLocalHomeomorph.right_inv hB.1] at h
    exact h

end LogSobolev
