module

public import LogSobolev.Unitary.MatrixExpDeterminant
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

/-! # Local matrix exponential coordinates

The inverse function theorem makes matrix exponential a local homeomorphism
at zero. On a sufficiently small open neighborhood, its inverse image of SU
is exactly the traceless skew-Hermitian algebra. All topologies are the
existing unnormalized Frobenius topologies.
-/

open Matrix Metric Filter Set Topology
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix exponential has invertible strict derivative at zero. -/
theorem matrixExp_hasStrictFDerivAt_zero :
    HasStrictFDerivAt (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ)
      (ContinuousLinearEquiv.refl ℝ (Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ) 0 :=
  hasStrictFDerivAt_exp_zero

/-- The ambient exponential as an actual local homeomorphism at zero. -/
noncomputable def matrixExpLocalHomeomorph :
    OpenPartialHomeomorph (Matrix n n ℂ) (Matrix n n ℂ) :=
  matrixExp_hasStrictFDerivAt_zero.toOpenPartialHomeomorph NormedSpace.exp

@[simp] theorem matrixExpLocalHomeomorph_apply (A : Matrix n n ℂ) :
    matrixExpLocalHomeomorph A = NormedSpace.exp A := rfl

theorem zero_mem_matrixExpLocalHomeomorph_source :
    (0 : Matrix n n ℂ) ∈ matrixExpLocalHomeomorph.source :=
  matrixExp_hasStrictFDerivAt_zero.mem_toOpenPartialHomeomorph_source

theorem one_mem_matrixExpLocalHomeomorph_target :
    (1 : Matrix n n ℂ) ∈ matrixExpLocalHomeomorph.target := by
  simpa [matrixExpLocalHomeomorph] using (matrixExp_hasStrictFDerivAt_zero (n := n)).image_mem_toOpenPartialHomeomorph_target

@[simp] theorem matrixExpLocalHomeomorph_symm_one :
    (matrixExpLocalHomeomorph (n := n)).symm 1 = 0 := by
  simpa only [matrixExpLocalHomeomorph_apply, NormedSpace.exp_zero] using
    (matrixExpLocalHomeomorph (n := n)).left_inv zero_mem_matrixExpLocalHomeomorph_source

/-- The actual local inverse has the identity as strict derivative at identity. -/
theorem matrixLog_hasStrictFDerivAt_one :
    HasStrictFDerivAt (matrixExpLocalHomeomorph (n := n)).symm
      (ContinuousLinearEquiv.refl ℝ (Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ) 1 := by
  simpa only [matrixExpLocalHomeomorph, HasStrictFDerivAt.localInverse,
    NormedSpace.exp_zero, ContinuousLinearEquiv.refl_symm] using
    (matrixExp_hasStrictFDerivAt_zero (n := n)).to_localInverse

/-- Local matrix logarithm has every order of smoothness at identity. -/
theorem matrixLog_contDiffAt_one (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (matrixExpLocalHomeomorph (n := n)).symm 1 := by
  apply (matrixExpLocalHomeomorph (n := n)).contDiffAt_symm
    one_mem_matrixExpLocalHomeomorph_target
    (f₀' := ContinuousLinearEquiv.refl ℝ (Matrix n n ℂ))
  · rw [matrixExpLocalHomeomorph_symm_one]
    exact matrixExp_hasStrictFDerivAt_zero.hasFDerivAt
  · rw [matrixExpLocalHomeomorph_symm_one]
    exact (NormedSpace.exp_analytic (𝕂 := ℝ) (0 : Matrix n n ℂ)).contDiffAt

/-- Ambient local exponential coordinates contain an ordinary Frobenius ball. -/
theorem exists_matrixExp_injective_ball : ∃ r : ℝ, 0 < r ∧
    ball (0 : Matrix n n ℂ) r ⊆ matrixExpLocalHomeomorph.source ∧
    InjOn (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) (ball 0 r) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (matrixExpLocalHomeomorph.open_source.mem_nhds
      (zero_mem_matrixExpLocalHomeomorph_source (n := n)))
  exact ⟨r, hr, hball, matrixExpLocalHomeomorph.injOn.mono hball⟩

/-- On an injectivity ball, the unitary constraint is exactly skew-adjointness. -/
theorem exp_mem_unitary_iff_of_injective_ball {r : ℝ}
    (hinj : InjOn (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) (ball 0 r))
    (A : Matrix n n ℂ) (hA : A ∈ ball 0 r) :
    NormedSpace.exp A ∈ Matrix.unitaryGroup n ℂ ↔ star A = -A := by
  constructor
  · intro hU
    have hs : star A ∈ ball (0 : Matrix n n ℂ) r := by
      simpa only [Metric.mem_ball, dist_zero_right, norm_star] using hA
    have hn : -A ∈ ball (0 : Matrix n n ℂ) r := by
      simpa only [Metric.mem_ball, dist_zero_right, norm_neg] using hA
    apply hinj hs hn
    have he : NormedSpace.exp A * NormedSpace.exp (-A) = 1 := by
      rw [← NormedSpace.exp_add_of_commute (Commute.refl A).neg_right]
      simp
    calc
      NormedSpace.exp (star A) = star (NormedSpace.exp A) := (NormedSpace.star_exp A).symm
      _ = star (NormedSpace.exp A) * (NormedSpace.exp A * NormedSpace.exp (-A)) := by rw [he, mul_one]
      _ = NormedSpace.exp (-A) := by rw [← mul_assoc, hU.1, one_mul]
  · intro hA
    exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hA

/-- Near zero, determinant one is exactly the trace-zero constraint. -/
theorem det_exp_eq_one_iff_of_trace_im (A : Matrix n n ℂ)
    (hlo : -Real.pi < (Matrix.trace A).im) (hhi : (Matrix.trace A).im ≤ Real.pi) :
    Matrix.det (NormedSpace.exp A) = 1 ↔ Matrix.trace A = 0 := by
  rw [det_matrix_exp]
  constructor
  · intro h
    apply Complex.exp_inj_of_neg_pi_lt_of_le_pi hlo hhi
      (by simpa using neg_neg_of_pos Real.pi_pos) (by simpa using Real.pi_pos.le)
    simpa using h
  · intro h
    simp [h]

/-- On some open Frobenius neighborhood of zero, exponential is injective and
its inverse image of the actual SU group is exactly su. -/
theorem exists_specialUnitary_exp_neighborhood :
    ∃ s : Set (Matrix n n ℂ), IsOpen s ∧ (0 : Matrix n n ℂ) ∈ s ∧
      s ⊆ matrixExpLocalHomeomorph.source ∧
      InjOn (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) s ∧
      ∀ A ∈ s, NormedSpace.exp A ∈ Matrix.specialUnitaryGroup n ℂ ↔
        A ∈ (specialUnitaryLieAlgebra : LieSubalgebra ℝ (Matrix n n ℂ)) := by
  obtain ⟨r, hr, hrs, hinj⟩ := exists_matrixExp_injective_ball (n := n)
  let s : Set (Matrix n n ℂ) := ball 0 r ∩
    (fun A : Matrix n n ℂ => (Matrix.trace A).im) ⁻¹' Ioo (-Real.pi) Real.pi
  have hc : Continuous (fun A : Matrix n n ℂ => (Matrix.trace A).im) :=
    Complex.continuous_im.comp continuous_id.matrix_trace
  refine ⟨s, isOpen_ball.inter (isOpen_Ioo.preimage hc), ?_,
    fun A hA => hrs hA.1, hinj.mono inter_subset_left, ?_⟩
  · constructor
    · simpa using hr
    · simp [Real.pi_pos]
  · intro A hA
    change (NormedSpace.exp A ∈ Matrix.unitaryGroup n ℂ ∧
      Matrix.det (NormedSpace.exp A) = 1) ↔ (star A = -A ∧ Matrix.trace A = 0)
    rw [exp_mem_unitary_iff_of_injective_ball hinj A hA.1,
      det_exp_eq_one_iff_of_trace_im A hA.2.1 hA.2.2.le]

end LogSobolev
