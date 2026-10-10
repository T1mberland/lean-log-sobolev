import LogSobolev.Unitary.SpecialUnitaryPolynomialNorm
import Mathlib.Analysis.SpecialFunctions.Exponential
import LogSobolev.Measure.CompactDifferentiation
import LogSobolev.Unitary.SpecialUnitaryHaarCalculus

/-! # Constructed heat evolution on every finite-degree SU polynomial space

The exponential of the continuous restricted generator gives an actual heat
evolution for every polynomial observable. Finite dimensionality provides
completeness. Initial values, the semigroup law, the actual heat equation, joint
continuity, and preservation of bounds are proved. Extension beyond polynomial
observables and equilibrium convergence remain separate obligations.
-/

open Matrix
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

/-- Heat evolution constructed by exponentiating the actual restricted generator. -/
noncomputable def specialUnitaryPolynomialHeat
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) (t : ℝ) : specialUnitaryPolynomialSpace (n := n) d :=
  NormedSpace.exp (t • specialUnitaryPolynomialLaplacianCLM b d) f

@[simp] theorem specialUnitaryPolynomialHeat_zero
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) :
    specialUnitaryPolynomialHeat b d f 0 = f := by
  simp [specialUnitaryPolynomialHeat]

/-- The constructed polynomial heat evolution has the semigroup law. -/
theorem specialUnitaryPolynomialHeat_add
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) (s t : ℝ) :
    specialUnitaryPolynomialHeat b d f (s + t) =
      specialUnitaryPolynomialHeat b d (specialUnitaryPolynomialHeat b d f t) s := by
  unfold specialUnitaryPolynomialHeat
  rw [add_smul, NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    (((Commute.refl (specialUnitaryPolynomialLaplacianCLM b d)).smul_left s).smul_right t)
    (by simp [NormedSpace.expSeries_radius_eq_top])
    (by simp [NormedSpace.expSeries_radius_eq_top])]
  rfl

/-- The exponential solves the actual finite-dimensional generator ODE. -/
theorem specialUnitaryPolynomialHeat_hasDerivAt
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) (t : ℝ) :
    HasDerivAt (specialUnitaryPolynomialHeat b d f)
      (specialUnitaryPolynomialLaplacianCLM b d (specialUnitaryPolynomialHeat b d f t)) t := by
  exact (ContinuousLinearMap.apply ℝ (specialUnitaryPolynomialSpace (n := n) d) f).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' (specialUnitaryPolynomialLaplacianCLM b d) t)

/-- Pointwise, the constructed evolution satisfies the original SU heat equation. -/
theorem specialUnitaryPolynomialHeat_hasDerivAt_apply
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) (t : ℝ)
    (U : Matrix.specialUnitaryGroup n ℂ) :
    HasDerivAt (fun r => (specialUnitaryPolynomialHeat b d f r).val U)
      (specialUnitaryLaplacian b (specialUnitaryPolynomialHeat b d f t).val U) t := by
  have h := (specialUnitaryPolynomialEval d U).hasFDerivAt.comp_hasDerivAt t
    (specialUnitaryPolynomialHeat_hasDerivAt b d f t)
  change HasDerivAt (fun r => (specialUnitaryPolynomialHeat b d f r).val U)
    ((specialUnitaryPolynomialLaplacian b d (specialUnitaryPolynomialHeat b d f t)).val U) t at h
  rw [specialUnitaryPolynomialLaplacian_apply] at h
  exact h

/-- Polynomial heat solutions are jointly continuous in time and the actual SU matrix. -/
theorem specialUnitaryPolynomialHeat_continuous
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) :
    Continuous (fun p : ℝ × Matrix.specialUnitaryGroup n ℂ =>
      (specialUnitaryPolynomialHeat b d f p.1).val p.2) := by
  have ht : Continuous (specialUnitaryPolynomialHeat b d f) :=
    continuous_iff_continuousAt.mpr fun t => (specialUnitaryPolynomialHeat_hasDerivAt b d f t).continuousAt
  have hc := (specialUnitaryPolynomialToContinuousCLM d).continuous.comp ht
  exact continuous_eval.comp ((hc.comp continuous_fst).prodMk continuous_snd)

/-- Every initial lower bound is preserved by the constructed polynomial heat evolution. -/
theorem specialUnitaryPolynomialHeat_lower_bound
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) {a T : ℝ} (hT : 0 ≤ T)
    (hinit : ∀ U, a ≤ f.val U) :
    ∀ U, a ≤ (specialUnitaryPolynomialHeat b d f T).val U := by
  apply specialUnitary_heat_lower_bound b (F := fun t U => (specialUnitaryPolynomialHeat b d f t).val U) hT (specialUnitaryPolynomialHeat_continuous b d f)
    (fun t _ => (specialUnitaryPolynomialHeat b d f t).val.contMDiff)
    (fun t _ U => specialUnitaryPolynomialHeat_hasDerivAt_apply b d f t U)
    (fun _ _ => rfl)
  simpa only [specialUnitaryPolynomialHeat_zero] using hinit

/-- Every initial upper bound is preserved by the constructed polynomial heat evolution. -/
theorem specialUnitaryPolynomialHeat_upper_bound
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) {a T : ℝ} (hT : 0 ≤ T)
    (hinit : ∀ U, f.val U ≤ a) :
    ∀ U, (specialUnitaryPolynomialHeat b d f T).val U ≤ a := by
  apply specialUnitary_heat_upper_bound b (F := fun t U => (specialUnitaryPolynomialHeat b d f t).val U) hT (specialUnitaryPolynomialHeat_continuous b d f)
    (fun t _ => (specialUnitaryPolynomialHeat b d f t).val.contMDiff)
    (fun t _ U => specialUnitaryPolynomialHeat_hasDerivAt_apply b d f t U)
    (fun _ _ => rfl)
  simpa only [specialUnitaryPolynomialHeat_zero] using hinit

/-- Strictly positive polynomial initial data remain strictly positive at all forward times. -/
theorem specialUnitaryPolynomialHeat_pos
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) {T : ℝ} (hT : 0 ≤ T)
    (hinit : ∀ U, 0 < f.val U) : ∀ U, 0 < (specialUnitaryPolynomialHeat b d f T).val U := by
  obtain ⟨V, _, hm⟩ := isCompact_univ.exists_isMinOn
    ⟨(1 : Matrix.specialUnitaryGroup n ℂ), Set.mem_univ _⟩ f.val.contMDiff.continuous.continuousOn
  have hb := specialUnitaryPolynomialHeat_lower_bound b d f hT
    (fun U => isMinOn_iff.mp hm U (Set.mem_univ U))
  exact fun U => lt_of_lt_of_le (hinit V) (hb U)

/-- Forward heat evolution contracts the actual supremum norm. -/
theorem specialUnitaryPolynomialHeat_norm_le
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) {T : ℝ} (hT : 0 ≤ T) :
    ‖specialUnitaryPolynomialHeat b d f T‖ ≤ ‖f‖ := by
  change ‖specialUnitaryPolynomialToContinuous d (specialUnitaryPolynomialHeat b d f T)‖ ≤
    ‖specialUnitaryPolynomialToContinuous d f‖
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro U
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨specialUnitaryPolynomialHeat_lower_bound b d f hT
    (fun V => (specialUnitaryPolynomialToContinuous d f).neg_norm_le_apply V) U,
    specialUnitaryPolynomialHeat_upper_bound b d f hT
    (fun V => (specialUnitaryPolynomialToContinuous d f).apply_le_norm V) U⟩

/-- The actual generator commutes with its constructed exponential. -/
theorem specialUnitaryPolynomialHeat_commute
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) (t : ℝ) :
    specialUnitaryPolynomialLaplacianCLM b d (specialUnitaryPolynomialHeat b d f t) =
      specialUnitaryPolynomialHeat b d (specialUnitaryPolynomialLaplacianCLM b d f) t := by
  have h := (ContinuousLinearMap.apply ℝ (specialUnitaryPolynomialSpace (n := n) d) f).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const (specialUnitaryPolynomialLaplacianCLM b d) t)
  exact (specialUnitaryPolynomialHeat_hasDerivAt b d f t).unique h

/-- The Laplacian of a polynomial heat solution is jointly continuous. -/
theorem specialUnitaryPolynomialHeat_laplacian_continuous
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) :
    Continuous (fun p : ℝ × Matrix.specialUnitaryGroup n ℂ =>
      specialUnitaryLaplacian b (specialUnitaryPolynomialHeat b d f p.1).val p.2) := by
  have he (t : ℝ) (U : Matrix.specialUnitaryGroup n ℂ) :
      specialUnitaryLaplacian b (specialUnitaryPolynomialHeat b d f t).val U =
        (specialUnitaryPolynomialHeat b d (specialUnitaryPolynomialLaplacianCLM b d f) t).val U := by
    rw [← specialUnitaryPolynomialLaplacian_apply]
    exact congrArg (fun g : specialUnitaryPolynomialSpace (n := n) d => g.val U)
      (specialUnitaryPolynomialHeat_commute b d f t)
  simp_rw [he]
  exact specialUnitaryPolynomialHeat_continuous b d _

/-- The constructed polynomial heat evolution preserves normalized Haar mass. -/
theorem specialUnitaryPolynomialHeat_integral
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) (t : ℝ) :
    (∫ U, (specialUnitaryPolynomialHeat b d f t).val U ∂specialUnitaryHaar n) =
      ∫ U, f.val U ∂specialUnitaryHaar n := by
  have hd (r : ℝ) : HasDerivAt
      (fun s => ∫ U, (specialUnitaryPolynomialHeat b d f s).val U ∂specialUnitaryHaar n) 0 r := by
    have h := hasDerivAt_integral_of_compact (μ := specialUnitaryHaar n) (s := Set.univ)
      (F := fun t U => (specialUnitaryPolynomialHeat b d f t).val U)
      (Q := fun t U => specialUnitaryLaplacian b (specialUnitaryPolynomialHeat b d f t).val U)
      (specialUnitaryPolynomialHeat_continuous b d f)
      (specialUnitaryPolynomialHeat_laplacian_continuous b d f)
      (fun s _ U => specialUnitaryPolynomialHeat_hasDerivAt_apply b d f s U) r (by simp)
    rw [specialUnitary_integral_laplacian_eq_zero b
      (specialUnitaryPolynomialHeat b d f r).val.contMDiff] at h
    exact h
  have h := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) t 0
  simpa only [specialUnitaryPolynomialHeat_zero] using h

end LogSobolev
