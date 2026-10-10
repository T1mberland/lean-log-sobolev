import LogSobolev.Unitary.SpecialUnitaryPolynomialDissipation

/-! # Continuous integral functionals on SU polynomial spaces

Evaluation and invariant differentiation are continuous on each finite-degree
space. Compact integration therefore makes Haar mass, integrated carré du
champ, and entropy continuous in the actual supremum norm on that space.
-/

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

/-- Joint evaluation after a continuous linear operator on polynomial observables. -/
theorem specialUnitaryPolynomial_clm_eval_continuous (d : ℕ)
    (A : specialUnitaryPolynomialSpace (n := n) d →L[ℝ]
      specialUnitaryPolynomialSpace (n := n) d) :
    Continuous (fun p : specialUnitaryPolynomialSpace (n := n) d × Matrix.specialUnitaryGroup n ℂ =>
      (A p.1).val p.2) :=
  continuous_eval.comp
    ((((specialUnitaryPolynomialToContinuousCLM d).continuous.comp A.continuous).comp
      continuous_fst).prodMk continuous_snd)

/-- Normalized Haar mass is continuous on each finite-degree polynomial space. -/
theorem specialUnitaryPolynomial_integral_continuous (d : ℕ) :
    Continuous (fun f : specialUnitaryPolynomialSpace (n := n) d =>
      ∫ U, f.val U ∂specialUnitaryHaar n) := by
  have h := continuous_parametric_integral_of_continuous (μ := specialUnitaryHaar n)
    (f := fun f : specialUnitaryPolynomialSpace (n := n) d => fun U => f.val U)
    (specialUnitaryPolynomial_clm_eval_continuous d (ContinuousLinearMap.id ℝ _)) isCompact_univ
  simpa only [Measure.restrict_univ] using h

/-- Integrated actual carré du champ is continuous on each finite-degree space. -/
theorem specialUnitaryPolynomial_energy_continuous
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ) :
    Continuous (fun f : specialUnitaryPolynomialSpace (n := n) d =>
      ∫ U, specialUnitaryGamma b f.val f.val U ∂specialUnitaryHaar n) := by
  have hG : Continuous (fun p : specialUnitaryPolynomialSpace (n := n) d × Matrix.specialUnitaryGroup n ℂ =>
      specialUnitaryGamma b p.1.val p.1.val p.2) := by
    have he (f : specialUnitaryPolynomialSpace (n := n) d) (U : Matrix.specialUnitaryGroup n ℂ) :=
      specialUnitaryGamma_eq b f.val.contMDiff f.val.contMDiff U
    simp_rw [he]
    apply continuous_finset_sum
    intro i _
    have hD := specialUnitaryPolynomial_clm_eval_continuous d (specialUnitaryPolynomialDerivCLM (b i) d)
    exact hD.mul hD
  have h := continuous_parametric_integral_of_continuous (μ := specialUnitaryHaar n)
    (f := fun f : specialUnitaryPolynomialSpace (n := n) d => fun U => specialUnitaryGamma b f.val f.val U)
    hG isCompact_univ
  simpa only [Measure.restrict_univ] using h

/-- Entropy is continuous on each finite-degree polynomial space, including at zeros. -/
theorem specialUnitaryPolynomial_entropy_continuous (d : ℕ) :
    Continuous (fun f : specialUnitaryPolynomialSpace (n := n) d =>
      entropy (specialUnitaryHaar n) f.val) := by
  have hF := specialUnitaryPolynomial_clm_eval_continuous (n := n) d (ContinuousLinearMap.id ℝ _)
  have h := continuous_parametric_integral_of_continuous (μ := specialUnitaryHaar n)
    (f := fun f : specialUnitaryPolynomialSpace (n := n) d => fun U => f.val U * Real.log (f.val U))
    (Real.continuous_mul_log.comp hF) isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h.sub (Real.continuous_mul_log.comp (specialUnitaryPolynomial_integral_continuous d))

/-- Constant observables belong to every polynomial degree bound. -/
theorem one_mem_specialUnitaryPolynomialSpace (d : ℕ) :
    (1 : specialUnitarySmoothFunctions n) ∈ specialUnitaryPolynomialSpace d := by
  apply specialUnitaryPolynomialSpace_mono (Nat.zero_le d)
  change (1 : specialUnitarySmoothFunctions n) ∈ specialUnitaryAffineSpace ^ 0
  rw [pow_zero (specialUnitaryAffineSpace (n := n))]
  exact Submodule.mem_one.mpr ⟨1, map_one _⟩

/-- A constant, represented inside the actual polynomial space. -/
noncomputable def specialUnitaryPolynomialConst (d : ℕ) (c : ℝ) :
    specialUnitaryPolynomialSpace (n := n) d :=
  ⟨c • 1, (specialUnitaryPolynomialSpace d).smul_mem c (one_mem_specialUnitaryPolynomialSpace d)⟩

@[simp] theorem specialUnitaryPolynomialConst_apply (d : ℕ) (c : ℝ)
    (U : Matrix.specialUnitaryGroup n ℂ) :
    (specialUnitaryPolynomialConst (n := n) d c).val U = c := by
  change c * 1 = c
  exact mul_one c

/-- The scalar-to-constant-polynomial map is continuous in the uniform norm. -/
theorem specialUnitaryPolynomialConst_continuous (d : ℕ) :
    Continuous (specialUnitaryPolynomialConst (n := n) d) := by
  change Continuous (fun c : ℝ => c •
    (⟨1, one_mem_specialUnitaryPolynomialSpace d⟩ : specialUnitaryPolynomialSpace (n := n) d))
  exact continuous_id.smul continuous_const

end LogSobolev
