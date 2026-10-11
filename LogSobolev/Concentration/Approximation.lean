module

public import LogSobolev.Concentration.Herbst

@[expose] public section

/-! # Uniform approximation of centered sub-Gaussian observables

Uniform approximation controls the means and centered exponential moments.
This permits nonsmooth observables without an entropy continuity argument.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology NNReal

namespace LogSobolev

/-- Centered sub-Gaussian bounds pass to a uniformly approximated observable.
The approximation errors tend to zero; no differentiability or compactness is
required. Integrability hypotheses are explicit for this analytic transfer. -/
theorem hasSubgaussianMGF_of_uniform_approximation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {g : ℕ → Ω → ℝ}
    {c : ℝ≥0} {δ : ℕ → ℝ} (hf : Integrable f μ)
    (hg : ∀ j, Integrable (g j) μ)
    (hint : ∀ t : ℝ, Integrable (fun x => exp (t * f x)) μ)
    (hsub : ∀ j, HasSubgaussianMGF (fun x => g j x - ∫ y, g j y ∂μ) c μ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (happrox : ∀ j x, |f x - g j x| ≤ δ j) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂μ) c μ := by
  have hmean (j : ℕ) : |(∫ x, f x ∂μ) - ∫ x, g j x ∂μ| ≤ δ j := by
    rw [← integral_sub hf (hg j)]
    have hh := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => f x - g j x)
      (C := δ j) (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using happrox j x)
    simpa [Real.norm_eq_abs] using hh
  have hcenter (j : ℕ) (x : Ω) :
      |(f x - ∫ y, f y ∂μ) - (g j x - ∫ y, g j y ∂μ)| ≤ 2 * δ j := by
    have ha := abs_sub (f x - g j x) ((∫ y, f y ∂μ) - ∫ y, g j y ∂μ)
    have he : (f x - ∫ y, f y ∂μ) - (g j x - ∫ y, g j y ∂μ) =
        (f x - g j x) - ((∫ y, f y ∂μ) - ∫ y, g j y ∂μ) := by ring
    rw [he]
    linarith [happrox j x, hmean j]
  have hi (t : ℝ) : Integrable (fun x => exp (t * (f x - ∫ y, f y ∂μ))) μ := by
    have hh := (hint t).mul_const (exp (-t * ∫ y, f y ∂μ))
    convert hh using 1
    funext x
    rw [← exp_add]
    congr 1
    ring
  refine ⟨hi, ?_⟩
  intro t
  have hb (j : ℕ) : mgf (fun x => f x - ∫ y, f y ∂μ) μ t ≤
      exp (2 * |t| * δ j) * exp ((c : ℝ) * t ^ 2 / 2) := by
    calc
      _ ≤ exp (2 * |t| * δ j) * mgf (fun x => g j x - ∫ y, g j y ∂μ) μ t := by
        simp only [mgf]
        rw [← integral_const_mul]
        apply integral_mono (hi t) ((hsub j).integrable_exp_mul t |>.const_mul _)
        intro x
        dsimp only
        rw [← exp_add]
        apply exp_le_exp.mpr
        have hh : t * ((f x - ∫ y, f y ∂μ) - (g j x - ∫ y, g j y ∂μ)) ≤
            |t| * (2 * δ j) := by
          calc
            _ ≤ |t * ((f x - ∫ y, f y ∂μ) - (g j x - ∫ y, g j y ∂μ))| := le_abs_self _
            _ = _ := abs_mul _ _
            _ ≤ _ := mul_le_mul_of_nonneg_left (hcenter j x) (abs_nonneg _)
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsub j |>.mgf_le t) (exp_pos _).le
  have ht : Tendsto (fun j => exp (2 * |t| * δ j) * exp ((c : ℝ) * t ^ 2 / 2))
      atTop (𝓝 (exp ((c : ℝ) * t ^ 2 / 2))) := by
    simpa using ((Real.continuous_exp.tendsto (2 * |t| * 0)).comp
      (hδ.const_mul (2 * |t|))).mul_const (exp ((c : ℝ) * t ^ 2 / 2))
  exact ge_of_tendsto ht (Eventually.of_forall hb)

end LogSobolev
