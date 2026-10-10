import LogSobolev.Gaussian.Port.GaussianLSI.TensorizedGLSI
import LogSobolev.Gaussian.EuclideanEnergy
import LogSobolev.Geometry.LocalSlopeFDeriv

/-! # Gaussian logarithmic Sobolev inequality

The standard Gaussian on Euclidean space satisfies the dimension-free bound
`Ent(f²) ≤ 2 ∫ ‖Df‖²` for continuously differentiable functions with the
stated Gaussian moments. The analytic proof is ported from AI4SLT; this module
transports its coordinate formulation to the Euclidean norm and the shared
entropy API. No assertion about arbitrary Sobolev representatives is made.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LogSobolev

/-- Standard Gaussian probability measure on Euclidean `n`-space. -/
noncomputable abbrev standardGaussian (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  GaussianMeasure.stdGaussianE n

/-- Dimension-free Gaussian LSI for `C¹` functions. The derivative norm is the
operator norm for the **Euclidean** domain, equal to the Euclidean gradient
norm. The entropy integrability hypothesis prevents totalized-integral issues. -/
theorem gaussian_entropy_sq_le_of_contDiff {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hc : ContDiff ℝ 1 f)
    (hf : MemLp f 2 (standardGaussian n))
    (hd : MemLp (fun x => ‖fderiv ℝ f x‖) 2 (standardGaussian n))
    (hl : Integrable (fun x => (f x)^2 * Real.log ((f x)^2)) (standardGaussian n)) :
    entropy (standardGaussian n) (fun x => (f x)^2) ≤
      2 * ∫ x, ‖fderiv ℝ f x‖^2 ∂standardGaussian n := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let g : (Fin n → ℝ) → ℝ := f ∘ e.symm
  have hg : ContDiff ℝ 1 g := hc.comp e.symm.contDiff
  have hf_diff : Differentiable ℝ f := hc.differentiable (by norm_num)
  have hg_diff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hcoord (i : Fin n) (x : Fin n → ℝ) :
      GaussianLSI.partialDeriv i g x =
        fderiv ℝ f (e.symm x) (EuclideanSpace.single i 1) := by
    have h := (hf_diff (e.symm x)).hasFDerivAt.comp x e.symm.hasFDerivAt
    change (fderiv ℝ g x) (Pi.single i 1) = _
    rw [h.fderiv]
    rfl
  have hcont (i : Fin n) : Continuous (GaussianLSI.partialDeriv i g) := by
    change Continuous (fun x => GaussianLSI.partialDeriv i g x)
    simp_rw [hcoord]
    exact ((hc.continuous_fderiv one_ne_zero).comp e.symm.continuous).clm_apply continuous_const
  have hmem : GaussianLSI.MemW12GaussianPi n g (GaussianMeasure.stdGaussianPi n) := by
    refine ⟨hf.comp_of_map e.symm.continuous.measurable.aemeasurable, ?_⟩
    intro i
    apply (hd.comp_of_map e.symm.continuous.measurable.aemeasurable).mono'
      (hcont i).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simp only [Function.comp_apply, hcoord]
      simpa using (fderiv ℝ f (e.symm x)).le_opNorm (EuclideanSpace.single i 1)
  have hlog : Integrable (fun x => (g x)^2 * Real.log ((g x)^2))
      (GaussianMeasure.stdGaussianPi n) :=
    (integrable_map_measure hl.aestronglyMeasurable
      e.symm.continuous.measurable.aemeasurable).mp hl
  have hlsi := GaussianLSI.gaussian_logSobolev_W12_pi hmem hg_diff hcont hlog
  have henergy (x : Fin n → ℝ) :
      GaussianLSI.gradNormSq n g x = ‖fderiv ℝ f (e.symm x)‖^2 := by
    simp only [GaussianLSI.gradNormSq, hcoord]
    exact sum_sq_apply_single_eq_norm_sq _
  rw [show entropy (standardGaussian n) (fun x => (f x)^2) =
      entropy (GaussianMeasure.stdGaussianPi n) (fun x => (g x)^2) from
    entropy_map _ e.symm.continuous.measurable (hc.continuous.pow 2).aestronglyMeasurable]
  rw [GaussianMeasure.integral_stdGaussianE_eq]
  simpa only [henergy] using hlsi

/-- For compactly supported `C¹` functions, all moment assumptions follow
automatically. This statement includes every dimension, including zero. -/
theorem gaussian_entropy_sq_le_of_contDiff_of_hasCompactSupport {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hc : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    entropy (standardGaussian n) (fun x => (f x)^2) ≤
      2 * ∫ x, ‖fderiv ℝ f x‖^2 ∂standardGaussian n := by
  apply gaussian_entropy_sq_le_of_contDiff hc
  · exact hc.continuous.memLp_of_hasCompactSupport hs
  · exact (hc.continuous_fderiv one_ne_zero).norm.memLp_of_hasCompactSupport
      ((hs.fderiv (𝕜 := ℝ)).comp_left
        (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => ‖L‖) (by simp))
  · exact (Real.continuous_mul_log.comp (hc.continuous.pow 2)).integrable_of_hasCompactSupport
      (hs.comp_left (g := fun y : ℝ => y^2 * Real.log (y^2)) (by simp))

/-- The same `C¹` Gaussian bound in the slope-energy convention of `MetricLSI`.
This is a theorem for the stated test class, not yet the all-locally-Lipschitz
assertion `MetricLSI (standardGaussian n) 1`. -/
theorem gaussian_entropy_sq_le_slopeEnergy_of_contDiff {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hc : ContDiff ℝ 1 f)
    (hf : MemLp f 2 (standardGaussian n))
    (hd : MemLp (fun x => ‖fderiv ℝ f x‖) 2 (standardGaussian n))
    (hl : Integrable (fun x => (f x)^2 * Real.log ((f x)^2)) (standardGaussian n)) :
    ENNReal.ofReal (entropy (standardGaussian n) (fun x => (f x)^2)) ≤
      2 * slopeEnergy (standardGaussian n) f := by
  have h := ENNReal.ofReal_le_ofReal (gaussian_entropy_sq_le_of_contDiff hc hf hd hl)
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] at h
  exact h.trans (mul_le_mul_right
    (ofReal_integral_norm_fderiv_sq_le_slopeEnergy _ f hd.integrable_sq) 2)

end LogSobolev
