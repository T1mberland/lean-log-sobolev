import LogSobolev.Gaussian.LSI

/-! # Independent Gaussian LSI usage examples -/

open MeasureTheory ProbabilityTheory LogSobolev
open scoped ENNReal

/-- A user can apply the Euclidean theorem without referring to the port's
coordinate derivatives or its internal Sobolev predicate. -/
example {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hc : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    entropy (standardGaussian n) (fun x => (f x)^2) ≤
      2 * ∫ x, ‖fderiv ℝ f x‖^2 ∂standardGaussian n :=
  gaussian_entropy_sq_le_of_contDiff_of_hasCompactSupport hc hs

example (n : ℕ) : IsProbabilityMeasure (standardGaussian n) := inferInstance

/-- The zero-dimensional case is an actual probability space. -/
example (c : ℝ) : entropy (standardGaussian 0) (fun _ => c^2) = 0 :=
  entropy_const _ _

/-- A meaningful unbounded, nonconstant test function in the one-dimensional
C¹ extension: `f(x) = x`. -/
example : entropy (gaussianReal 0 1) (fun x : ℝ => x^2) ≤ 2 := by
  have hc : ContDiff ℝ 1 (id : ℝ → ℝ) := contDiff_id
  have hm : GaussianSobolevReal.MemW12GaussianReal id (gaussianReal 0 1) := by
    constructor
    · exact memLp_id_gaussianReal 2
    · simpa only [fderiv_id] using
        (memLp_const (ContinuousLinearMap.id ℝ ℝ) :
          MemLp (fun _ : ℝ => ContinuousLinearMap.id ℝ ℝ) 2 (gaussianReal 0 1))
  have h := GaussianSobolevReal.gaussian_logSobolev_W12_real hm differentiable_id
    (hc.continuous_fderiv one_ne_zero)
  simpa [GaussianPoincare.stdGaussianMeasure, GaussianPoincare.stdGaussian,
    ContinuousLinearMap.norm_id] using h

example : (id : ℝ → ℝ) 0 ≠ id 1 := by norm_num

/-- Coordinate sums use Euclidean, unnormalized energy. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : EuclideanSpace ℝ ι →L[ℝ] ℝ) :
    ∑ i, (L (EuclideanSpace.single i 1))^2 = ‖L‖^2 :=
  sum_sq_apply_single_eq_norm_sq L

/-- A concrete smooth bump in every Euclidean dimension; no moment hypotheses
are left to the caller. -/
example (n : ℕ) :
    entropy (standardGaussian n)
      (fun x => (GaussianSobolev.smoothCutoffR (n := n) 1 x)^2) ≤
    2 * ∫ x, ‖fderiv ℝ (GaussianSobolev.smoothCutoffR (n := n) 1) x‖^2
      ∂standardGaussian n :=
  gaussian_entropy_sq_le_of_contDiff_of_hasCompactSupport
    ((GaussianSobolev.smoothCutoffR_contDiff (by norm_num : (0 : ℝ) < 1)).of_le (by simp))
    (GaussianSobolev.smoothCutoffR_hasCompactSupport (by norm_num))

/-- The preceding bump is nonconstant already in dimension two. -/
example : GaussianSobolev.smoothCutoffR (n := 2) 1 0 ≠
    GaussianSobolev.smoothCutoffR (n := 2) 1 (EuclideanSpace.single (0 : Fin 2) 3) := by
  rw [GaussianSobolev.smoothCutoffR_eq_one_of_norm_le (by norm_num) (by simp),
    GaussianSobolev.smoothCutoffR_eq_zero_of_norm_ge (by norm_num) (by norm_num)]
  norm_num

/-- Full support upgrades nonconstancy to Gaussian almost-everywhere
nonconstancy, so the concrete test is not vacuous at the measure level. -/
example (c : ℝ) : ¬ GaussianSobolev.smoothCutoffR (n := 2) 1 =ᵐ[standardGaussian 2]
    (fun _ => c) := by
  intro h
  have he := (standardGaussian 2).eq_of_ae_eq h
    (GaussianSobolev.smoothCutoffR_contDiff (by norm_num : (0 : ℝ) < 1)).continuous
    continuous_const
  have h0 := congrFun he 0
  have h3 := congrFun he (EuclideanSpace.single (0 : Fin 2) 3)
  rw [GaussianSobolev.smoothCutoffR_eq_one_of_norm_le (by norm_num) (by simp)] at h0
  rw [GaussianSobolev.smoothCutoffR_eq_zero_of_norm_ge (by norm_num) (by norm_num)] at h3
  exact one_ne_zero (h0.trans h3.symm)
