/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
The exponential domination proof is adapted from StatsMLlib commit
75611ba335ee4ff2fb8b09938f6319d2cbf3d804, Gaussian/LipschitzConcentration.lean.
Modifications: Euclidean domain, shared measure-independent Herbst argument,
and all dimensions and nonnegative Lipschitz constants.
-/
module

public import LogSobolev.Concentration.Metric
public import LogSobolev.Concentration.Approximation
public import LogSobolev.Gaussian.LSI
public import LogSobolev.Gaussian.Port.GaussianSobolevDense.LipschitzMollification

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Dimension-free Gaussian concentration in Euclidean geometry

Exponential moments follow from linear growth and independent Gaussian
coordinates. The shared Herbst argument applies first to C¹ observables;
Lipschitz mollification then removes the differentiability assumption.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

namespace LogSobolev

/-- All exponential moments of a Euclidean Lipschitz Gaussian observable exist.
The proof includes dimension zero and constant functions. -/
theorem gaussian_integrable_exp_mul {n : ℕ} {K : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LipschitzWith K f) (t : ℝ) :
    Integrable (fun x => exp (t * f x)) (standardGaussian n) := by
  classical
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hn (x : EuclideanSpace ℝ (Fin n)) : ‖x‖ ≤ ∑ i, |x i| := by
    have hx : (∑ i, EuclideanSpace.single i (x i)) = x := by
      ext j
      simp
    calc
      ‖x‖ = ‖∑ i, EuclideanSpace.single i (x i)‖ := congrArg norm hx.symm
      _ ≤ ∑ i, ‖EuclideanSpace.single i (x i)‖ := norm_sum_le _ _
      _ = _ := by simp [EuclideanSpace.single, Real.norm_eq_abs]
  have hg (x : EuclideanSpace ℝ (Fin n)) : |f x| ≤ |f 0| + (K : ℝ) * ∑ i, |x i| := by
    have hl := hf.dist_le_mul x 0
    rw [Real.dist_eq, dist_zero_right] at hl
    have ha := abs_add_le (f x - f 0) (f 0)
    have hb := mul_le_mul_of_nonneg_left (hn x) K.coe_nonneg
    rw [sub_add_cancel] at ha
    linarith
  have hi (c : ℝ) : Integrable (fun x : Fin n → ℝ => exp (c * ∑ i, |x i|))
      (GaussianMeasure.stdGaussianPi n) := by
    simp_rw [Finset.mul_sum, Real.exp_sum]
    unfold GaussianMeasure.stdGaussianPi
    apply Integrable.fintype_prod (f := fun (_ : Fin n) (y : ℝ) => exp (c * |y|))
    intro i
    exact integrable_exp_mul_abs (integrable_exp_mul_gaussianReal c)
      (integrable_exp_mul_gaussianReal (-c))
  have hb := (hi (|t| * K)).const_mul (exp (|t| * |f 0|))
  have hp : Integrable (fun x : Fin n → ℝ => exp (t * f (e.symm x)))
      (GaussianMeasure.stdGaussianPi n) := by
    have hm : AEStronglyMeasurable (fun x : Fin n → ℝ => exp (t * f (e.symm x)))
        (GaussianMeasure.stdGaussianPi n) :=
      (Real.continuous_exp.comp
        (continuous_const.mul (hf.continuous.comp e.symm.continuous))).aestronglyMeasurable
    apply hb.mono' hm
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_exp, ← exp_add]
    apply exp_le_exp.mpr
    calc
      t * f (e.symm x) ≤ |t| * |f (e.symm x)| := by
        simpa only [abs_mul] using le_abs_self (t * f (e.symm x))
      _ ≤ |t| * (|f 0| + (K : ℝ) * ∑ i, |(e.symm x) i|) :=
        mul_le_mul_of_nonneg_left (hg _) (abs_nonneg _)
      _ = _ := by simp [e, EuclideanSpace.equiv]; ring
  exact (integrable_map_measure
    (Real.continuous_exp.comp (continuous_const.mul hf.continuous)).aestronglyMeasurable
    e.symm.continuous.measurable.aemeasurable).2 hp

/-- Gaussian Herbst bound for C¹ globally Lipschitz functions. All moment and
entropy hypotheses of Gaussian LSI are proved here. -/
theorem gaussian_hasSubgaussianMGF_of_contDiff {n : ℕ} {K : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hc : ContDiff ℝ 1 f)
    (hf : LipschitzWith K f) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂standardGaussian n)
      (K ^ 2) (standardGaussian n) := by
  have hint := gaussian_integrable_exp_mul hf
  apply hasSubgaussianMGF_of_entropy_exp_bound hint
  intro t
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun x => exp (t / 2 * f x)
  have hgc : ContDiff ℝ 1 g := contDiff_exp.comp (contDiff_const.mul hc)
  have hsq (x) : g x ^ 2 = exp (t * f x) := by
    dsimp [g]
    rw [sq, ← exp_add]
    congr 1
    ring
  have hgm : MemLp g 2 (standardGaussian n) := by
    apply (memLp_two_iff_integrable_sq hgc.continuous.aestronglyMeasurable).2
    simpa only [hsq] using hint t
  have hdb (x) : ‖fderiv ℝ g x‖ ≤ |t / 2| * (K : ℝ) * g x := by
    have hd := (((hc.differentiable (by norm_num) x).hasFDerivAt.const_mul
      (t / 2)).exp).fderiv
    change ‖fderiv ℝ (fun x => exp (t / 2 * f x)) x‖ ≤ _
    rw [hd]
    simp only [norm_smul, Real.norm_eq_abs, abs_exp]
    calc
      _ ≤ exp (t / 2 * f x) * (|t / 2| * (K : ℝ)) := by
        gcongr
        exact norm_fderiv_le_of_lipschitz ℝ hf
      _ = _ := by dsimp [g]; ring
  have hdm : MemLp (fun x => ‖fderiv ℝ g x‖) 2 (standardGaussian n) := by
    apply (hgm.const_mul (|t / 2| * (K : ℝ))).mono'
      (hgc.continuous_fderiv one_ne_zero).norm.aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    simpa only [norm_norm] using hdb x
  have hs : integrableExpSet f (standardGaussian n) = Set.univ :=
    Set.ext fun s => by simp [integrableExpSet, hint]
  have hl : Integrable (fun x => g x ^ 2 * log (g x ^ 2)) (standardGaussian n) := by
    simp only [hsq, log_exp]
    have hi := (integrable_pow_mul_exp_of_mem_interior_integrableExpSet
      (show t ∈ interior (integrableExpSet f (standardGaussian n)) by simp [hs]) 1).const_mul t
    convert hi using 1
    funext x
    simp only [pow_one]
    ring
  have henergy : (∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂standardGaussian n) ≤
      (t ^ 2 * (K : ℝ)^2 / 4) * mgf f (standardGaussian n) t := by
    rw [mgf, ← integral_const_mul]
    apply integral_mono hdm.integrable_sq ((hint t).const_mul _)
    intro x
    calc
      _ ≤ (|t / 2| * (K : ℝ) * g x) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hdb x) 2
      _ = _ := by rw [mul_pow, mul_pow, sq_abs, div_pow, hsq]; ring
  have hh := (gaussian_entropy_sq_le_of_contDiff hgc hgm hdm hl).trans
    (mul_le_mul_of_nonneg_left henergy (by norm_num : (0 : ℝ) ≤ 2))
  simpa only [hsq, NNReal.coe_pow] using (show entropy (standardGaussian n) (fun x => g x ^ 2) ≤
      ((K : ℝ)^2 * t^2 / 2) * mgf f (standardGaussian n) t by nlinarith [hh])

/-- Every globally Euclidean Lipschitz Gaussian observable is integrable. -/
theorem gaussian_integrable_of_lipschitz {n : ℕ} {K : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LipschitzWith K f) :
    Integrable f (standardGaussian n) := by
  apply integrable_of_mem_interior_integrableExpSet
  have hs : integrableExpSet f (standardGaussian n) = Set.univ :=
    Set.ext fun t => by simp [integrableExpSet, gaussian_integrable_exp_mul hf]
  simp [hs]

/-- Dimension-free Gaussian Herbst bound for every globally Lipschitz real
function in Euclidean geometry, including nonsmooth functions, dimension zero,
and Lipschitz constant zero. No moment assumptions remain for callers. -/
theorem gaussian_hasSubgaussianMGF {n : ℕ} {K : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LipschitzWith K f) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂standardGaussian n)
      (K ^ 2) (standardGaussian n) := by
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  let g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun j => GaussianSobolev.mollify (ε j) f
  have hgl (j : ℕ) : LipschitzWith K (g j) :=
    GaussianSobolev.mollify_lipschitzWith (hε j) hf
  apply hasSubgaussianMGF_of_uniform_approximation (g := g)
    (δ := fun j => (K : ℝ) * ε j * Real.sqrt n)
    (gaussian_integrable_of_lipschitz hf)
    (fun j => gaussian_integrable_of_lipschitz (hgl j))
    (gaussian_integrable_exp_mul hf)
  · intro j
    exact gaussian_hasSubgaussianMGF_of_contDiff
      ((GaussianSobolev.mollify_smooth_of_lipschitz hf (hε j)).of_le (by norm_num)) (hgl j)
  · simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (K : ℝ) |>.mul_const (Real.sqrt n)
  · intro j x
    simpa only [Real.dist_eq, abs_sub_comm] using
      GaussianSobolev.mollify_dist_le_of_lipschitz' (hε j) hf x

/-- Dimension-free upper Gaussian tail: `P(f - E f ≥ r) ≤ exp(-r²/(2 K²))`.
No smoothness or additional integrability hypotheses are required. -/
theorem gaussian_measure_ge_le {n : ℕ} {K : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LipschitzWith K f)
    {r : ℝ} (hr : 0 ≤ r) :
    (standardGaussian n).real {x | r ≤ f x - ∫ y, f y ∂standardGaussian n} ≤
      exp (-r ^ 2 / (2 * (K : ℝ) ^ 2)) := by
  simpa only [NNReal.coe_pow] using (gaussian_hasSubgaussianMGF hf).measure_ge_le hr

/-- Dimension-free lower Gaussian tail. -/
theorem gaussian_measure_le_le {n : ℕ} {K : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LipschitzWith K f)
    {r : ℝ} (hr : 0 ≤ r) :
    (standardGaussian n).real {x | r ≤ (∫ y, f y ∂standardGaussian n) - f x} ≤
      exp (-r ^ 2 / (2 * (K : ℝ) ^ 2)) := by
  simpa only [NNReal.coe_pow, Pi.neg_apply, neg_sub] using
    (gaussian_hasSubgaussianMGF hf).neg.measure_ge_le hr

/-- Dimension-free two-sided Gaussian concentration for all globally Euclidean
Lipschitz real functions. This includes the nonsmooth Euclidean norm. -/
theorem gaussian_measure_abs_ge_le {n : ℕ} {K : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LipschitzWith K f)
    {r : ℝ} (hr : 0 ≤ r) :
    (standardGaussian n).real {x | r ≤ |f x - ∫ y, f y ∂standardGaussian n|} ≤
      2 * exp (-r ^ 2 / (2 * (K : ℝ) ^ 2)) := by
  simpa only [NNReal.coe_pow] using
    measure_abs_ge_le_of_hasSubgaussianMGF (gaussian_hasSubgaussianMGF hf) hr

end LogSobolev
