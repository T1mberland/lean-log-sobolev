/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
The ratio lemma is adapted from StatsMLlib 75611ba335ee4ff2fb8b09938f6319d2cbf3d804,
StatsMLlib/Probability/Gaussian/LipschitzConcentration.lean.
The measure-independent Herbst theorem and sub-Gaussian interface are added here.
-/
module

public import LogSobolev.Measure.Entropy
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! # The Herbst argument on a probability space

An exponential entropy bound implies a centered sub-Gaussian MGF bound.
All exponential moments are assumed explicitly in this abstract analytic lemma;
applications establish them. Constants use `Ent(f²) ≤ 2C ∫ |∇f|²`, giving
variance proxy `C L²` for an `L`-Lipschitz observable.
-/

open MeasureTheory ProbabilityTheory Filter Real
open scoped Topology ENNReal NNReal

namespace LogSobolev

/-- A differential inequality controls the ratio at positive times. -/
lemma herbst_ratio_nonpos (φ : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hφ_zero : φ 0 = 0)
    (hφ_deriv_zero : deriv φ 0 = 0)
    (hφ_diff : ∀ x, DifferentiableAt ℝ φ x)
    (h_diff_ineq : ∀ s, s ≠ 0 → s * deriv φ s - φ s ≤ 0) :
    φ t / t ≤ 0 := by
  by_contra h_contra
  push Not at h_contra
  -- If φ(t)/t > 0, we derive a contradiction
  have h_ratio_diff : ∀ x, x ∈ Set.Ioo (0 : ℝ) t → DifferentiableAt ℝ (fun s => φ s / s) x := by
    intro x hx
    apply DifferentiableAt.div (hφ_diff x) differentiableAt_id (ne_of_gt hx.1)
  have h_mvt : AntitoneOn (fun s => φ s / s) (Set.Ioo 0 t) :=
    antitoneOn_of_deriv_nonpos (convex_Ioo 0 t)
      (by
        apply ContinuousOn.div
        · apply continuousOn_of_forall_continuousAt
          intro x _
          exact (hφ_diff x).continuousAt
        · exact continuous_id.continuousOn
        · intro x hx; exact ne_of_gt hx.1)
      (by
        intro x hx
        rw [interior_Ioo] at hx
        apply (h_ratio_diff x hx).differentiableWithinAt)
      (by
        intro x hx
        simp only [interior_Ioo, Set.mem_Ioo] at hx
        have hx_pos : 0 < x := hx.1
        have hx_ne : x ≠ 0 := ne_of_gt hx_pos
        -- Compute derivative: d/dx(φ(x)/x) = (x*φ'(x) - φ(x))/x²
        have h_deriv_ratio : deriv (fun s => φ s / s) x =
            (x * deriv φ x - φ x) / x^2 := by
          have hf_eq : (fun s => φ s / s) = (fun s => φ s * s⁻¹) := by
            ext s; ring
          rw [hf_eq]
          have h1 : deriv (fun s => φ s * s⁻¹) x =
              deriv φ x * x⁻¹ + φ x * deriv (·⁻¹) x := by
            apply deriv_mul (hφ_diff x)
            exact differentiableAt_inv hx_ne
          rw [h1, deriv_inv]
          field_simp
          ring
        rw [h_deriv_ratio]
        have h3 := h_diff_ineq x hx_ne
        have hx_sq_pos : 0 < x^2 := sq_pos_of_pos hx_pos
        apply div_nonpos_of_nonpos_of_nonneg h3 (le_of_lt hx_sq_pos))
  -- Compute limit as s → 0+
  have h_limit : Filter.Tendsto (fun s => φ s / s) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h_lhopital : Filter.Tendsto (fun s => φ s / s) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (deriv φ 0)) := by
      have h_slope := (hφ_diff 0).hasDerivAt.tendsto_slope_zero_right
      simp only [zero_add, hφ_zero, sub_zero, smul_eq_mul, inv_mul_eq_div] at h_slope
      exact h_slope
    rw [hφ_deriv_zero] at h_lhopital
    exact h_lhopital
  -- The function φ(s)/s approaches 0 as s → 0+ and is decreasing for s > 0
  have h_mono : ∀ s, s ∈ Set.Ioo 0 t → φ s / s ≥ φ t / t := fun s hs => by
    have h_ratio_cont : ContinuousAt (fun x => φ x / x) t :=
      ContinuousAt.div (hφ_diff t).continuousAt continuousAt_id (ne_of_gt ht)
    have h_tendsto : Filter.Tendsto (fun y => φ y / y) (nhdsWithin t (Set.Iio t)) (nhds (φ t / t)) :=
      h_ratio_cont.tendsto.mono_left nhdsWithin_le_nhds
    have : (nhdsWithin t (Set.Iio t)).NeBot := inferInstance
    apply le_of_tendsto h_tendsto
    filter_upwards [Ioo_mem_nhdsLT hs.2] with y hy
    exact h_mvt hs ⟨lt_trans hs.1 hy.1, hy.2⟩ (le_of_lt hy.1)
  -- Derive contradiction
  have h_eps : φ t / t / 2 > 0 := by linarith
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := Metric.tendsto_nhdsWithin_nhds.mp h_limit (φ t / t / 2) h_eps
  let s := min (t / 2) (δ / 2)
  have hs_pos : 0 < s := lt_min (by linarith) (by linarith)
  have hs_lt_t : s < t := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs_lt_δ : s < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hs_in : s ∈ Set.Ioo 0 t := ⟨hs_pos, hs_lt_t⟩
  have h4 := h_mono s hs_in
  have hs_mem : s ∈ Set.Ioi 0 := hs_pos
  have hs_dist : dist s 0 < δ := by simp [abs_of_pos hs_pos, hs_lt_δ]
  have h5 := hδ_bound hs_mem hs_dist
  simp only [Real.dist_eq, sub_zero] at h5
  have h9 : |φ s / s| ≥ φ s / s := le_abs_self _
  linarith

/-- The scalar Herbst differential inequality implies a quadratic bound.
The derivative at zero records the mean, so no centering hypothesis is hidden. -/
theorem quadratic_bound_of_herbst {F : ℝ → ℝ} {m a : ℝ}
    (hF : Differentiable ℝ F) (h0 : F 0 = 0) (hd0 : deriv F 0 = m)
    (hineq : ∀ s, s * deriv F s - F s ≤ a * s ^ 2 / 2) (t : ℝ) :
    F t ≤ m * t + a * t ^ 2 / 2 := by
  let φ : ℝ → ℝ := fun s => F s - m * s - a * s ^ 2 / 2
  have hd (s : ℝ) : HasDerivAt φ (deriv F s - m - a * s) s := by
    convert ((hF s).hasDerivAt.sub ((hasDerivAt_id s).const_mul m)).sub
      (((hasDerivAt_pow 2 s).const_mul a).div_const 2) using 1
    · funext y; simp [φ]
    · simp; ring
  have hz : φ 0 = 0 := by simp [φ, h0]
  have hdz : deriv φ 0 = 0 := by rw [(hd 0).deriv, hd0]; ring
  have hi (s : ℝ) : s * deriv φ s - φ s ≤ 0 := by
    rw [(hd s).deriv]
    dsimp [φ]
    linarith [hineq s]
  have hnonpos : φ t ≤ 0 := by
    rcases lt_trichotomy 0 t with ht | ht | ht
    · simpa using (div_le_iff₀ ht).mp
        (herbst_ratio_nonpos φ t ht hz hdz (fun s => (hd s).differentiableAt)
          (fun s _ => hi s))
    · simpa [← ht] using hz.le
    · let ψ : ℝ → ℝ := fun s => φ (-s)
      have hdψ (s : ℝ) : HasDerivAt ψ (-deriv φ (-s)) s := by
        convert (hd (-s)).comp s (hasDerivAt_neg s) using 1 <;>
          simp [(hd (-s)).deriv, ψ, Function.comp_def]
      have hψ0 : ψ 0 = 0 := by simpa [ψ] using hz
      have hdψ0 : deriv ψ 0 = 0 := by simp [(hdψ 0).deriv, hdz]
      have hiψ (s : ℝ) (_ : s ≠ 0) : s * deriv ψ s - ψ s ≤ 0 := by
        rw [(hdψ s).deriv]
        dsimp [ψ]
        nlinarith [hi (-s)]
      have hh := (div_le_iff₀ (neg_pos.mpr ht)).mp
        (herbst_ratio_nonpos ψ (-t) (neg_pos.mpr ht) hψ0 hdψ0
          (fun s => (hdψ s).differentiableAt) hiψ)
      simpa [ψ] using hh
  dsimp [φ] at hnonpos
  linarith

/-- Exponential entropy is the MGF times the Herbst differential expression. -/
theorem entropy_exp_eq_mgf_mul {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hint : ∀ t : ℝ, Integrable (fun x => exp (t * f x)) μ) (t : ℝ) :
    entropy μ (fun x => exp (t * f x)) =
      mgf f μ t * (t * deriv (cgf f μ) t - cgf f μ t) := by
  have hs : integrableExpSet f μ = Set.univ := Set.ext fun s => by simp [integrableExpSet, hint]
  have ht : t ∈ interior (integrableExpSet f μ) := by simp [hs]
  have hp : mgf f μ t ≠ 0 := (mgf_pos' (IsProbabilityMeasure.ne_zero μ) (hint t)).ne'
  rw [deriv_cgf ht]
  simp only [entropy, log_exp, cgf]
  have he : (∫ x, exp (t * f x) * (t * f x) ∂μ) =
      t * ∫ x, f x * exp (t * f x) ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [he]
  change t * (∫ x, f x * exp (t * f x) ∂μ) - mgf f μ t * log (mgf f μ t) = _
  field_simp

/-- Herbst's theorem: a proved exponential entropy estimate gives a centered
sub-Gaussian MGF with the same variance proxy. No LSI is assumed by this lemma. -/
theorem hasSubgaussianMGF_of_entropy_exp_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {c : ℝ≥0}
    (hint : ∀ t : ℝ, Integrable (fun x => exp (t * f x)) μ)
    (hent : ∀ t : ℝ, entropy μ (fun x => exp (t * f x)) ≤
      ((c : ℝ) * t ^ 2 / 2) * mgf f μ t) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂μ) c μ := by
  have hs : integrableExpSet f μ = Set.univ := Set.ext fun s => by simp [integrableExpSet, hint]
  have hmem (s : ℝ) : s ∈ interior (integrableExpSet f μ) := by simp [hs]
  have hbound (t : ℝ) : cgf f μ t ≤ (∫ x, f x ∂μ) * t + (c : ℝ) * t ^ 2 / 2 := by
    apply quadratic_bound_of_herbst (fun s => (analyticAt_cgf (hmem s)).differentiableAt)
      cgf_zero ?_ ?_ t
    · simpa using deriv_cgf_zero (hmem 0)
    · intro s
      have h := hent s
      rw [entropy_exp_eq_mgf_mul hint s] at h
      exact (mul_le_mul_iff_right₀ (mgf_pos' (IsProbabilityMeasure.ne_zero μ) (hint s))).mp
        (by simpa [mul_comm] using h)
  refine ⟨?_, ?_⟩
  · intro t
    have h := (hint t).mul_const (exp (-t * ∫ y, f y ∂μ))
    convert h using 1
    funext x
    rw [← exp_add]
    congr 1
    ring
  · intro t
    have hp := mgf_pos' (IsProbabilityMeasure.ne_zero μ) (hint t)
    have hm : mgf (fun x => f x - ∫ y, f y ∂μ) μ t =
        mgf f μ t * exp (-t * ∫ y, f y ∂μ) := by
      simp only [mgf]
      rw [← integral_mul_const]
      congr 1
      funext x
      rw [← exp_add]
      congr 1
      ring
    rw [hm, ← exp_log hp]
    rw [← exp_add]
    apply exp_le_exp.mpr
    change cgf f μ t + -t * (∫ y, f y ∂μ) ≤ _
    nlinarith [hbound t]

end LogSobolev
