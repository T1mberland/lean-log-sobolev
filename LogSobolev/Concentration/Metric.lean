module

public import LogSobolev.Concentration.Herbst
public import LogSobolev.Geometry.LocalSlopeChain
public import LogSobolev.Geometry.CompactRegularity
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

/-! # Concentration from metric logarithmic Sobolev inequalities

The Herbst argument uses the exact scalar exponential chain factor for local
slope. On noncompact spaces exponential moments are explicit hypotheses; on
compact spaces they follow from continuity. The variance proxy is `C K²`.
-/

open MeasureTheory ProbabilityTheory Real Filter ENNReal
open scoped ENNReal NNReal Topology

namespace LogSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]

omit [BorelSpace X] in
/-- An LSI controls exponential entropy of a Lipschitz observable. -/
theorem MetricLSI.entropy_exp_le {C K : ℝ≥0} (h : MetricLSI μ C)
    {f : X → ℝ} (hf : LipschitzWith K f)
    (hint : ∀ t : ℝ, Integrable (fun x => exp (t * f x)) μ) (t : ℝ) :
    entropy μ (fun x => exp (t * f x)) ≤
      ((C : ℝ) * (K : ℝ) ^ 2 * t ^ 2 / 2) * mgf f μ t := by
  let g : X → ℝ := fun x => exp (t / 2 * f x)
  have hg : LocallyLipschitz g :=
    ((contDiff_exp : ContDiff ℝ 1 Real.exp).comp
      (contDiff_const.mul contDiff_id)).locallyLipschitz.comp hf.locallyLipschitz
  have hsq : (fun x => g x ^ 2) = (fun x => exp (t * f x)) := by
    funext x
    dsimp [g]
    rw [sq, ← exp_add]
    congr 1
    ring
  have hs : integrableExpSet f μ = Set.univ := Set.ext fun s => by simp [integrableExpSet, hint]
  have hlog : Integrable (fun x => g x ^ 2 * log (g x ^ 2)) μ := by
    simp only [congrFun hsq, log_exp]
    have hi := (integrable_pow_mul_exp_of_mem_interior_integrableExpSet
      (show t ∈ interior (integrableExpSet f μ) by simp [hs]) 1).const_mul t
    convert hi using 1
    funext x
    simp only [pow_one]
    ring
  have hb (x : X) : localSlope g x ≤ ENNReal.ofReal (|t / 2| * exp (t / 2 * f x) * K) := by
    have hd : HasDerivAt (fun z : ℝ => exp (t / 2 * z))
        (exp (t / 2 * f x) * (t / 2)) (f x) :=
      by simpa using ((hasDerivAt_id (f x)).const_mul (t / 2)).exp
    simpa only [g, Function.comp_def, norm_mul, Real.norm_eq_abs, abs_exp, mul_comm,
      mul_left_comm, mul_assoc] using localSlope_comp_hasDerivAt_le hf x hd
  have he : slopeEnergy μ g ≤ ENNReal.ofReal ((t ^ 2 * (K : ℝ) ^ 2 / 4) * mgf f μ t) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal ((t ^ 2 * (K : ℝ) ^ 2 / 4) * exp (t * f x)) ∂μ := by
        apply lintegral_mono
        intro x
        calc
          _ ≤ (ENNReal.ofReal (|t / 2| * exp (t / 2 * f x) * K)) ^ 2 :=
            pow_le_pow_left' (hb x) 2
          _ = _ := by
            rw [← ofReal_pow (by positivity)]
            congr 1
            rw [mul_pow, mul_pow, sq_abs, div_pow, ← exp_nat_mul]
            norm_num only [Nat.cast_ofNat]
            rw [show 2 * (t / 2 * f x) = t * f x by ring]
            ring
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal ((hint t).const_mul _)
          (Eventually.of_forall fun x => by positivity), integral_const_mul]
        rfl
  have hh := (h g hg (by simpa only [hsq] using hint t) hlog).trans
    (mul_le_mul_right he _)
  rw [hsq] at hh
  have hn : 0 ≤ ((C : ℝ) * (K : ℝ)^2 * t^2 / 2) * mgf f μ t := by
    have := (mgf_pos' (IsProbabilityMeasure.ne_zero μ) (hint t)).le
    positivity
  apply (ofReal_le_ofReal_iff hn).mp
  convert hh using 1
  rw [← ofReal_coe_nnreal, ← ofReal_ofNat 2,
    ← ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (C : ℝ))]
  congr 1
  ring

omit [BorelSpace X] in
/-- Metric LSI implies a centered sub-Gaussian bound, provided all exponential
moments exist. Compactness is not required. -/
theorem MetricLSI.hasSubgaussianMGF {C K : ℝ≥0} (h : MetricLSI μ C)
    {f : X → ℝ} (hf : LipschitzWith K f)
    (hint : ∀ t : ℝ, Integrable (fun x => exp (t * f x)) μ) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂μ) (C * K ^ 2) μ := by
  apply hasSubgaussianMGF_of_entropy_exp_bound hint
  intro t
  simpa only [NNReal.coe_mul, NNReal.coe_pow] using h.entropy_exp_le hf hint t

/-- Compact metric LSI gives concentration for every globally Lipschitz real
observable; exponential integrability is automatic. -/
theorem MetricLSI.hasSubgaussianMGF_of_compact [CompactSpace X]
    {C K : ℝ≥0} (h : MetricLSI μ C) {f : X → ℝ} (hf : LipschitzWith K f) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂μ) (C * K ^ 2) μ := by
  apply h.hasSubgaussianMGF hf
  intro t
  exact (Real.continuous_exp.comp (continuous_const.mul hf.continuous)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Two-sided Chernoff bound in terms of a sub-Gaussian variance proxy. This also
includes the zero proxy and threshold zero with Mathlib's total division convention. -/
theorem measure_abs_ge_le_of_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {f : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF f c ν) {r : ℝ} (hr : 0 ≤ r) :
    ν.real {x | r ≤ |f x|} ≤ 2 * exp (-r ^ 2 / (2 * (c : ℝ))) := by
  have he : {x | r ≤ |f x|} = {x | r ≤ f x} ∪ {x | r ≤ -f x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [he]
  exact (measureReal_union_le _ _).trans (by
    have hu := h.measure_ge_le hr
    have hl := h.neg.measure_ge_le hr
    change ν.real {x | r ≤ -f x} ≤ _ at hl
    linarith)

/-- Upper tail from a compact metric LSI, with exponent `-r²/(2 C K²)`. -/
theorem MetricLSI.measure_ge_le [CompactSpace X] {C K : ℝ≥0}
    (h : MetricLSI μ C) {f : X → ℝ} (hf : LipschitzWith K f) {r : ℝ} (hr : 0 ≤ r) :
    μ.real {x | r ≤ f x - ∫ y, f y ∂μ} ≤
      exp (-r ^ 2 / (2 * ((C * K ^ 2 : ℝ≥0) : ℝ))) :=
  (h.hasSubgaussianMGF_of_compact hf).measure_ge_le hr

/-- Lower tail from a compact metric LSI. -/
theorem MetricLSI.measure_le_le [CompactSpace X] {C K : ℝ≥0}
    (h : MetricLSI μ C) {f : X → ℝ} (hf : LipschitzWith K f) {r : ℝ} (hr : 0 ≤ r) :
    μ.real {x | r ≤ (∫ y, f y ∂μ) - f x} ≤
      exp (-r ^ 2 / (2 * ((C * K ^ 2 : ℝ≥0) : ℝ))) := by
  simpa only [Pi.neg_apply, neg_sub] using
    (h.hasSubgaussianMGF_of_compact hf).neg.measure_ge_le hr

/-- Two-sided concentration from a compact metric LSI. -/
theorem MetricLSI.measure_abs_ge_le [CompactSpace X] {C K : ℝ≥0}
    (h : MetricLSI μ C) {f : X → ℝ} (hf : LipschitzWith K f) {r : ℝ} (hr : 0 ≤ r) :
    μ.real {x | r ≤ |f x - ∫ y, f y ∂μ|} ≤
      2 * exp (-r ^ 2 / (2 * ((C * K ^ 2 : ℝ≥0) : ℝ))) :=
  measure_abs_ge_le_of_hasSubgaussianMGF (h.hasSubgaussianMGF_of_compact hf) hr

end LogSobolev
