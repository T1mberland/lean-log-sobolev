module

public import LogSobolev.Measure.Entropy
public import LogSobolev.Measure.CompactDifferentiation
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

@[expose] public section

/-! # Differentiating entropy of positive families on compact probability spaces

Joint continuity of a positive family and of its time derivative provides all
domination and integrability needed for the entropy derivative. The formula
retains the varying-mass term; the zero-mass-derivative version is a corollary.
-/

open MeasureTheory Filter Topology

namespace LogSobolev

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- Derivative of entropy, including the correction for varying total mass. -/
theorem hasDerivAt_entropy_of_compact
    {F Q : ℝ → X → ℝ} {s : Set ℝ}
    (hF : Continuous (Function.uncurry F))
    (hQ : Continuous (Function.uncurry Q))
    (hpos : ∀ t x, 0 < F t x)
    (hd : ∀ t ∈ s, ∀ x, HasDerivAt (fun r => F r x) (Q t x) t)
    (t : ℝ) (hs : s ∈ 𝓝 t) :
    HasDerivAt (fun s => entropy μ (F s))
      ((∫ x, (Real.log (F t x) + 1) * Q t x ∂μ) -
        (Real.log (∫ x, F t x ∂μ) + 1) * (∫ x, Q t x ∂μ)) t := by
  have hlog : Continuous (fun p : ℝ × X => Real.log (F p.1 p.2)) :=
    hF.log (fun p => ne_of_gt (hpos p.1 p.2))
  have hprod := hasDerivAt_integral_of_compact (μ := μ)
    (F := fun r x => F r x * Real.log (F r x))
    (Q := fun r x => (Real.log (F r x) + 1) * Q r x)
    (hF.mul hlog) ((hlog.add (continuous_const (y := (1 : ℝ)))).mul hQ)
    (fun r hr x => by
      simpa only [Function.comp_def] using
        (Real.hasDerivAt_mul_log (x := F r x) (ne_of_gt (hpos r x))).comp r (hd r hr x)) t hs
  have hFt : Continuous (F t) := hF.comp (continuous_const.prodMk continuous_id)
  have hm : 0 < ∫ x, F t x ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun x => (hpos t x).le)
      (hFt.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    have hs : Function.support (F t) = Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact ne_of_gt (hpos t x)
    rw [hs, measure_univ]
    exact zero_lt_one
  have hmder := (Real.hasDerivAt_mul_log (x := ∫ x, F t x ∂μ) (ne_of_gt hm)).comp t
    (hasDerivAt_integral_of_compact (μ := μ) hF hQ hd t hs)
  exact hprod.sub hmder

/-- For a mass-preserving derivative, entropy differentiates to the logarithmic pairing. -/
theorem hasDerivAt_entropy_of_compact_of_integral_eq_zero
    {F Q : ℝ → X → ℝ} {s : Set ℝ}
    (hF : Continuous (Function.uncurry F))
    (hQ : Continuous (Function.uncurry Q))
    (hpos : ∀ t x, 0 < F t x)
    (hd : ∀ t ∈ s, ∀ x, HasDerivAt (fun r => F r x) (Q t x) t)
    (t : ℝ) (hs : s ∈ 𝓝 t) (hzero : (∫ x, Q t x ∂μ) = 0) :
    HasDerivAt (fun s => entropy μ (F s))
      (∫ x, Real.log (F t x) * Q t x ∂μ) t := by
  have h := hasDerivAt_entropy_of_compact (μ := μ) hF hQ hpos hd t hs
  have hFt : Continuous (F t) := hF.comp (continuous_const.prodMk continuous_id)
  have hQt : Continuous (Q t) := hQ.comp (continuous_const.prodMk continuous_id)
  have hlog := hFt.log (fun x => ne_of_gt (hpos t x))
  have hInt := (hlog.mul hQt).integrable_of_hasCompactSupport (μ := μ)
    (HasCompactSupport.of_compactSpace _)
  have hIntQ := hQt.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  simp only [add_mul, one_mul] at h
  have hi := integral_add hInt hIntQ
  simp only [Pi.mul_apply] at hi
  rw [hi, hzero] at h
  simpa only [add_zero, mul_zero, sub_zero] using h

end LogSobolev
