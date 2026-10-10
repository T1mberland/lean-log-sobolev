import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Compact

/-! # Normalized powers as concentrating kernels

Powers of a continuous nonnegative function peaked at a point can be normalized
to probability densities. Comparing the function on two sets gives a geometric
tail bound. This is the concentration mechanism for polynomial approximate
identities; no Sobolev inequality is assumed.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace LogSobolev

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- The density obtained by normalizing a natural power of a real function. -/
noncomputable def powerKernel (q : X → ℝ) (j : ℕ) (x : X) : ℝ :=
  q x ^ j / (∫ y, q y ^ j ∂μ)

/-- Powers of continuous functions are integrable on a compact finite-measure space. -/
theorem integrable_pow_of_continuous {q : X → ℝ} (hq : Continuous q) (j : ℕ) :
    Integrable (fun x => q x ^ j) μ :=
  (hq.pow j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Full support and one positive value give strictly positive normalization. -/
theorem integral_pow_pos [μ.IsOpenPosMeasure] {q : X → ℝ} (hq : Continuous q)
    (hn : ∀ x, 0 ≤ q x) {x₀ : X} (hx : 0 < q x₀) (j : ℕ) :
    0 < ∫ x, q x ^ j ∂μ :=
  integral_pos_of_integrable_nonneg_nonzero (hq.pow j)
    (integrable_pow_of_continuous μ hq j) (fun x => pow_nonneg (hn x) j)
    (ne_of_gt (pow_pos hx j))

omit [CompactSpace X] [OpensMeasurableSpace X] [IsFiniteMeasure μ] in
/-- The normalized density is continuous, including when its denominator vanishes. -/
theorem continuous_powerKernel {q : X → ℝ} (hq : Continuous q) (j : ℕ) :
    Continuous (powerKernel μ q j) := (hq.pow j).div_const _

omit [TopologicalSpace X] [CompactSpace X] [OpensMeasurableSpace X] [IsFiniteMeasure μ] in
/-- Nonnegative functions give nonnegative normalized powers. -/
theorem powerKernel_nonneg {q : X → ℝ} (hn : ∀ x, 0 ≤ q x) (j : ℕ) (x : X) :
    0 ≤ powerKernel μ q j x :=
  div_nonneg (pow_nonneg (hn x) j) (integral_nonneg fun y => pow_nonneg (hn y) j)

omit [TopologicalSpace X] [CompactSpace X] [OpensMeasurableSpace X] [IsFiniteMeasure μ] in
/-- A positive normalization gives a density of mass one. -/
theorem integral_powerKernel {q : X → ℝ} {j : ℕ}
    (h : 0 < ∫ x, q x ^ j ∂μ) : ∫ x, powerKernel μ q j x ∂μ = 1 := by
  simp only [powerKernel, integral_div]
  exact div_self (ne_of_gt h)

/-- Geometric tail estimate: a set where `q ≤ a` loses mass relative to a
positive-measure set where `b ≤ q`, whenever `a < b`. The inequality itself
does not require `a < b`; that condition is used for convergence. -/
theorem integral_powerKernel_le {q : X → ℝ} (hq : Continuous q)
    (hn : ∀ x, 0 ≤ q x) {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hmt : 0 < μ.real t)
    (hqa : ∀ x ∈ s, q x ≤ a) (hqb : ∀ x ∈ t, b ≤ q x) (j : ℕ) :
    (∫ x in s, powerKernel μ q j x ∂μ) ≤
      (μ.real s / μ.real t) * (a / b) ^ j := by
  have hi := integrable_pow_of_continuous μ hq j
  have hl : μ.real t * b ^ j ≤ ∫ x, q x ^ j ∂μ := by
    calc
      _ = ∫ _ in t, b ^ j ∂μ := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ ∫ x in t, q x ^ j ∂μ := integral_mono_ae (integrable_const _) hi.restrict
        ((ae_restrict_mem ht).mono fun x hx => pow_le_pow_left₀ hb.le (hqb x hx) j)
      _ ≤ _ := setIntegral_le_integral hi (Eventually.of_forall fun x => pow_nonneg (hn x) j)
  have hz : 0 < ∫ x, q x ^ j ∂μ := (mul_pos hmt (pow_pos hb j)).trans_le hl
  have hu : (∫ x in s, q x ^ j ∂μ) ≤ μ.real s * a ^ j := by
    calc
      _ ≤ ∫ _ in s, a ^ j ∂μ := integral_mono_ae hi.restrict (integrable_const _)
        ((ae_restrict_mem hs).mono fun x hx => pow_le_pow_left₀ (hn x) (hqa x hx) j)
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  simp only [powerKernel, integral_div]
  calc
    _ ≤ (μ.real s * a ^ j) / (∫ x, q x ^ j ∂μ) := div_le_div_of_nonneg_right hu hz.le
    _ ≤ (μ.real s * a ^ j) / (μ.real t * b ^ j) :=
      div_le_div_of_nonneg_left (mul_nonneg (measureReal_nonneg) (pow_nonneg ha j))
        (mul_pos hmt (pow_pos hb j)) hl
    _ = _ := by rw [div_pow]; ring

/-- The normalized powers vanish in mass on any set with a strict gap below
the function on some positive-measure comparison set. -/
theorem tendsto_integral_powerKernel_zero {q : X → ℝ} (hq : Continuous q)
    (hn : ∀ x, 0 ≤ q x) {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hab : a < b) (hmt : 0 < μ.real t)
    (hqa : ∀ x ∈ s, q x ≤ a) (hqb : ∀ x ∈ t, b ≤ q x) :
    Tendsto (fun j => ∫ x in s, powerKernel μ q j x ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero (fun j => integral_nonneg fun x => powerKernel_nonneg μ hn j x)
    (integral_powerKernel_le μ hq hn hs ht ha hb hmt hqa hqb)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg ha hb.le)
    ((div_lt_one hb).mpr hab)).const_mul (μ.real s / μ.real t)

/-- Normalized powers concentrate at a unique maximum of height one.
Every open neighborhood of the maximum eventually contains all their mass. -/
theorem tendsto_integral_powerKernel_compl_zero [μ.IsOpenPosMeasure]
    {q : X → ℝ} (hq : Continuous q) (hn : ∀ x, 0 ≤ q x)
    {x₀ : X} (hx : q x₀ = 1) (hpeak : ∀ x, x ≠ x₀ → q x < 1)
    {s : Set X} (hs : IsOpen s) (hxs : x₀ ∈ s) :
    Tendsto (fun j => ∫ x in sᶜ, powerKernel μ q j x ∂μ) atTop (𝓝 0) := by
  by_cases he : sᶜ = ∅
  · simp only [he, Measure.restrict_empty, integral_zero_measure]
    exact tendsto_const_nhds
  obtain ⟨z, hz, hmax⟩ := hs.isClosed_compl.isCompact.exists_isMaxOn
    (Set.nonempty_iff_ne_empty.mpr he) hq.continuousOn
  have hz0 : z ≠ x₀ := fun h => hz (h ▸ hxs)
  obtain ⟨b, hzb, hb1⟩ := exists_between (hpeak z hz0)
  have hb : 0 < b := (hn z).trans_lt hzb
  have ht : IsOpen {x | b < q x} := isOpen_lt continuous_const hq
  have hmt : 0 < μ.real {x | b < q x} :=
    ENNReal.toReal_pos (ne_of_gt (ht.measure_pos μ ⟨x₀, by change b < q x₀; rw [hx]; exact hb1⟩))
      (measure_ne_top _ _)
  exact tendsto_integral_powerKernel_zero μ hq hn hs.measurableSet.compl ht.measurableSet
    (hn z) hb hzb hmt (fun x hx => hmax hx) (fun x hx => hx.le)

end LogSobolev
