/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
Adapted to heterogeneous binary products and Lean 4.28.0.
-/
import LogSobolev.Measure.Entropy
import Mathlib.MeasureTheory.Integral.Prod

/-! # Entropy chain rule on a product

This adapts the conditional entropy argument in StatsMLlib's
`Probability/Entropy/Conditional/Decomposition.lean` and the log-integrability
argument in `Conditional/Subadditivity.lean` to two possibly different spaces.
The marginal log moment is proved integrable, not supplied as an extra
assumption. These results are ingredients of tensorization, not metric-LSI
tensorization itself: control of the marginal square root's slope is still
needed for that application.
-/

open MeasureTheory Filter

namespace LogSobolev

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {g : X × Y → ℝ}

/-- Taking a marginal preserves log-moment integrability for a nonnegative
integrable density with integrable log moment. -/
theorem integrable_marginal_mul_log
    (hg : 0 ≤ᵐ[μ.prod ν] g) (hi : Integrable g (μ.prod ν))
    (hl : Integrable (fun p => g p * Real.log (g p)) (μ.prod ν)) :
    Integrable (fun x => (∫ y, g (x, y) ∂ν) * Real.log (∫ y, g (x, y) ∂ν)) μ := by
  let m := fun x => ∫ y, g (x, y) ∂ν
  let l := fun x => ∫ y, g (x, y) * Real.log (g (x, y)) ∂ν
  have hmn : ∀ᵐ x ∂μ, 0 ≤ m x :=
    (Measure.ae_ae_of_ae_prod hg).mono fun _ hx => integral_nonneg_of_ae hx
  have hj : ∀ᵐ x ∂μ, m x * Real.log (m x) ≤ l x := by
    filter_upwards [Measure.ae_ae_of_ae_prod hg, hi.prod_right_ae, hl.prod_right_ae]
      with x hx hix hlx
    exact Real.convexOn_mul_log.map_integral_le
      Real.continuous_mul_log.continuousOn isClosed_Ici hx hix hlx
  have hb : Integrable (fun x => |l x| + 1) μ :=
    hl.integral_prod_left.abs.add (integrable_const 1)
  have hm : AEStronglyMeasurable (fun x => m x * Real.log (m x)) μ :=
    Real.continuous_mul_log.comp_aestronglyMeasurable hi.integral_prod_left.aestronglyMeasurable
  apply hb.mono' hm
  filter_upwards [hmn, hj] with x hx hjx
  rw [Real.norm_eq_abs]
  by_cases hm1 : m x ≤ 1
  · by_cases hm0 : 0 < m x
    · have hbound : |m x * Real.log (m x)| < 1 := by
        rw [mul_comm]
        exact Real.abs_log_mul_self_lt (m x) hm0 hm1
      linarith [abs_nonneg (l x)]
    · have hz : m x = 0 := le_antisymm (not_lt.mp hm0) hx
      simp only [hz, zero_mul, abs_zero]
      positivity
  · rw [abs_of_nonneg (Real.mul_log_nonneg (not_le.mp hm1).le)]
    exact hjx.trans ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one))

/-- The entropy of a slice is integrable over the other coordinate. -/
theorem integrable_slice_entropy
    (hg : 0 ≤ᵐ[μ.prod ν] g) (hi : Integrable g (μ.prod ν))
    (hl : Integrable (fun p => g p * Real.log (g p)) (μ.prod ν)) :
    Integrable (fun x => entropy ν (fun y => g (x, y))) μ :=
  hl.integral_prod_left.sub (integrable_marginal_mul_log hg hi hl)

/-- Exact entropy chain rule, with all marginal log-integrability deduced
from the joint density's hypotheses. No LSI is assumed. -/
theorem entropy_prod_chain
    (hg : 0 ≤ᵐ[μ.prod ν] g) (hi : Integrable g (μ.prod ν))
    (hl : Integrable (fun p => g p * Real.log (g p)) (μ.prod ν)) :
    entropy (μ.prod ν) g =
      (∫ x, entropy ν (fun y => g (x, y)) ∂μ) +
        entropy μ (fun x => ∫ y, g (x, y) ∂ν) := by
  unfold entropy
  rw [integral_sub hl.integral_prod_left (integrable_marginal_mul_log hg hi hl),
    integral_prod _ hi, integral_prod _ hl]
  ring

/-- Entropy cannot increase when a coordinate is integrated out. -/
theorem entropy_marginal_le
    (hg : 0 ≤ᵐ[μ.prod ν] g) (hi : Integrable g (μ.prod ν))
    (hl : Integrable (fun p => g p * Real.log (g p)) (μ.prod ν)) :
    entropy μ (fun x => ∫ y, g (x, y) ∂ν) ≤ entropy (μ.prod ν) g := by
  rw [entropy_prod_chain hg hi hl]
  apply le_add_of_nonneg_left
  apply integral_nonneg_of_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hg, hi.prod_right_ae, hl.prod_right_ae]
    with x hx hix hlx
  exact entropy_nonneg hx hix hlx

end LogSobolev
