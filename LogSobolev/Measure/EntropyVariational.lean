import LogSobolev.Measure.Entropy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! # A real-valued Gibbs entropy bound

A positive density of mass one supplies a lower bound for entropy. All
integrability assumptions are explicit. This is the variational ingredient
for entropy subadditivity on products; it does not assume an LSI.
-/

open MeasureTheory

namespace LogSobolev

/-- The scalar relative-entropy inequality, including zero density. -/
theorem mul_log_le_mul_log_add_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    a * Real.log b ≤ a * Real.log a + b - a := by
  rcases ha.eq_or_lt with ha | ha
  · simp [← ha, hb.le]
  · have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hb ha)) ha.le
    rw [Real.log_div hb.ne' ha.ne'] at h
    have he : a * (b / a - 1) = b - a := by field_simp
    rw [he] at h
    linarith

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Gibbs' inequality for a positive reference density of mass one.
The log cross moment is required integrable, avoiding totalized-integral issues. -/
theorem integral_mul_log_le_entropy_of_integral_pos {g T : X → ℝ}
    (hg : 0 ≤ᵐ[μ] g) (hi : Integrable g μ)
    (hl : Integrable (fun x => g x * Real.log (g x)) μ)
    (hm : 0 < ∫ x, g x ∂μ)
    (hT : ∀ᵐ x ∂μ, 0 < T x) (hTi : Integrable T μ)
    (hTm : ∫ x, T x ∂μ = 1)
    (hc : Integrable (fun x => g x * Real.log (T x)) μ) :
    (∫ x, g x * Real.log (T x) ∂μ) ≤ entropy μ g := by
  let m := ∫ x, g x ∂μ
  have hpoint : ∀ᵐ x ∂μ,
      g x * Real.log (T x) + g x * Real.log m ≤
        g x * Real.log (g x) + m * T x - g x := by
    filter_upwards [hg, hT] with x hx htx
    have h := mul_log_le_mul_log_add_sub hx (mul_pos hm htx)
    rw [Real.log_mul hm.ne' htx.ne'] at h
    dsimp [m]
    nlinarith
  have h := integral_mono_ae (hc.add (hi.mul_const (Real.log m)))
    ((hl.add (hTi.const_mul m)).sub hi) hpoint
  simp only [Pi.add_apply, Pi.sub_apply] at h
  have hab : Integrable (fun x => g x * Real.log (g x) + m * T x) μ :=
    hl.add (hTi.const_mul m)
  rw [integral_add hc (hi.mul_const _), integral_mul_const,
    integral_sub hab hi,
    integral_add hl (hTi.const_mul m), integral_const_mul, hTm, mul_one] at h
  change (∫ x, g x * Real.log (T x) ∂μ) ≤
    (∫ x, g x * Real.log (g x) ∂μ) - m * Real.log m
  dsimp [m] at *
  linarith

/-- Gibbs' inequality also holds for a density of zero mass. -/
theorem integral_mul_log_le_entropy {g T : X → ℝ}
    (hg : 0 ≤ᵐ[μ] g) (hi : Integrable g μ)
    (hl : Integrable (fun x => g x * Real.log (g x)) μ)
    (hT : ∀ᵐ x ∂μ, 0 < T x) (hTi : Integrable T μ)
    (hTm : ∫ x, T x ∂μ = 1)
    (hc : Integrable (fun x => g x * Real.log (T x)) μ) :
    (∫ x, g x * Real.log (T x) ∂μ) ≤ entropy μ g := by
  by_cases hm : 0 < ∫ x, g x ∂μ
  · exact integral_mul_log_le_entropy_of_integral_pos hg hi hl hm hT hTi hTm hc
  · have hz : ∫ x, g x ∂μ = 0 := le_antisymm (not_lt.mp hm) (integral_nonneg_of_ae hg)
    have hgz := (integral_eq_zero_iff_of_nonneg_ae hg hi).mp hz
    have hc0 : (fun x => g x * Real.log (T x)) =ᵐ[μ] (fun _ => 0) :=
      hgz.mono fun x hx => by simp [hx]
    have hl0 : (fun x => g x * Real.log (g x)) =ᵐ[μ] (fun _ => 0) :=
      hgz.mono fun x hx => by simp [hx]
    simp [entropy, integral_congr_ae hc0, integral_congr_ae hl0, hz]

end LogSobolev
