module

public import LogSobolev.Measure.PowerKernel
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

/-! # Approximation by normalized powers

Concentration at a unique peak implies convergence of averages of continuous
Banach-valued functions. Taking the Banach space to be a continuous-function
space yields uniform approximation, not merely pointwise approximation.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace LogSobolev

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Normalized powers of a unique peak approximate evaluation, in any Banach space. -/
theorem tendsto_integral_powerKernel_smul {q : X → ℝ} (hq : Continuous q)
    (hn : ∀ x, 0 ≤ q x) {x₀ : X} (hx : q x₀ = 1)
    (hpeak : ∀ x, x ≠ x₀ → q x < 1) (F : C(X, E)) :
    Tendsto (fun j => ∫ x, powerKernel μ q j x • F x ∂μ) atTop (𝓝 (F x₀)) := by
  let G : C(X, E) := F - ContinuousMap.const X (F x₀)
  have hG : ∀ x, G x = F x - F x₀ := fun _ => rfl
  have hki (j : ℕ) : Integrable (powerKernel μ q j) μ :=
    (continuous_powerKernel μ hq j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hkn (j : ℕ) := powerKernel_nonneg μ hn j
  have hmass (j : ℕ) : ∫ x, powerKernel μ q j x ∂μ = 1 :=
    integral_powerKernel μ (integral_pow_pos μ hq hn (by rw [hx]; norm_num) j)
  have he (j : ℕ) : (∫ x, powerKernel μ q j x • F x ∂μ) - F x₀ =
      ∫ x, powerKernel μ q j x • G x ∂μ := by
    simp_rw [hG, smul_sub]
    rw [integral_sub (f := fun x => powerKernel μ q j x • F x)
      (g := fun x => powerKernel μ q j x • F x₀)
      (((continuous_powerKernel μ hq j).smul F.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      ((continuous_powerKernel μ hq j).smul continuous_const |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)), integral_smul_const, hmass, one_smul]
  rw [Metric.tendsto_nhds]
  intro ε hε
  let s : Set X := {x | ‖G x‖ < ε / 2}
  have hs : IsOpen s := isOpen_lt G.continuous.norm continuous_const
  have hxmem : x₀ ∈ s := by simp [s, G, half_pos hε]
  have ht := (tendsto_integral_powerKernel_compl_zero μ hq hn hx hpeak hs hxmem).const_mul ‖G‖
  have hsmall : ∀ᶠ j in atTop, ‖G‖ * (∫ x in sᶜ, powerKernel μ q j x ∂μ) < ε / 2 :=
    (tendsto_order.mp (by simpa using ht)).2 _ (half_pos hε)
  filter_upwards [hsmall] with j hj
  have hi : Integrable (fun x => powerKernel μ q j x * ‖G x‖) μ :=
    ((continuous_powerKernel μ hq j).mul G.continuous.norm).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hnear : (∫ x in s, powerKernel μ q j x * ‖G x‖ ∂μ) ≤ ε / 2 := by
    calc
      _ ≤ ∫ x in s, (ε / 2) * powerKernel μ q j x ∂μ :=
        integral_mono_ae hi.restrict ((hki j).const_mul _).restrict
          ((ae_restrict_mem hs.measurableSet).mono fun x hx => by
            dsimp [s] at hx
            nlinarith [hkn j x])
      _ = (ε / 2) * ∫ x in s, powerKernel μ q j x ∂μ := integral_const_mul _ _
      _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left
        (by rw [← hmass j]; exact setIntegral_le_integral (hki j) (Eventually.of_forall (hkn j)))
        (half_pos hε).le
      _ = _ := mul_one _
  have hfar : (∫ x in sᶜ, powerKernel μ q j x * ‖G x‖ ∂μ) ≤
      ‖G‖ * ∫ x in sᶜ, powerKernel μ q j x ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono hi.restrict ((hki j).const_mul _).restrict fun x => by
      nlinarith [G.norm_coe_le_norm x, hkn j x]
  rw [dist_eq_norm, he]
  calc
    _ ≤ ∫ x, ‖powerKernel μ q j x • G x‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x, powerKernel μ q j x * ‖G x‖ ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change ‖powerKernel μ q j x • G x‖ = powerKernel μ q j x * ‖G x‖
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hkn j x)]
    _ = (∫ x in s, powerKernel μ q j x * ‖G x‖ ∂μ) +
        ∫ x in sᶜ, powerKernel μ q j x * ‖G x‖ ∂μ := (integral_add_compl hs.measurableSet hi).symm
    _ ≤ ε / 2 + ‖G‖ * ∫ x in sᶜ, powerKernel μ q j x ∂μ := add_le_add hnear hfar
    _ < ε := by linarith

end LogSobolev
