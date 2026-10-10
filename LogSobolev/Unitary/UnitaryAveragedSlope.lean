import LogSobolev.Unitary.UnitaryConvolutionDerivative
import LogSobolev.Unitary.PhaseHaar
import Mathlib.MeasureTheory.Integral.Prod

/-! # Haar integration of averaged local slopes

Normalized SU averaging preserves the total local-slope energy on U(N).
The exact phase decomposition also transports arbitrary nonnegative measurable
integrands, permitting energy estimates without a continuity assumption on slopes.
-/

open Matrix MeasureTheory Filter
open scoped Matrix.Norms.Frobenius ENNReal NNReal

namespace LogSobolev

/-- The verified Haar phase decomposition in nonnegative-integral form. -/
theorem lintegral_phase_decomposition (N : ℕ) (hN : 0 < N)
    (g : Matrix.unitaryGroup (Fin N) ℂ → ENNReal) (hg : Measurable g) :
    (∫⁻ t, ∫⁻ U, g (phaseMul (Real.sqrt (2 / (N : ℝ))) t.val (specialUnitaryInclusion U))
      ∂specialUnitaryHaar (Fin N) ∂intervalUniform (phaseIntervalLength N)) =
        ∫⁻ U, g U ∂unitaryHaar (Fin N) := by
  have hF := (intervalPhaseMap_lipschitz N hN).continuous.measurable
  have hLp := WithLp.measurable_toLp 2 (PhaseInterval N × Matrix.specialUnitaryGroup (Fin N) ℂ)
  rw [← map_intervalPhaseMap N hN, lintegral_map hg hF]
  unfold phaseDomainMeasure
  have hc : Measurable (fun a => g (intervalPhaseMap N a)) := hg.comp hF
  rw [lintegral_map hc hLp]
  exact (lintegral_prod _ (hc.comp hLp).aemeasurable).symm

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Averaging over normalized SU kernels preserves the integrated U(N) slope energy. -/
theorem unitary_SU_average_slopeEnergy
    {f : Matrix.unitaryGroup n ℂ → ℝ} (hf : Continuous f)
    (k : C(Matrix.specialUnitaryGroup n ℂ, ℝ)) (hkn : ∀ V, 0 ≤ k V)
    (hkm : ∫ V, k V ∂specialUnitaryHaar n = 1) :
    (∫⁻ U, ∫⁻ V, ENNReal.ofReal (k V) * localSlope f (U * specialUnitaryInclusion V) ^ 2
      ∂specialUnitaryHaar n ∂unitaryHaar n) = slopeEnergy (unitaryHaar n) f := by
  have hsm := measurable_localSlope hf
  have hm : Measurable (fun z : Matrix.unitaryGroup n ℂ × Matrix.specialUnitaryGroup n ℂ =>
      ENNReal.ofReal (k z.2) * localSlope f (z.1 * specialUnitaryInclusion z.2) ^ 2) :=
    (k.continuous.measurable.ennreal_ofReal.comp measurable_snd).mul
      ((hsm.comp (measurable_fst.mul
        (specialUnitaryInclusion_isometry.continuous.measurable.comp measurable_snd))).pow_const 2)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc
    _ = ∫⁻ V, ENNReal.ofReal (k V) * slopeEnergy (unitaryHaar n) f ∂specialUnitaryHaar n := by
      apply lintegral_congr
      intro V
      have hV : Measurable (fun U => localSlope f (U * specialUnitaryInclusion V) ^ 2) :=
        (hsm.comp (measurable_id.mul_const _)).pow_const 2
      rw [lintegral_const_mul _ hV]
      rw [lintegral_mul_right_eq_self (μ := unitaryHaar n) (fun U => localSlope f U ^ 2)
        (specialUnitaryInclusion V)]
      rfl
    _ = _ := by
      rw [lintegral_mul_const _ k.continuous.measurable.ennreal_ofReal,
        ← ofReal_integral_eq_lintegral_ofReal
          (k.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          (Eventually.of_forall hkn), hkm, ENNReal.ofReal_one, one_mul]

/-- The same preservation identity in the phase/SU coordinates of the paper. -/
theorem phase_SU_average_slopeEnergy (N : ℕ) (hN : 0 < N)
    {f : Matrix.unitaryGroup (Fin N) ℂ → ℝ} (hf : Continuous f)
    (k : C(Matrix.specialUnitaryGroup (Fin N) ℂ, ℝ)) (hkn : ∀ V, 0 ≤ k V)
    (hkm : ∫ V, k V ∂specialUnitaryHaar (Fin N) = 1) :
    (∫⁻ t, ∫⁻ U, ∫⁻ V, ENNReal.ofReal (k V) * localSlope f
      (phaseMul (Real.sqrt (2 / (N : ℝ))) t.val (specialUnitaryInclusion U) *
        specialUnitaryInclusion V) ^ 2 ∂specialUnitaryHaar (Fin N)
          ∂specialUnitaryHaar (Fin N) ∂intervalUniform (phaseIntervalLength N)) =
      slopeEnergy (unitaryHaar (Fin N)) f := by
  have hm : Measurable (fun z : Matrix.unitaryGroup (Fin N) ℂ ×
      Matrix.specialUnitaryGroup (Fin N) ℂ =>
      ENNReal.ofReal (k z.2) * localSlope f (z.1 * specialUnitaryInclusion z.2) ^ 2) :=
    (k.continuous.measurable.ennreal_ofReal.comp measurable_snd).mul
      (((measurable_localSlope hf).comp (measurable_fst.mul
        (specialUnitaryInclusion_isometry.continuous.measurable.comp measurable_snd))).pow_const 2)
  exact (lintegral_phase_decomposition N hN _ hm.lintegral_prod_right).trans
    (unitary_SU_average_slopeEnergy hf k hkn hkm)

end LogSobolev
