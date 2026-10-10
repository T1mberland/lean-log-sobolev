import LogSobolev.Unitary.UnitaryPhaseConvolutionEnergy
import LogSobolev.Unitary.UnitaryAveragedSlope
import LogSobolev.Measure.IntervalAlmostEverywhere
import LogSobolev.Unitary.UnitaryPhasePolynomial

/-! # Integrated energy bound for polynomial phase regularization

The polynomial-valued derivative exists almost everywhere by Rademacher.
The pointwise quadratic estimate integrates through the proved Haar phase
decomposition to the original U(N) slope energy, with no constant loss.
-/

open Matrix MeasureTheory Filter
open scoped Matrix.Norms.Frobenius ENNReal NNReal

namespace LogSobolev

/-- The phase/SU quadratic energy of a positive convolution is bounded by the input slope energy. -/
theorem unitary_phase_integrated_energy_le (N : ℕ) (hN : 0 < N) (d : ℕ)
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := Fin N)))
    {f : Matrix.unitaryGroup (Fin N) ℂ → ℝ} (hf : LocallyLipschitz f)
    (k : C(Matrix.specialUnitaryGroup (Fin N) ℂ, ℝ))
    (hkn : ∀ V, 0 ≤ k V) (hkm : ∫ V, k V ∂specialUnitaryHaar (Fin N) = 1)
    {p : ℝ → specialUnitaryPolynomialSpace (n := Fin N) d} {K : NNReal}
    (hp : LipschitzWith K p)
    (he : ∀ t U, (p t).val U = ∫ V,
      f (phaseMul (Real.sqrt (2 / (N : ℝ))) t (specialUnitaryInclusion (U * V))) * k V
        ∂specialUnitaryHaar (Fin N)) :
    (∫⁻ t, ∫⁻ U, ENNReal.ofReal ((deriv p t.val).val U ^ 2 / 2 +
        specialUnitaryGamma b (p t.val).val (p t.val).val U)
      ∂specialUnitaryHaar (Fin N) ∂intervalUniform (phaseIntervalLength N)) ≤
      slopeEnergy (unitaryHaar (Fin N)) f := by
  have hd := ae_intervalUniform_of_ae (phaseIntervalLength N)
    (specialUnitaryPolynomialFamily_ae_differentiable d hp)
  calc
    _ ≤ ∫⁻ t, ∫⁻ U, ∫⁻ V, ENNReal.ofReal (k V) * localSlope f
        (phaseMul (Real.sqrt (2 / (N : ℝ))) t.val (specialUnitaryInclusion U) *
          specialUnitaryInclusion V) ^ 2 ∂specialUnitaryHaar (Fin N)
            ∂specialUnitaryHaar (Fin N) ∂intervalUniform (phaseIntervalLength N) := by
      apply lintegral_mono_ae
      filter_upwards [hd] with t ht
      apply lintegral_mono
      intro U
      simpa only [map_mul, phaseMul_mul] using
        unitary_phase_convolution_energy_le N hN d b hf k hkn hkm he ht.hasDerivAt U
    _ = _ := phase_SU_average_slopeEnergy N hN hf.continuous k hkn hkm

/-- The actual power-kernel approximants exist with the integrated energy bound;
no energy-control assumption is imposed on the input. -/
theorem unitary_exists_phase_polynomial_energy (N : ℕ) (hN : 0 < N) (d : ℕ)
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := Fin N)))
    {f : Matrix.unitaryGroup (Fin N) ℂ → ℝ} (hf : LocallyLipschitz f) :
    ∃ (K : NNReal) (p : ℝ → specialUnitaryPolynomialSpace (n := Fin N) d),
      (∀ t U, (p t).val U = ∫ V,
        f (phaseMul (Real.sqrt (2 / (N : ℝ))) t (specialUnitaryInclusion (U * V))) *
          (specialUnitaryPowerKernel d).val V ∂specialUnitaryHaar (Fin N)) ∧
      LipschitzWith K p ∧
      (∫⁻ t, ∫⁻ U, ENNReal.ofReal ((deriv p t.val).val U ^ 2 / 2 +
          specialUnitaryGamma b (p t.val).val (p t.val).val U)
        ∂specialUnitaryHaar (Fin N) ∂intervalUniform (phaseIntervalLength N)) ≤
        slopeEnergy (unitaryHaar (Fin N)) f := by
  obtain ⟨K, p, he, hp, _⟩ := unitary_exists_phase_polynomial_of_locallyLipschitz N hN d hf
  refine ⟨K, p, he, hp, ?_⟩
  exact unitary_phase_integrated_energy_le N hN d b hf
    (specialUnitaryPolynomialToContinuous d (specialUnitaryPowerKernel d))
    (specialUnitaryPowerKernel_nonneg d)
    (specialUnitaryPowerKernel_integral (by simpa using hN) d) hp he

end LogSobolev
