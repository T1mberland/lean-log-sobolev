import LogSobolev.Unitary.PhaseSlices
import LogSobolev.Geometry.CompactRegularity
import LogSobolev.Unitary.SpecialUnitaryPolynomialFamily
import LogSobolev.Unitary.SpecialUnitaryPowerKernel

/-! # Polynomial regularization along the SU slices of U(N)

The polynomial-valued phase curve is Lipschitz, and hence differentiable almost
everywhere as a curve in a single finite-dimensional space. The kernel is the
proved normalized SU power kernel; no smoothing or differentiability hypothesis
is imposed on the input observable beyond its Lipschitz bound.
-/

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius NNReal

namespace LogSobolev

/-- SU convolution of a U(N) observable gives a Lipschitz polynomial-valued phase curve. -/
theorem unitary_exists_phase_polynomial (N : ℕ) (hN : 0 < N) (d : ℕ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℝ)) {K : NNReal} (hf : LipschitzWith K f) :
    ∃ p : ℝ → specialUnitaryPolynomialSpace (n := Fin N) d,
      (∀ t U, (p t).val U = ∫ V,
        f (phaseMul (Real.sqrt (2 / (N : ℝ))) t (specialUnitaryInclusion (U * V))) *
          (specialUnitaryPowerKernel d).val V ∂specialUnitaryHaar (Fin N)) ∧
      LipschitzWith (K * ⟨Real.sqrt 2, Real.sqrt_nonneg 2⟩) p ∧
      (∀ᵐ t ∂volume, DifferentiableAt ℝ p t) := by
  obtain ⟨p, hp, hLip⟩ := specialUnitaryPolynomial_exists_lipschitz_averaging d
    (specialUnitaryPowerKernel d) (specialUnitaryPowerKernel_nonneg d)
    (specialUnitaryPowerKernel_integral (by simpa using hN) d)
    (unitaryPhaseSlice N f) (unitaryPhaseSlice_lipschitz N hN f hf)
  exact ⟨p, hp, hLip, specialUnitaryPolynomialFamily_ae_differentiable d hLip⟩

/-- The polynomial phase regularization is available for every locally Lipschitz input. -/
theorem unitary_exists_phase_polynomial_of_locallyLipschitz (N : ℕ) (hN : 0 < N) (d : ℕ)
    {f : Matrix.unitaryGroup (Fin N) ℂ → ℝ} (hf : LocallyLipschitz f) :
    ∃ (K : NNReal) (p : ℝ → specialUnitaryPolynomialSpace (n := Fin N) d),
      (∀ t U, (p t).val U = ∫ V,
        f (phaseMul (Real.sqrt (2 / (N : ℝ))) t (specialUnitaryInclusion (U * V))) *
          (specialUnitaryPowerKernel d).val V ∂specialUnitaryHaar (Fin N)) ∧
      LipschitzWith K p ∧ (∀ᵐ t ∂volume, DifferentiableAt ℝ p t) := by
  obtain ⟨K, hK⟩ := hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_univ
  obtain ⟨p, hp, hl, hd⟩ := unitary_exists_phase_polynomial N hN d
    ⟨f, hf.continuous⟩ (lipschitzOnWith_univ.mp hK)
  exact ⟨_, p, hp, hl, hd⟩

end LogSobolev
