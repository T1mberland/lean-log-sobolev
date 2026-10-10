module

public import LogSobolev.Unitary.UnitaryPhaseFlow
public import LogSobolev.Unitary.UnitaryConvolutionDerivative
public import LogSobolev.Unitary.SpecialUnitaryPolynomialJointDerivative
public import LogSobolev.Unitary.SpecialUnitarySlope

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Combined phase and SU energy of positive convolution

Testing along the sum of the phase gradient and SU gradient avoids the loss
from estimating the two coordinate slopes separately. The input is only
locally Lipschitz; differentiability is required solely of its polynomial
phase curve, a condition already proved almost everywhere.
-/

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius ENNReal NNReal

namespace LogSobolev

/-- A combined directional derivative is bounded by averaged original local slopes. -/
theorem unitary_phase_convolution_deriv_sq_le (N : ℕ) (hN : 0 < N) (d : ℕ)
    {f : Matrix.unitaryGroup (Fin N) ℂ → ℝ} (hf : LocallyLipschitz f)
    (k : C(Matrix.specialUnitaryGroup (Fin N) ℂ, ℝ))
    (hkn : ∀ V, 0 ≤ k V) (hkm : ∫ V, k V ∂specialUnitaryHaar (Fin N) = 1)
    {p : ℝ → specialUnitaryPolynomialSpace (n := Fin N) d}
    (he : ∀ t U, (p t).val U = ∫ V,
      f (phaseMul (Real.sqrt (2 / (N : ℝ))) t (specialUnitaryInclusion (U * V))) * k V
        ∂specialUnitaryHaar (Fin N))
    {t : ℝ} {p' : specialUnitaryPolynomialSpace (n := Fin N) d} (hp : HasDerivAt p p' t)
    (c : ℝ) (U : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : specialUnitaryLieAlgebra (n := Fin N)) :
    ENNReal.ofReal ((c * p'.val U + specialUnitaryDeriv A (p t).val U) ^ 2) ≤
      ENNReal.ofReal (‖A.val‖ ^ 2 + 2 * c ^ 2) *
        ∫⁻ V, ENNReal.ofReal (k V) * localSlope f
          (phaseMul (Real.sqrt (2 / (N : ℝ))) t (specialUnitaryInclusion (U * V))) ^ 2
            ∂specialUnitaryHaar (Fin N) := by
  have hid (r : ℝ) (V : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      unitaryPhaseFlow N t c U A r * specialUnitaryInclusion V =
        phaseMul (Real.sqrt (2 / (N : ℝ))) (t + c * r)
          (specialUnitaryInclusion ((U * specialUnitaryExpCurve A r) * V)) := by
    rw [map_mul, phaseMul_mul]
    rfl
  have hd := specialUnitaryPolynomial_hasDerivAt_phase_flow d hp c A U
  have hd' : HasDerivAt
      (fun r => ∫ V, f (unitaryPhaseFlow N t c U A r * specialUnitaryInclusion V) * k V
        ∂specialUnitaryHaar (Fin N))
      (c * p'.val U + specialUnitaryDeriv A (p t).val U) 0 := by
    simpa only [hid, he] using hd
  have h := unitary_SU_average_deriv_sq_le hf k hkn hkm
    (unitaryPhaseFlow_lipschitz N hN t c U A) hd'
  have hc : ((Real.toNNReal (Real.sqrt (‖A.val‖ ^ 2 + 2 * c ^ 2)) : NNReal) : ENNReal) ^ 2 =
      ENNReal.ofReal (‖A.val‖ ^ 2 + 2 * c ^ 2) := by
    change ENNReal.ofReal (Real.sqrt (‖A.val‖ ^ 2 + 2 * c ^ 2)) ^ 2 = _
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2, Real.sq_sqrt (by positivity)]
  simpa only [hc, hid, mul_zero, add_zero, specialUnitaryExpCurve_zero, mul_one] using h

/-- The full quadratic energy is bounded pointwise by the average of original squared slopes.
The phase derivative contributes half its square because the phase coordinate has speed `sqrt(2)`. -/
theorem unitary_phase_convolution_energy_le (N : ℕ) (hN : 0 < N) (d : ℕ)
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := Fin N)))
    {f : Matrix.unitaryGroup (Fin N) ℂ → ℝ} (hf : LocallyLipschitz f)
    (k : C(Matrix.specialUnitaryGroup (Fin N) ℂ, ℝ))
    (hkn : ∀ V, 0 ≤ k V) (hkm : ∫ V, k V ∂specialUnitaryHaar (Fin N) = 1)
    {p : ℝ → specialUnitaryPolynomialSpace (n := Fin N) d}
    (he : ∀ t U, (p t).val U = ∫ V,
      f (phaseMul (Real.sqrt (2 / (N : ℝ))) t (specialUnitaryInclusion (U * V))) * k V
        ∂specialUnitaryHaar (Fin N))
    {t : ℝ} {p' : specialUnitaryPolynomialSpace (n := Fin N) d} (hp : HasDerivAt p p' t)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ENNReal.ofReal (p'.val U ^ 2 / 2 + specialUnitaryGamma b (p t).val (p t).val U) ≤
      ∫⁻ V, ENNReal.ofReal (k V) * localSlope f
        (phaseMul (Real.sqrt (2 / (N : ℝ))) t (specialUnitaryInclusion (U * V))) ^ 2
          ∂specialUnitaryHaar (Fin N) := by
  let Q := p'.val U ^ 2 / 2 + specialUnitaryGamma b (p t).val (p t).val U
  have hQ : 0 ≤ Q := add_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
    (specialUnitaryGamma_nonneg b (p t).val.contMDiff U)
  have h := unitary_phase_convolution_deriv_sq_le N hN d hf k hkn hkm he hp
    (p'.val U / 2) U (specialUnitaryGradient b (p t).val U)
  rw [specialUnitaryDeriv_gradient b (p t).val.contMDiff U] at h
  have hn : ‖(specialUnitaryGradient b (p t).val U).val‖ ^ 2 =
      specialUnitaryGamma b (p t).val (p t).val U :=
    specialUnitaryGradient_norm_sq b (p t).val.contMDiff U
  rw [hn] at h
  have hdv : p'.val U / 2 * p'.val U + specialUnitaryGamma b (p t).val (p t).val U = Q := by
    dsimp [Q]; ring
  have hsv : specialUnitaryGamma b (p t).val (p t).val U + 2 * (p'.val U / 2) ^ 2 = Q := by
    dsimp [Q]; ring
  rw [hdv, hsv, ENNReal.ofReal_pow hQ 2, pow_two] at h
  by_cases hz : ENNReal.ofReal Q = 0
  · change ENNReal.ofReal Q ≤ _
    rw [hz]
    exact zero_le
  · exact (ENNReal.mul_le_mul_iff_right hz ENNReal.ofReal_ne_top).mp h

end LogSobolev
