import LogSobolev.Geometry.LocalSlopeAverage
import LogSobolev.Geometry.CompactRegularity
import LogSobolev.Unitary.SpecialUnitary

/-! # Local-slope control of SU averages on U(N)

A differentiable average along a Lipschitz U(N) curve is controlled by the
average of the input's squared local slope. Only the average is differentiated;
the original observable may be nonsmooth.
-/

open Matrix MeasureTheory Filter
open scoped Matrix.Norms.Frobenius ENNReal NNReal

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Right translation preserves the unnormalized HS metric on U(N). -/
theorem unitary_isometry_mul_right (V : Matrix.unitaryGroup n ℂ) :
    Isometry (fun U : Matrix.unitaryGroup n ℂ => U * V) := by
  apply Isometry.of_dist_eq
  intro U W
  change ‖U.val * V.val - W.val * V.val‖ = ‖U.val - W.val‖
  rw [← sub_mul]
  exact norm_mul_unitary _ V

/-- A derivative of a normalized SU average is controlled by the original U(N) slope. -/
theorem unitary_SU_average_deriv_sq_le
    {f : Matrix.unitaryGroup n ℂ → ℝ} (hf : LocallyLipschitz f)
    (k : C(Matrix.specialUnitaryGroup n ℂ, ℝ)) (hkn : ∀ V, 0 ≤ k V)
    (hkm : ∫ V, k V ∂specialUnitaryHaar n = 1)
    {γ : ℝ → Matrix.unitaryGroup n ℂ} {K : NNReal} (hγ : LipschitzWith K γ)
    {a : ℝ} (hd : HasDerivAt
      (fun t => ∫ V, f (γ t * specialUnitaryInclusion V) * k V ∂specialUnitaryHaar n) a 0) :
    ENNReal.ofReal (a ^ 2) ≤ (K : ENNReal) ^ 2 *
      ∫⁻ V, ENNReal.ofReal (k V) * localSlope f (γ 0 * specialUnitaryInclusion V) ^ 2
        ∂specialUnitaryHaar n := by
  let ν := (specialUnitaryHaar n).withDensity (fun V => ENNReal.ofReal (k V))
  have hkint : Integrable k (specialUnitaryHaar n) :=
    k.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  letI : IsProbabilityMeasure ν := ⟨by
    change ((specialUnitaryHaar n).withDensity (fun V => ENNReal.ofReal (k V))) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hkint (Eventually.of_forall hkn), hkm]
    exact ENNReal.ofReal_one⟩
  have hmean (W : Matrix.unitaryGroup n ℂ) :
      (∫ V, f (W * specialUnitaryInclusion V) ∂ν) =
        ∫ V, f (W * specialUnitaryInclusion V) * k V ∂specialUnitaryHaar n := by
    change (∫ V, f (W * specialUnitaryInclusion V) ∂(specialUnitaryHaar n).withDensity
      (fun V => ENNReal.ofReal (k V))) = _
    rw [integral_withDensity_eq_integral_toReal_smul k.continuous.measurable.ennreal_ofReal
      (Eventually.of_forall (fun V => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    exact Eventually.of_forall fun V => by
      change (ENNReal.ofReal (k V)).toReal • f (W * specialUnitaryInclusion V) = _
      rw [ENNReal.toReal_ofReal (hkn V), smul_eq_mul, mul_comm]
  obtain ⟨L, hL⟩ := hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_univ
  have hfL : LipschitzWith L f := lipschitzOnWith_univ.mp hL
  have hcurve (V : Matrix.specialUnitaryGroup n ℂ) :
      LipschitzWith K (fun t => γ t * specialUnitaryInclusion V) := by
    simpa only [one_mul] using
      (unitary_isometry_mul_right (specialUnitaryInclusion V)).lipschitz.comp hγ
  have hd' : HasDerivAt (fun t => ∫ V, f (γ t * specialUnitaryInclusion V) ∂ν) a 0 := by
    simpa only [hmean] using hd
  have hsq := ofReal_deriv_integral_sq_le_lintegral_localSlope_sq ν
    (g := fun t V => f (γ t * specialUnitaryInclusion V))
    (fun t => hf.continuous.comp (continuous_const.mul specialUnitaryInclusion_isometry.continuous))
    (fun V => hfL.comp (hcurve V)) hd'
  have hsl (V : Matrix.specialUnitaryGroup n ℂ) :
      localSlope (fun t => f (γ t * specialUnitaryInclusion V)) 0 ≤
        (K : ENNReal) * localSlope f (γ 0 * specialUnitaryInclusion V) :=
    localSlope_comp_le (hcurve V) f 0
  have hsm : Measurable (fun V => localSlope f (γ 0 * specialUnitaryInclusion V) ^ 2) :=
    ((measurable_localSlope hf.continuous).comp
      (measurable_const.mul specialUnitaryInclusion_isometry.continuous.measurable)).pow_const 2
  calc
    _ ≤ ∫⁻ V, localSlope (fun t => f (γ t * specialUnitaryInclusion V)) 0 ^ 2 ∂ν := hsq
    _ ≤ ∫⁻ V, ((K : ENNReal) * localSlope f (γ 0 * specialUnitaryInclusion V)) ^ 2 ∂ν :=
      lintegral_mono fun V => pow_le_pow_left' (hsl V) 2
    _ = (K : ENNReal) ^ 2 * ∫⁻ V, localSlope f (γ 0 * specialUnitaryInclusion V) ^ 2 ∂ν := by
      simp_rw [mul_pow]
      exact lintegral_const_mul _ hsm
    _ = _ := by
      congr 1
      exact lintegral_withDensity_eq_lintegral_mul _ k.continuous.measurable.ennreal_ofReal hsm

end LogSobolev
