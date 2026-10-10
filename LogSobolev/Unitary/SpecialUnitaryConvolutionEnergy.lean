module

public import LogSobolev.Geometry.LocalSlopeAverage
public import LogSobolev.Geometry.CompactRegularity
public import LogSobolev.Unitary.SpecialUnitarySlope
public import LogSobolev.Unitary.SpecialUnitaryHaarCalculus
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Local-slope control of SU convolution energy

Positive normalized convolution is tested along the actual exponential curves.
A reverse-Fatou estimate for squared difference quotients handles locally
Lipschitz input without assuming its differentiability.
-/

open Matrix MeasureTheory Filter
open scoped Matrix.Norms.Frobenius Manifold ContDiff Topology ENNReal NNReal

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Right multiplication is an isometry for the actual unnormalized HS metric. -/
theorem specialUnitary_isometry_mul_right (V : Matrix.specialUnitaryGroup n ℂ) :
    Isometry (fun U : Matrix.specialUnitaryGroup n ℂ => U * V) := by
  apply isometry_iff_dist_eq.mpr
  intro U W
  simp only [Subtype.dist_eq, dist_eq_norm, Submonoid.coe_mul]
  change ‖U.val * V.val - W.val * V.val‖ = ‖U.val - W.val‖
  rw [← sub_mul]
  exact norm_mul_unitary _ (specialUnitaryInclusion V)

/-- A smooth convolution's directional derivative is controlled by averaged
squared local slopes of the nonsmooth input, with exact HS speed. -/
theorem specialUnitary_convolution_deriv_sq_le
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ} (hf : LocallyLipschitz f)
    (k : C(Matrix.specialUnitaryGroup n ℂ, ℝ)) (hkn : ∀ V, 0 ≤ k V)
    (hkm : ∫ V, k V ∂specialUnitaryHaar n = 1)
    {p : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hp : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ p)
    (he : ∀ U, p U = ∫ V, f (U * V) * k V ∂specialUnitaryHaar n)
    (U : Matrix.specialUnitaryGroup n ℂ) (A : specialUnitaryLieAlgebra (n := n)) :
    ENNReal.ofReal (specialUnitaryDeriv A p U ^ 2) ≤
      (‖A.val‖₊ : ℝ≥0∞) ^ 2 *
        ∫⁻ V, ENNReal.ofReal (k V) * localSlope f (U * V) ^ 2 ∂specialUnitaryHaar n := by
  let ν := (specialUnitaryHaar n).withDensity (fun V => ENNReal.ofReal (k V))
  have hkint : Integrable k (specialUnitaryHaar n) :=
    k.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  letI : IsProbabilityMeasure ν := ⟨by
    change ((specialUnitaryHaar n).withDensity (fun V => ENNReal.ofReal (k V))) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hkint (Eventually.of_forall hkn), hkm]
    exact ENNReal.ofReal_one⟩
  have hmean (W : Matrix.specialUnitaryGroup n ℂ) : (∫ V, f (W * V) ∂ν) = p W := by
    rw [he W]
    change (∫ V, f (W * V) ∂(specialUnitaryHaar n).withDensity
      (fun V => ENNReal.ofReal (k V))) = _
    rw [integral_withDensity_eq_integral_toReal_smul k.continuous.measurable.ennreal_ofReal
      (Eventually.of_forall (fun V => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    exact Eventually.of_forall fun V => by
      change (ENNReal.ofReal (k V)).toReal • f (W * V) = f (W * V) * k V
      rw [ENNReal.toReal_ofReal (hkn V), smul_eq_mul, mul_comm]
  obtain ⟨L, hL⟩ := hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_univ
  have hfL : LipschitzWith L f := lipschitzOnWith_univ.mp hL
  have hγ (V : Matrix.specialUnitaryGroup n ℂ) :
      LipschitzWith ‖A.val‖₊ (fun t => U * specialUnitaryExpCurve A t * V) := by
    simpa only [one_mul, Function.comp_def] using
      (specialUnitary_isometry_mul_right V).lipschitz.comp (specialUnitary_mul_exp_lipschitz U A)
  have hd := specialUnitary_hasDerivAt_mul_exp A U hp 0
  simp only [specialUnitaryExpCurve_zero, mul_one] at hd
  have hd' : HasDerivAt (fun t => ∫ V, f (U * specialUnitaryExpCurve A t * V) ∂ν)
      (specialUnitaryDeriv A p U) 0 := by simpa only [hmean] using hd
  have hsq := ofReal_deriv_integral_sq_le_lintegral_localSlope_sq ν
    (g := fun t V => f (U * specialUnitaryExpCurve A t * V))
    (fun t => hf.continuous.comp (continuous_const.mul continuous_id))
    (fun V => hfL.comp (hγ V)) hd'
  have hsl (V : Matrix.specialUnitaryGroup n ℂ) :
      localSlope (fun t => f (U * specialUnitaryExpCurve A t * V)) 0 ≤
        (‖A.val‖₊ : ℝ≥0∞) * localSlope f (U * V) := by
    simpa only [Function.comp_def, specialUnitaryExpCurve_zero, mul_one] using
      localSlope_comp_le (hγ V) f 0
  have hsm : Measurable (fun V => localSlope f (U * V) ^ 2) :=
    ((measurable_localSlope hf.continuous).comp (measurable_const.mul measurable_id)).pow_const 2
  calc
    _ ≤ ∫⁻ V, localSlope (fun t => f (U * specialUnitaryExpCurve A t * V)) 0 ^ 2 ∂ν := hsq
    _ ≤ ∫⁻ V, ((‖A.val‖₊ : ℝ≥0∞) * localSlope f (U * V)) ^ 2 ∂ν :=
      lintegral_mono fun V => pow_le_pow_left' (hsl V) 2
    _ = (‖A.val‖₊ : ℝ≥0∞) ^ 2 * ∫⁻ V, localSlope f (U * V) ^ 2 ∂ν := by
      simp_rw [mul_pow]
      exact lintegral_const_mul _ hsm
    _ = _ := by
      congr 1
      exact lintegral_withDensity_eq_lintegral_mul _ k.continuous.measurable.ennreal_ofReal hsm

variable {ι : Type*} [Fintype ι]

/-- The actual carré-du-champ energy of smooth positive convolution is bounded
pointwise by the convolution of the input's squared local slope. -/
theorem specialUnitary_convolution_gamma_le
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ} (hf : LocallyLipschitz f)
    (k : C(Matrix.specialUnitaryGroup n ℂ, ℝ)) (hkn : ∀ V, 0 ≤ k V)
    (hkm : ∫ V, k V ∂specialUnitaryHaar n = 1)
    {p : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hp : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ p)
    (he : ∀ U, p U = ∫ V, f (U * V) * k V ∂specialUnitaryHaar n)
    (U : Matrix.specialUnitaryGroup n ℂ) :
    ENNReal.ofReal (specialUnitaryGamma b p p U) ≤
      ∫⁻ V, ENNReal.ofReal (k V) * localSlope f (U * V) ^ 2 ∂specialUnitaryHaar n := by
  have hd := specialUnitary_convolution_deriv_sq_le hf k hkn hkm hp he U
    (specialUnitaryGradient b p U)
  rw [specialUnitaryDeriv_gradient b hp U] at hd
  have hn : (‖(specialUnitaryGradient b p U).val‖₊ : ℝ≥0∞) ^ 2 =
      ENNReal.ofReal (specialUnitaryGamma b p p U) := by
    calc
      _ = ENNReal.ofReal (‖specialUnitaryGradient b p U‖ ^ 2) := by
        rw [ENNReal.ofReal_pow (norm_nonneg _) 2]
        congr 1
        change (‖(specialUnitaryGradient b p U).val‖₊ : ℝ≥0∞) =
          ENNReal.ofReal ((‖(specialUnitaryGradient b p U).val‖₊ : ℝ≥0) : ℝ)
        exact ENNReal.ofReal_coe_nnreal.symm
      _ = _ := congrArg ENNReal.ofReal (specialUnitaryGradient_norm_sq b hp U)
  rw [hn, ENNReal.ofReal_pow (specialUnitaryGamma_nonneg b hp U) 2, pow_two] at hd
  by_cases hz : ENNReal.ofReal (specialUnitaryGamma b p p U) = 0
  · rw [hz]
    exact zero_le
  · exact (ENNReal.mul_le_mul_iff_right hz ENNReal.ofReal_ne_top).mp hd

/-- Positive normalized convolution controls integrated differential energy by
the input's actual Hilbert–Schmidt local-slope energy. No differentiability of
the input is assumed. -/
theorem specialUnitary_convolution_energy_le_slopeEnergy
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ} (hf : LocallyLipschitz f)
    (k : C(Matrix.specialUnitaryGroup n ℂ, ℝ)) (hkn : ∀ V, 0 ≤ k V)
    (hkm : ∫ V, k V ∂specialUnitaryHaar n = 1)
    {p : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hp : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ p)
    (he : ∀ U, p U = ∫ V, f (U * V) * k V ∂specialUnitaryHaar n) :
    ENNReal.ofReal (∫ U, specialUnitaryGamma b p p U ∂specialUnitaryHaar n) ≤
      slopeEnergy (specialUnitaryHaar n) f := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (specialUnitary_integrable_of_continuous (specialUnitaryGamma_contMDiff b hp hp).continuous)
    (Eventually.of_forall (specialUnitaryGamma_nonneg b hp))]
  have hsm := measurable_localSlope hf.continuous
  have hm : Measurable (fun z : Matrix.specialUnitaryGroup n ℂ × Matrix.specialUnitaryGroup n ℂ =>
      ENNReal.ofReal (k z.2) * localSlope f (z.1 * z.2) ^ 2) :=
    (k.continuous.measurable.ennreal_ofReal.comp measurable_snd).mul
      ((hsm.comp (measurable_fst.mul measurable_snd)).pow_const 2)
  calc
    _ ≤ ∫⁻ U, ∫⁻ V, ENNReal.ofReal (k V) * localSlope f (U * V) ^ 2 ∂specialUnitaryHaar n
        ∂specialUnitaryHaar n := lintegral_mono (specialUnitary_convolution_gamma_le b hf k hkn hkm hp he)
    _ = ∫⁻ V, ∫⁻ U, ENNReal.ofReal (k V) * localSlope f (U * V) ^ 2 ∂specialUnitaryHaar n
        ∂specialUnitaryHaar n := lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ V, ENNReal.ofReal (k V) * slopeEnergy (specialUnitaryHaar n) f ∂specialUnitaryHaar n := by
      apply lintegral_congr
      intro V
      have hV : Measurable (fun U => localSlope f (U * V) ^ 2) :=
        (hsm.comp (measurable_id.mul_const V)).pow_const 2
      rw [lintegral_const_mul _ hV]
      rw [lintegral_mul_right_eq_self (μ := specialUnitaryHaar n) (fun U => localSlope f U ^ 2) V]
      rfl
    _ = _ := by
      rw [lintegral_mul_const _ k.continuous.measurable.ennreal_ofReal,
        ← ofReal_integral_eq_lintegral_ofReal
          (specialUnitary_integrable_of_continuous k.continuous) (Eventually.of_forall hkn),
        hkm, ENNReal.ofReal_one, one_mul]

end LogSobolev
