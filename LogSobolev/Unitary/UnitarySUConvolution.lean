import LogSobolev.Unitary.SpecialUnitaryPowerKernel
import LogSobolev.Measure.PowerKernelApproximation
import LogSobolev.Measure.EntropyContinuity

/-! # Uniform approximation on U(N) by SU convolution

The actual normalized SU power kernels approximate continuous U(N) observables
uniformly. This regularizes the SU directions while leaving a Lipschitz phase
parameter, avoiding an assumed smooth approximation on the U(N) manifold.
-/

open Matrix MeasureTheory Filter
open scoped Matrix.Norms.Frobenius Topology

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Right translation of a continuous U observable by an SU matrix. -/
noncomputable def unitarySUTranslate (f : C(Matrix.unitaryGroup n ℂ, ℝ))
    (V : Matrix.specialUnitaryGroup n ℂ) : C(Matrix.unitaryGroup n ℂ, ℝ) :=
  ⟨fun U => f (U * specialUnitaryInclusion V),
    f.continuous.comp (continuous_id.mul continuous_const)⟩

theorem continuous_unitarySUTranslate (f : C(Matrix.unitaryGroup n ℂ, ℝ)) :
    Continuous (unitarySUTranslate f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact f.continuous.comp (continuous_snd.mul
    (specialUnitaryInclusion_isometry.continuous.comp continuous_fst))

/-- SU convolution as a continuous function on the actual unitary group. -/
noncomputable def unitarySUConvolution (d : ℕ) (f : C(Matrix.unitaryGroup n ℂ, ℝ)) :
    C(Matrix.unitaryGroup n ℂ, ℝ) :=
  ∫ V, (specialUnitaryPowerKernel d).val V • unitarySUTranslate f V ∂specialUnitaryHaar n

/-- The Banach-space integral has the usual scalar averaging formula. -/
theorem unitarySUConvolution_apply (d : ℕ) (f : C(Matrix.unitaryGroup n ℂ, ℝ))
    (U : Matrix.unitaryGroup n ℂ) :
    unitarySUConvolution d f U =
      ∫ V, f (U * specialUnitaryInclusion V) * (specialUnitaryPowerKernel d).val V
        ∂specialUnitaryHaar n := by
  unfold unitarySUConvolution
  rw [ContinuousMap.integral_apply
    (((specialUnitaryPowerKernel d).val.contMDiff.continuous.smul
      (continuous_unitarySUTranslate f)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae
  exact Eventually.of_forall fun V => by
    change (specialUnitaryPowerKernel d).val V * f (U * specialUnitaryInclusion V) = _
    rw [mul_comm]

/-- Convergence in uniform norm of the SU regularizations of an arbitrary continuous U function. -/
theorem tendsto_unitarySUConvolution (hN : 0 < Fintype.card n)
    (f : C(Matrix.unitaryGroup n ℂ, ℝ)) :
    Tendsto (fun d => unitarySUConvolution d f) atTop (𝓝 f) := by
  have h1 : unitarySUTranslate f 1 = f := by
    ext U
    change f (U * specialUnitaryInclusion 1) = f U
    rw [map_one, mul_one]
  have ht := tendsto_integral_powerKernel_smul (specialUnitaryHaar n)
    specialUnitaryPeak.val.contMDiff.continuous specialUnitaryPeak_nonneg
    (specialUnitaryPeak_one hN) (specialUnitaryPeak_lt_one hN)
    (⟨unitarySUTranslate f, continuous_unitarySUTranslate f⟩ : C(_, C(_, ℝ)))
  simpa only [ContinuousMap.coe_mk, ← specialUnitaryPowerKernel_apply, h1,
    unitarySUConvolution] using ht

/-- Squared entropy also converges, allowing signed functions and zeros. -/
theorem tendsto_entropy_sq_unitarySUConvolution (hN : 0 < Fintype.card n)
    (f : C(Matrix.unitaryGroup n ℂ, ℝ)) :
    Tendsto (fun d => entropy (unitaryHaar n) (fun U => unitarySUConvolution d f U ^ 2)) atTop
      (𝓝 (entropy (unitaryHaar n) (fun U => f U ^ 2))) :=
  tendsto_entropy_sq_of_tendsto_continuousMap (unitaryHaar n) (tendsto_unitarySUConvolution hN f)

end LogSobolev
