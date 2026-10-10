import LogSobolev.Unitary.SpecialUnitaryIntegratedGammaTwo
import LogSobolev.Unitary.SpecialUnitaryConnected
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.LocallyConstant.Basic

/-! # Zero energy for actual smooth SU functions

Normalized Haar measure has full support, so zero integrated energy forces
pointwise zero carré du champ. An orthonormal basis then detects every actual
invariant derivative. This identifies zero-energy functions as constant along
all exponential orbits. The proved connectedness of SU then gives global constancy.
-/

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

/-- Zero Haar energy implies pointwise zero energy, using full support of Haar. -/
theorem specialUnitaryGamma_eq_zero_of_integral_eq_zero
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hz : (∫ U, specialUnitaryGamma b f f U ∂specialUnitaryHaar n) = 0) :
    specialUnitaryGamma b f f = 0 := by
  have hc := (specialUnitaryGamma_contMDiff b hf hf).continuous
  exact Measure.eq_of_ae_eq ((integral_eq_zero_iff_of_nonneg
    (specialUnitaryGamma_nonneg b hf) (specialUnitary_integrable_of_continuous hc)).mp hz)
    hc continuous_const

/-- A real orthonormal basis detects all invariant derivatives at a zero-energy point. -/
theorem specialUnitaryDeriv_eq_zero_of_gamma_eq_zero
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    {U : Matrix.specialUnitaryGroup n ℂ} (hz : specialUnitaryGamma b f f U = 0)
    (A : specialUnitaryLieAlgebra (n := n)) : specialUnitaryDeriv A f U = 0 := by
  rw [specialUnitaryGamma_eq b hf hf] at hz
  have hi (i : ι) : specialUnitaryDeriv (b i) f U = 0 := by
    have h := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset ι)) => mul_self_nonneg (specialUnitaryDeriv (b j) f U))
      (Finset.mem_univ i)
    nlinarith
  unfold specialUnitaryDeriv at hi ⊢
  rw [← b.sum_repr A, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul, hi, smul_zero]

/-- Every actual invariant derivative vanishes when the integrated energy is zero. -/
theorem specialUnitaryDeriv_eq_zero_of_integral_gamma_eq_zero
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hz : (∫ U, specialUnitaryGamma b f f U ∂specialUnitaryHaar n) = 0)
    (A : specialUnitaryLieAlgebra (n := n)) (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryDeriv A f U = 0 :=
  specialUnitaryDeriv_eq_zero_of_gamma_eq_zero b hf
    (congrFun (specialUnitaryGamma_eq_zero_of_integral_eq_zero b hf hz) U) A

/-- A smooth function in the kernel of the actual generator has zero Haar energy. -/
theorem specialUnitary_integral_gamma_eq_zero_of_laplacian_eq_zero
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hL : specialUnitaryLaplacian b f = 0) :
    (∫ U, specialUnitaryGamma b f f U ∂specialUnitaryHaar n) = 0 := by
  have h := specialUnitary_integral_mul_laplacian b hf hf
  simp only [hL, Pi.zero_apply, mul_zero, integral_zero] at h
  linarith

/-- Vanishing invariant derivatives imply invariance under every exponential orbit. -/
theorem specialUnitary_eq_mul_exp_of_deriv_eq_zero
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hz : ∀ A U, specialUnitaryDeriv A f U = 0)
    (A : specialUnitaryLieAlgebra (n := n)) (U : Matrix.specialUnitaryGroup n ℂ) (t : ℝ) :
    f (U * specialUnitaryExpCurve A t) = f U := by
  have hd (s : ℝ) : HasDerivAt (fun r => f (U * specialUnitaryExpCurve A r)) 0 s := by
    simpa only [hz] using specialUnitary_hasDerivAt_mul_exp A U hf s
  have h := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simpa only [specialUnitaryExpCurve_zero, mul_one] using h

/-- Local exponential coordinates turn vanishing invariant derivatives into local constancy. -/
theorem specialUnitary_isLocallyConstant_of_deriv_eq_zero
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hz : ∀ A U, specialUnitaryDeriv A f U = 0) : IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_exists_open f).mpr
  intro U
  refine ⟨(specialUnitaryChartAt U).source, (specialUnitaryChartAt U).open_source,
    specialUnitary_mem_chart_source U, ?_⟩
  intro V hV
  have hv : U⁻¹ * V ∈ (specialUnitaryExpChart (n := n)).target := hV.2
  have he : specialUnitaryExpCurve (specialUnitaryLocalLog (U⁻¹ * V)) 1 = U⁻¹ * V :=
    specialUnitaryExpChart.right_inv hv
  have h := specialUnitary_eq_mul_exp_of_deriv_eq_zero hf hz
    (specialUnitaryLocalLog (U⁻¹ * V)) U 1
  simpa only [he, mul_inv_cancel_left] using h

/-- The actual SU generator has locally constant kernel on smooth functions.
Global constancy is not concluded without proving connectedness. -/
theorem specialUnitary_isLocallyConstant_of_laplacian_eq_zero
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hL : specialUnitaryLaplacian b f = 0) : IsLocallyConstant f :=
  specialUnitary_isLocallyConstant_of_deriv_eq_zero hf
    (specialUnitaryDeriv_eq_zero_of_integral_gamma_eq_zero b hf
      (specialUnitary_integral_gamma_eq_zero_of_laplacian_eq_zero b hf hL))

/-- Zero Haar energy forces global constancy on the actual connected SU group. -/
theorem specialUnitary_eq_const_of_integral_gamma_eq_zero
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hz : (∫ U, specialUnitaryGamma b f f U ∂specialUnitaryHaar n) = 0) :
    f = fun _ => f 1 :=
  (specialUnitary_isLocallyConstant_of_deriv_eq_zero hf
    (specialUnitaryDeriv_eq_zero_of_integral_gamma_eq_zero b hf hz)).eq_const 1

/-- The kernel of the actual SU generator on smooth real functions consists of constants. -/
theorem specialUnitary_eq_const_of_laplacian_eq_zero
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hL : specialUnitaryLaplacian b f = 0) : f = fun _ => f 1 :=
  specialUnitary_eq_const_of_integral_gamma_eq_zero b hf
    (specialUnitary_integral_gamma_eq_zero_of_laplacian_eq_zero b hf hL)

/-- The constant determined by zero energy is its normalized Haar mean. -/
theorem specialUnitary_eq_mean_of_integral_gamma_eq_zero
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hz : (∫ U, specialUnitaryGamma b f f U ∂specialUnitaryHaar n) = 0) :
    f = fun _ => ∫ U, f U ∂specialUnitaryHaar n := by
  have he := specialUnitary_eq_const_of_integral_gamma_eq_zero b hf hz
  have hm : (∫ U, f U ∂specialUnitaryHaar n) = f 1 := by
    conv_lhs => rw [he]
    simp
  exact he.trans (funext fun _ => hm.symm)

end LogSobolev
