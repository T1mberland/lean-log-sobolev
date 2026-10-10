module

public import LogSobolev.Unitary.SpecialUnitaryHaarCalculus
public import LogSobolev.Unitary.SpecialUnitaryGammaTwo

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Integrated Γ₂ identities for normalized SU Haar measure

Haar integration by parts identifies the integral of the actual Γ₂ with the
squared generator norm. Combining this with the proved pointwise curvature
estimate gives `(N/2) ∫ Γ(f,f) ≤ ∫ (Lf)²`. This is a coercivity estimate for the
generator on smooth tests, not yet a Poincaré or logarithmic Sobolev inequality.
-/

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

/-- Iterated carré du champ is smooth for every finite family of invariant directions. -/
theorem specialUnitaryGammaTwo_contMDiff
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f) :
    ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞
      (specialUnitaryGammaTwo b f) := by
  unfold specialUnitaryGammaTwo
  exact ((specialUnitaryLaplacian_contMDiff b (specialUnitaryGamma_contMDiff b hf hf)).sub
    (contMDiff_const.mul (specialUnitaryGamma_contMDiff b hf
      (specialUnitaryLaplacian_contMDiff b hf)))).div_const 2

/-- Integrated Γ₂ equals the squared generator norm for actual normalized Haar measure. -/
theorem specialUnitary_integral_gammaTwo
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f) :
    (∫ U, specialUnitaryGammaTwo b f U ∂specialUnitaryHaar n) =
      ∫ U, (specialUnitaryLaplacian b f U) ^ 2 ∂specialUnitaryHaar n := by
  have hL := specialUnitaryLaplacian_contMDiff b hf
  have hG := specialUnitaryGamma_contMDiff b hf hf
  have hLG := specialUnitary_integrable_of_continuous
    (specialUnitaryLaplacian_contMDiff b hG).continuous
  have hGL := specialUnitary_integrable_of_continuous
    (specialUnitaryGamma_contMDiff b hf hL).continuous
  unfold specialUnitaryGammaTwo
  rw [integral_div, integral_sub hLG (hGL.const_mul 2), integral_const_mul,
    specialUnitary_integral_laplacian_eq_zero b hG]
  have h := specialUnitary_integral_mul_laplacian b hL hf
  have he : specialUnitaryGamma b f (specialUnitaryLaplacian b f) =
      specialUnitaryGamma b (specialUnitaryLaplacian b f) f := by
    funext U
    simp_rw [specialUnitaryGamma_eq b hf hL, specialUnitaryGamma_eq b hL hf, mul_comm]
  rw [he]
  simp only [pow_two] at ⊢
  linarith

/-- The integrated curvature estimate, with the unnormalized Hilbert–Schmidt constant `N/2`.
This asserts generator coercivity; no spectral theorem or entropy inequality is assumed. -/
theorem specialUnitary_integrated_gammaTwo_lower_bound
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f) :
    (Fintype.card n : ℝ) / 2 *
        (∫ U, specialUnitaryGamma b f f U ∂specialUnitaryHaar n) ≤
      ∫ U, (specialUnitaryLaplacian b f U) ^ 2 ∂specialUnitaryHaar n := by
  rw [← specialUnitary_integral_gammaTwo b hf, ← integral_const_mul]
  exact integral_mono
    ((specialUnitary_integrable_of_continuous
      (specialUnitaryGamma_contMDiff b hf hf).continuous).const_mul _)
    (specialUnitary_integrable_of_continuous (specialUnitaryGammaTwo_contMDiff b hf).continuous)
    (specialUnitaryGammaTwo_lower_bound b hf)

end LogSobolev
