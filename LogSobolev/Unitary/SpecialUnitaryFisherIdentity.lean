module

public import LogSobolev.Unitary.SpecialUnitaryEntropyDissipation

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The spatial Fisher-information dissipation identity on SU

This module proves the integration-by-parts calculation underlying Fisher
information decay, using the actual generator, carré du champ, and normalized
Haar measure. Time differentiation and existence of heat trajectories are
separate obligations; no time-decay estimate is assumed here.
-/

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]
variable {f g : Matrix.specialUnitaryGroup n ℂ → ℝ}

/-- Symmetry follows directly from the generator definition, even before regularity is assumed. -/
theorem specialUnitaryGamma_comm
    (b : ι → specialUnitaryLieAlgebra (n := n))
    (f g : Matrix.specialUnitaryGroup n ℂ → ℝ) (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryGamma b f g U = specialUnitaryGamma b g f U := by
  unfold specialUnitaryGamma
  rw [mul_comm f g]
  ring

/-- Mixed logarithmic chain rule for the actual carré du champ. -/
theorem specialUnitaryGamma_log_mixed
    (b : ι → specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ g)
    (h0 : ∀ U, f U ≠ 0) (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryGamma b (Real.log ∘ f) g U = specialUnitaryGamma b f g U / f U := by
  rw [specialUnitaryGamma_eq b (specialUnitary_log_contMDiff hf h0) hg,
    specialUnitaryGamma_eq b hf hg]
  simp_rw [specialUnitaryDeriv_log _ U (hf.mdifferentiableAt (by decide)) (h0 U)]
  simp only [div_mul_eq_mul_div, Finset.sum_div]

/-- Multiplication by the original test removes the logarithmic weight. -/
theorem specialUnitary_mul_gamma_log_mixed
    (b : ι → specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ g)
    (h0 : ∀ U, f U ≠ 0) (U : Matrix.specialUnitaryGroup n ℂ) :
    f U * specialUnitaryGamma b (Real.log ∘ f) g U = specialUnitaryGamma b f g U := by
  rw [specialUnitaryGamma_log_mixed b hf hg h0]
  exact mul_div_cancel₀ _ (h0 U)

/-- Weighted Γ₂ of the logarithm, expressed by ordinary generator pairings. -/
theorem specialUnitary_integral_weighted_gammaTwo_log
    (b : ι → specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (h0 : ∀ U, f U ≠ 0) :
    (∫ U, f U * specialUnitaryGammaTwo b (Real.log ∘ f) U ∂specialUnitaryHaar n) =
      (∫ U, specialUnitaryLaplacian b f U *
        specialUnitaryGamma b (Real.log ∘ f) (Real.log ∘ f) U ∂specialUnitaryHaar n) / 2 +
      ∫ U, specialUnitaryLaplacian b f U *
        specialUnitaryLaplacian b (Real.log ∘ f) U ∂specialUnitaryHaar n := by
  have hl := specialUnitary_log_contMDiff hf h0
  have hG := specialUnitaryGamma_contMDiff b hl hl
  have hLG := specialUnitaryLaplacian_contMDiff b hG
  have hLl := specialUnitaryLaplacian_contMDiff b hl
  have h1 := specialUnitary_integrable_of_continuous (hf.continuous.mul hLG.continuous)
  have h2 := specialUnitary_integrable_of_continuous
    (specialUnitaryGamma_contMDiff b hf hLl).continuous
  have he (U : Matrix.specialUnitaryGroup n ℂ) :
      f U * specialUnitaryGammaTwo b (Real.log ∘ f) U =
        (f U * specialUnitaryLaplacian b (specialUnitaryGamma b (Real.log ∘ f) (Real.log ∘ f)) U -
          2 * specialUnitaryGamma b f (specialUnitaryLaplacian b (Real.log ∘ f)) U) / 2 := by
    unfold specialUnitaryGammaTwo
    rw [← specialUnitary_mul_gamma_log_mixed b hf hLl h0 U]
    ring
  simp_rw [he]
  rw [integral_div]
  have hi := integral_sub h1 (h2.const_mul 2)
  simp only [Pi.mul_apply] at hi
  rw [hi, integral_const_mul]
  have hsym := specialUnitary_laplacian_symmetric b hf hG
  have hparts2 := specialUnitary_integral_mul_laplacian b hLl hf
  simp only [mul_comm] at hsym hparts2
  rw [hsym]
  have hgSym : specialUnitaryGamma b f (specialUnitaryLaplacian b (Real.log ∘ f)) =
      specialUnitaryGamma b (specialUnitaryLaplacian b (Real.log ∘ f)) f := by
    funext U
    simp_rw [specialUnitaryGamma_eq b hf hLl, specialUnitaryGamma_eq b hLl hf, mul_comm]
  rw [hgSym]
  linarith

/-- The full spatial identity underlying Fisher-information dissipation.
The left side is the formal first variation of `∫ Γ(f,f)/f` in direction `Lf`;
this theorem proves its value without assuming a time-derivative identity. -/
theorem specialUnitary_fisher_variation_identity
    (b : ι → specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (h0 : ∀ U, f U ≠ 0) :
    (∫ U, 2 * specialUnitaryGamma b f (specialUnitaryLaplacian b f) U / f U -
        specialUnitaryGamma b f f U * specialUnitaryLaplacian b f U / (f U) ^ 2
      ∂specialUnitaryHaar n) =
      -2 * (∫ U, f U * specialUnitaryGammaTwo b (Real.log ∘ f) U ∂specialUnitaryHaar n) := by
  have hl := specialUnitary_log_contMDiff hf h0
  have hLf := specialUnitaryLaplacian_contMDiff b hf
  have hA := specialUnitary_integrable_of_continuous
    ((specialUnitaryGamma_contMDiff b hf hLf).continuous.div hf.continuous h0)
  have hB := specialUnitary_integrable_of_continuous
    (hLf.continuous.mul (specialUnitaryGamma_contMDiff b hl hl).continuous)
  have he (U : Matrix.specialUnitaryGroup n ℂ) :
      2 * specialUnitaryGamma b f (specialUnitaryLaplacian b f) U / f U -
        specialUnitaryGamma b f f U * specialUnitaryLaplacian b f U / (f U) ^ 2 =
      2 * (specialUnitaryGamma b f (specialUnitaryLaplacian b f) U / f U) -
        specialUnitaryLaplacian b f U *
          specialUnitaryGamma b (Real.log ∘ f) (Real.log ∘ f) U := by
    rw [specialUnitaryGamma_log b hf h0]
    ring
  simp_rw [he]
  have hi := integral_sub (hA.const_mul 2) hB
  simp only [Pi.mul_apply, Pi.div_apply] at hi
  rw [hi, integral_const_mul]
  have hp := specialUnitary_integral_mul_laplacian b hLf hl
  simp_rw [specialUnitaryGamma_comm b (specialUnitaryLaplacian b f) (Real.log ∘ f),
    specialUnitaryGamma_log_mixed b hf hLf h0] at hp
  have hw := specialUnitary_integral_weighted_gammaTwo_log b hf h0
  linarith

/-- The spatial Fisher variation is at most `−N` times Fisher information.
The real HS orthonormal basis fixes the exact unnormalized metric coefficient. -/
theorem specialUnitary_fisher_variation_le
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hpos : ∀ U, 0 < f U) :
    (∫ U, 2 * specialUnitaryGamma b f (specialUnitaryLaplacian b f) U / f U -
        specialUnitaryGamma b f f U * specialUnitaryLaplacian b f U / (f U) ^ 2
      ∂specialUnitaryHaar n) ≤
      -(Fintype.card n : ℝ) * (∫ U, specialUnitaryGamma b f f U / f U ∂specialUnitaryHaar n) := by
  rw [specialUnitary_fisher_variation_identity b hf (fun U => ne_of_gt (hpos U))]
  have h := specialUnitary_weighted_gammaTwo_log_lower_bound b hf hpos
  linarith

end LogSobolev
