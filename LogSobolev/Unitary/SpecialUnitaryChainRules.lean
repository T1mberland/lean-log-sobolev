import LogSobolev.Unitary.SpecialUnitaryHaarCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Scalar chain rules for the actual SU differential operators

These rules connect the invariant derivatives and Haar Dirichlet identity with
the logarithmic expressions needed for entropy dissipation. They make no
assumption about existence of a heat flow or an entropy-decay estimate.
-/

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {f : Matrix.specialUnitaryGroup n ℂ → ℝ}

/-- Scalar chain rule for an actual invariant derivative at a differentiability point. -/
theorem specialUnitaryDeriv_comp
    (A : specialUnitaryLieAlgebra (n := n)) (U : Matrix.specialUnitaryGroup n ℂ)
    (hf : MDifferentiableAt 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) f U)
    {φ : ℝ → ℝ} {φ' : ℝ} (hφ : HasDerivAt φ φ' (f U)) :
    specialUnitaryDeriv A (φ ∘ f) U = φ' * specialUnitaryDeriv A f U := by
  have h := hφ.hasFDerivAt.hasMFDerivAt.comp U hf.hasMFDerivAt
  have he := DFunLike.congr_fun h.mfderiv A
  change specialUnitaryDeriv A (φ ∘ f) U = specialUnitaryDeriv A f U * φ' at he
  simpa only [mul_comm] using he

/-- A nowhere-zero smooth real test has a smooth real logarithm. -/
theorem specialUnitary_log_contMDiff
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (h0 : ∀ U, f U ≠ 0) :
    ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ (Real.log ∘ f) := by
  intro U
  exact (Real.contDiffAt_log.mpr (h0 U)).comp_contMDiffAt hf.contMDiffAt

/-- Logarithmic derivative of an SU test, with the denominator explicitly nonzero. -/
theorem specialUnitaryDeriv_log
    (A : specialUnitaryLieAlgebra (n := n)) (U : Matrix.specialUnitaryGroup n ℂ)
    (hf : MDifferentiableAt 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) f U)
    (h0 : f U ≠ 0) :
    specialUnitaryDeriv A (Real.log ∘ f) U = specialUnitaryDeriv A f U / f U := by
  simpa [div_eq_mul_inv, mul_comm] using
    specialUnitaryDeriv_comp A U hf (Real.hasDerivAt_log h0)

variable {ι : Type*} [Fintype ι]

/-- The diffusion chain rule for the constructed SU generator.
Scalar smoothness is needed only along the range of the test function. -/
theorem specialUnitaryLaplacian_comp
    (b : ι → specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    {φ φ' φ'' : ℝ → ℝ}
    (hφ : ∀ U, HasDerivAt φ (φ' (f U)) (f U))
    (hφ' : ∀ U, HasDerivAt φ' (φ'' (f U)) (f U))
    (hs : ∀ U, ContDiffAt ℝ ∞ φ' (f U)) (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryLaplacian b (φ ∘ f) U =
      φ' (f U) * specialUnitaryLaplacian b f U +
        φ'' (f U) * specialUnitaryGamma b f f U := by
  have hc : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ (φ' ∘ f) :=
    fun V => (hs V).comp_contMDiffAt hf.contMDiffAt
  have he (A : specialUnitaryLieAlgebra (n := n)) :
      specialUnitaryDeriv A (φ ∘ f) = (φ' ∘ f) * specialUnitaryDeriv A f := by
    funext V
    exact specialUnitaryDeriv_comp A V (hf.mdifferentiableAt (by decide)) (hφ V)
  have htwice (A : specialUnitaryLieAlgebra (n := n)) :
      specialUnitaryDeriv A (specialUnitaryDeriv A (φ ∘ f)) U =
        φ' (f U) * specialUnitaryDeriv A (specialUnitaryDeriv A f) U +
          φ'' (f U) * (specialUnitaryDeriv A f U * specialUnitaryDeriv A f U) := by
    rw [he, specialUnitaryDeriv_mul A hc (specialUnitaryDeriv_contMDiff A hf)]
    simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]
    rw [specialUnitaryDeriv_comp A U (hf.mdifferentiableAt (by decide)) (hφ' U)]
    ring
  rw [specialUnitaryGamma_eq b hf hf]
  unfold specialUnitaryLaplacian
  simp_rw [htwice]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- The logarithmic carré du champ is the Fisher-information density. -/
theorem specialUnitaryGamma_log_left
    (b : ι → specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (h0 : ∀ U, f U ≠ 0) (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryGamma b (Real.log ∘ f) f U = specialUnitaryGamma b f f U / f U := by
  rw [specialUnitaryGamma_eq b (specialUnitary_log_contMDiff hf h0) hf,
    specialUnitaryGamma_eq b hf hf]
  simp_rw [specialUnitaryDeriv_log _ U (hf.mdifferentiableAt (by decide)) (h0 U)]
  simp only [div_mul_eq_mul_div, Finset.sum_div]

/-- The logarithmic diffusion chain rule with its exact negative quadratic term. -/
theorem specialUnitaryLaplacian_log
    (b : ι → specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (h0 : ∀ U, f U ≠ 0) (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryLaplacian b (Real.log ∘ f) U =
      specialUnitaryLaplacian b f U / f U - specialUnitaryGamma b f f U / (f U) ^ 2 := by
  have h := specialUnitaryLaplacian_comp b hf (φ := Real.log) (φ' := Inv.inv)
    (φ'' := fun x : ℝ => -(x ^ 2)⁻¹)
    (fun V => Real.hasDerivAt_log (h0 V))
    (fun V => hasDerivAt_inv (h0 V))
    (fun V => contDiffAt_inv ℝ (h0 V)) U
  simpa only [div_eq_mul_inv, sub_eq_add_neg, neg_mul, mul_neg, mul_comm] using h

/-- Squared logarithmic gradient, expressed using the original carré du champ. -/
theorem specialUnitaryGamma_log
    (b : ι → specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (h0 : ∀ U, f U ≠ 0) (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryGamma b (Real.log ∘ f) (Real.log ∘ f) U =
      specialUnitaryGamma b f f U / (f U) ^ 2 := by
  rw [specialUnitaryGamma_eq b (specialUnitary_log_contMDiff hf h0)
    (specialUnitary_log_contMDiff hf h0), specialUnitaryGamma_eq b hf hf]
  simp_rw [specialUnitaryDeriv_log _ U (hf.mdifferentiableAt (by decide)) (h0 U)]
  simp only [← pow_two, div_pow, Finset.sum_div]

/-- Haar integration by parts gives the exact logarithmic energy identity.
For positive `f`, the right side is minus its Fisher information. -/
theorem specialUnitary_integral_log_mul_laplacian
    (b : ι → specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (h0 : ∀ U, f U ≠ 0) :
    (∫ U, Real.log (f U) * specialUnitaryLaplacian b f U ∂specialUnitaryHaar n) =
      -(∫ U, specialUnitaryGamma b f f U / f U ∂specialUnitaryHaar n) := by
  have h := specialUnitary_integral_mul_laplacian b (specialUnitary_log_contMDiff hf h0) hf
  simpa only [Function.comp_apply, specialUnitaryGamma_log_left b hf h0] using h

end LogSobolev
