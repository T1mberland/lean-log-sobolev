module

public import LogSobolev.Unitary.SpecialUnitaryGeneratorCommutation
public import LogSobolev.Unitary.SpecialUnitarySecondOrder

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The Bakry–Émery Γ₂ estimate for the actual SU differential operator

The iterated carré du champ is defined from the proved sum-of-squares operator
and its generator product formula. Casimir commutation identifies it with the
sum of squared second derivatives. The exact Killing contraction then yields
`Γ₂ ≥ (N/2) Γ` for every smooth real test. This is a differential estimate, not
a curvature-to-LSI theorem or a construction of a heat semigroup.
-/

open Matrix
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Invariant differentiation commutes with finite sums of smooth functions. -/
theorem specialUnitaryDeriv_sum {κ : Type*} [Fintype κ]
    (A : specialUnitaryLieAlgebra (n := n))
    (f : κ → Matrix.specialUnitaryGroup n ℂ → ℝ)
    (hf : ∀ k, ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ (f k)) :
    specialUnitaryDeriv A (∑ k, f k) = ∑ k, specialUnitaryDeriv A (f k) := by
  let F : κ → specialUnitarySmoothFunctions n := fun k => ⟨f k, hf k⟩
  let coeHom : specialUnitarySmoothFunctions n →+ (Matrix.specialUnitaryGroup n ℂ → ℝ) :=
    ContMDiffMap.coeFnAddMonoidHom
  have hs : ⇑(∑ k, F k) = ∑ k, f k := map_sum coeHom F Finset.univ
  calc
    specialUnitaryDeriv A (∑ k, f k) = ⇑(specialUnitaryDerivEnd A (∑ k, F k)) := by
      change specialUnitaryDeriv A (∑ k, f k) = specialUnitaryDeriv A ⇑(∑ k, F k)
      rw [hs]
    _ = ⇑(∑ k, specialUnitaryDerivEnd A (F k)) := by rw [map_sum]
    _ = ∑ k, specialUnitaryDeriv A (f k) :=
      map_sum coeHom (fun k => specialUnitaryDerivEnd A (F k)) Finset.univ

variable {ι : Type*} [Fintype ι]

/-- The constructed generator commutes with finite sums on its smooth test space. -/
theorem specialUnitaryLaplacian_sum {κ : Type*} [Fintype κ]
    (b : ι → specialUnitaryLieAlgebra (n := n))
    (f : κ → Matrix.specialUnitaryGroup n ℂ → ℝ)
    (hf : ∀ k, ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ (f k)) :
    specialUnitaryLaplacian b (∑ k, f k) = ∑ k, specialUnitaryLaplacian b (f k) := by
  funext U
  unfold specialUnitaryLaplacian
  simp_rw [specialUnitaryDeriv_sum _ f hf]
  simp_rw [specialUnitaryDeriv_sum _ _ (fun k => specialUnitaryDeriv_contMDiff _ (hf k))]
  simp only [Finset.sum_apply]
  exact Finset.sum_comm

/-- Product formula rearranged directly from the generator definition of carré du champ. -/
theorem specialUnitaryLaplacian_mul (b : ι → specialUnitaryLieAlgebra (n := n))
    (f g : Matrix.specialUnitaryGroup n ℂ → ℝ) (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryLaplacian b (f * g) U =
      f U * specialUnitaryLaplacian b g U + g U * specialUnitaryLaplacian b f U +
        2 * specialUnitaryGamma b f g U := by
  unfold specialUnitaryGamma
  ring

/-- The genuine iterated carré du champ of the constructed operator, with its standard factor. -/
noncomputable def specialUnitaryGammaTwo (b : ι → specialUnitaryLieAlgebra (n := n))
    (f : Matrix.specialUnitaryGroup n ℂ → ℝ) (U : Matrix.specialUnitaryGroup n ℂ) : ℝ :=
  (specialUnitaryLaplacian b (specialUnitaryGamma b f f) U -
    2 * specialUnitaryGamma b f (specialUnitaryLaplacian b f) U) / 2

/-- Casimir commutation proves the Γ₂ identity for the actual differential operator. -/
theorem specialUnitaryGammaTwo_eq
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryGammaTwo b f U =
      ∑ i, ∑ j, (specialUnitaryDeriv (b i) (specialUnitaryDeriv (b j) f) U) ^ 2 := by
  have hD i := specialUnitaryDeriv_contMDiff (b i) hf
  have hG : specialUnitaryGamma b f f =
      ∑ i, specialUnitaryDeriv (b i) f * specialUnitaryDeriv (b i) f := by
    funext V
    simpa only [Finset.sum_apply, Pi.mul_apply] using specialUnitaryGamma_eq b hf hf V
  have hL : specialUnitaryLaplacian b (specialUnitaryGamma b f f) U =
      2 * (∑ i, specialUnitaryDeriv (b i) f U *
        specialUnitaryDeriv (b i) (specialUnitaryLaplacian b f) U) +
      2 * (∑ i, ∑ j, (specialUnitaryDeriv (b j) (specialUnitaryDeriv (b i) f) U) ^ 2) := by
    rw [hG, specialUnitaryLaplacian_sum b _ (fun i => (hD i).mul (hD i))]
    simp only [Finset.sum_apply]
    calc
      _ = ∑ i, (2 * (specialUnitaryDeriv (b i) f U *
          specialUnitaryDeriv (b i) (specialUnitaryLaplacian b f) U) +
          2 * ∑ j, (specialUnitaryDeriv (b j) (specialUnitaryDeriv (b i) f) U) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [specialUnitaryLaplacian_mul, specialUnitaryLaplacian_deriv b (b i) hf,
          specialUnitaryGamma_eq b (hD i) (hD i)]
        simp only [pow_two]
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]
  unfold specialUnitaryGammaTwo
  rw [hL, specialUnitaryGamma_eq b hf (specialUnitaryLaplacian_contMDiff b hf)]
  have hs : (∑ i, ∑ j, (specialUnitaryDeriv (b j) (specialUnitaryDeriv (b i) f) U) ^ 2) =
      ∑ i, ∑ j, (specialUnitaryDeriv (b i) (specialUnitaryDeriv (b j) f) U) ^ 2 :=
    Finset.sum_comm
  rw [hs]
  ring

/-- The exact `N/2` Bakry–Émery differential estimate, with no curvature or LSI hypothesis. -/
theorem specialUnitaryGammaTwo_lower_bound
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (U : Matrix.specialUnitaryGroup n ℂ) :
    (Fintype.card n : ℝ) / 2 * specialUnitaryGamma b f f U ≤ specialUnitaryGammaTwo b f U := by
  rw [specialUnitaryGammaTwo_eq b hf, specialUnitaryGamma_eq b hf hf]
  simp only [← pow_two]
  exact specialUnitary_second_derivative_energy_lower_bound b hf.contMDiffAt

end LogSobolev
