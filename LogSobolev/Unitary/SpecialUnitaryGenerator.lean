module

public import LogSobolev.Unitary.SpecialUnitaryDifferentialOperators

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The sum-of-squares differential operator and carré du champ on SU

The operator is constructed from the actual invariant manifold derivatives.
Its carré du champ is defined by the generator product formula and then proved
to equal the sum of squared first derivatives. No heat semigroup, invariant
measure identity, Γ₂ estimate, or logarithmic Sobolev inequality is assumed.
-/

open Matrix
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {f g : Matrix.specialUnitaryGroup n ℂ → ℝ}

/-- Invariant differentiation is additive on smooth tests. -/
theorem specialUnitaryDeriv_add (A : specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ g) :
    specialUnitaryDeriv A (f + g) = specialUnitaryDeriv A f + specialUnitaryDeriv A g := by
  funext U
  exact DFunLike.congr_fun ((hf.mdifferentiableAt (by decide)).hasMFDerivAt.add
    (hg.mdifferentiableAt (by decide)).hasMFDerivAt).mfderiv A

/-- Product rule for the actual invariant derivatives. -/
theorem specialUnitaryDeriv_mul (A : specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ g) :
    specialUnitaryDeriv A (f * g) = f * specialUnitaryDeriv A g + g * specialUnitaryDeriv A f := by
  funext U
  exact DFunLike.congr_fun ((hf.mdifferentiableAt (by decide)).hasMFDerivAt.mul
    (hg.mdifferentiableAt (by decide)).hasMFDerivAt).mfderiv A

/-- The second product rule, needed for the generator identity. -/
theorem specialUnitaryDeriv_twice_mul (A : specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ g)
    (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryDeriv A (specialUnitaryDeriv A (f * g)) U =
      f U * specialUnitaryDeriv A (specialUnitaryDeriv A g) U +
      g U * specialUnitaryDeriv A (specialUnitaryDeriv A f) U +
      2 * specialUnitaryDeriv A f U * specialUnitaryDeriv A g U := by
  have hDf := specialUnitaryDeriv_contMDiff A hf
  have hDg := specialUnitaryDeriv_contMDiff A hg
  rw [specialUnitaryDeriv_mul A hf hg,
    specialUnitaryDeriv_add A (hf.mul hDg) (hg.mul hDf),
    specialUnitaryDeriv_mul A hf hDg, specialUnitaryDeriv_mul A hg hDf]
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

variable {ι : Type*} [Fintype ι]

/-- The actual invariant sum-of-squares operator for a finite family of directions.
An orthonormal basis is supplied when using the Hilbert–Schmidt normalization. -/
noncomputable def specialUnitaryLaplacian (b : ι → specialUnitaryLieAlgebra (n := n))
    (f : Matrix.specialUnitaryGroup n ℂ → ℝ) (U : Matrix.specialUnitaryGroup n ℂ) : ℝ :=
  ∑ i, specialUnitaryDeriv (b i) (specialUnitaryDeriv (b i) f) U

/-- Carré du champ defined by the generator product formula, with its factor `1/2`. -/
noncomputable def specialUnitaryGamma (b : ι → specialUnitaryLieAlgebra (n := n))
    (f g : Matrix.specialUnitaryGroup n ℂ → ℝ) (U : Matrix.specialUnitaryGroup n ℂ) : ℝ :=
  (specialUnitaryLaplacian b (f * g) U - f U * specialUnitaryLaplacian b g U -
    g U * specialUnitaryLaplacian b f U) / 2

/-- The generator preserves smooth tests. -/
theorem specialUnitaryLaplacian_contMDiff (b : ι → specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f) :
    ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ (specialUnitaryLaplacian b f) := by
  apply ContMDiff.sum
  intro i _
  exact specialUnitaryDeriv_contMDiff (b i) (specialUnitaryDeriv_contMDiff (b i) hf)

/-- The generator definition gives the expected first-derivative energy, without assuming it. -/
theorem specialUnitaryGamma_eq (b : ι → specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ g)
    (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryGamma b f g U =
      ∑ i, specialUnitaryDeriv (b i) f U * specialUnitaryDeriv (b i) g U := by
  unfold specialUnitaryGamma specialUnitaryLaplacian
  simp_rw [specialUnitaryDeriv_twice_mul _ hf hg]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
  ring

/-- In particular, carré du champ is nonnegative on smooth tests. -/
theorem specialUnitaryGamma_nonneg (b : ι → specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (U : Matrix.specialUnitaryGroup n ℂ) : 0 ≤ specialUnitaryGamma b f f U := by
  rw [specialUnitaryGamma_eq b hf hf]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

end LogSobolev
