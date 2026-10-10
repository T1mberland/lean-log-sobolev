import LogSobolev.Unitary.SpecialUnitaryChainRules

/-! # Energy of a regularized square on SU

The actual invariant derivatives give `Γ(f²+ε) = 4 f² Γ(f)`. Consequently
`Γ(f²+ε)/(f²+ε) ≤ 4 Γ(f)` for positive ε. This is the normalization needed to
pass from a positive-density entropy bound to the usual squared-function LSI.
-/

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

/-- The invariant derivative of a regularized square. -/
theorem specialUnitaryDeriv_sq_add_const
    (A : specialUnitaryLieAlgebra (n := n))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (ε : ℝ) (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryDeriv A (fun V => f V ^ 2 + ε) U = 2 * f U * specialUnitaryDeriv A f U := by
  have h := specialUnitaryDeriv_comp A U (hf.mdifferentiableAt (by decide))
    (((hasDerivAt_id (f U)).pow 2).add_const ε)
  simpa using h

/-- Carré du champ of a regularized square, with the exact factor four. -/
theorem specialUnitaryGamma_sq_add_const
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (ε : ℝ) (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryGamma b (fun V => f V ^ 2 + ε) (fun V => f V ^ 2 + ε) U =
      4 * f U ^ 2 * specialUnitaryGamma b f f U := by
  have hs : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞
      (fun V => f V ^ 2 + ε) := (hf.pow 2).add contMDiff_const
  rw [specialUnitaryGamma_eq b hs hs, specialUnitaryGamma_eq b hf hf]
  simp_rw [specialUnitaryDeriv_sq_add_const _ hf ε]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Fisher density of a positive regularized square is bounded by four times its energy. -/
theorem specialUnitary_fisher_sq_add_const_le
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    {ε : ℝ} (hε : 0 < ε) (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryGamma b (fun V => f V ^ 2 + ε) (fun V => f V ^ 2 + ε) U /
      (f U ^ 2 + ε) ≤ 4 * specialUnitaryGamma b f f U := by
  rw [specialUnitaryGamma_sq_add_const b hf ε]
  apply (div_le_iff₀ (add_pos_of_nonneg_of_pos (sq_nonneg _) hε)).mpr
  nlinarith [mul_nonneg hε.le (specialUnitaryGamma_nonneg b hf U)]

end LogSobolev
