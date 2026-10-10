import LogSobolev.Geometry.CompactEvolutionMaximum
import LogSobolev.Unitary.SpecialUnitaryMaximumPrinciple

/-! # Preservation of bounds by supplied SU heat solutions

Jointly continuous classical solutions of the actual invariant heat equation
preserve their initial lower and upper bounds. Positivity is a conclusion here,
not an assumption. The proofs use the verified compact-space maximum principle
and the verified sign of the SU Laplacian at spatial extrema. Construction of
such heat solutions remains a separate obligation.
-/

open Matrix Filter Set
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

/-- Initial lower bounds are preserved by the actual SU heat equation. -/
theorem specialUnitary_heat_lower_bound
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {F Q : ℝ → Matrix.specialUnitaryGroup n ℂ → ℝ} {T c : ℝ}
    (hT : 0 ≤ T) (hF : Continuous (Function.uncurry F))
    (hf : ∀ t ∈ Ioc 0 T,
      ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ (F t))
    (hd : ∀ t ∈ Ioc 0 T, ∀ U, HasDerivAt (fun r => F r U) (Q t U) t)
    (hheat : ∀ t ∈ Ioc 0 T, Q t = specialUnitaryLaplacian b (F t))
    (hinit : ∀ U, c ≤ F 0 U) : ∀ U, c ≤ F T U := by
  have h := nonneg_of_compact_minimum_principle
    (F := fun t U => F t U - c) (Q := Q) hT
    (hF.sub continuous_const)
    (fun t ht U => (hd t ht U).sub_const c) ?_ (fun U => sub_nonneg.mpr (hinit U))
  · exact fun U => sub_nonneg.mp (h U)
  · intro t ht U hm
    have hm' : IsLocalMin (F t) U := Eventually.of_forall fun V =>
      (sub_le_sub_iff_right c).mp (hm V)
    rw [hheat t ht]
    exact specialUnitary_laplacian_nonneg_at_min b (hf t ht) hm'

/-- Initial upper bounds are preserved by the actual SU heat equation. -/
theorem specialUnitary_heat_upper_bound
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {F Q : ℝ → Matrix.specialUnitaryGroup n ℂ → ℝ} {T c : ℝ}
    (hT : 0 ≤ T) (hF : Continuous (Function.uncurry F))
    (hf : ∀ t ∈ Ioc 0 T,
      ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ (F t))
    (hd : ∀ t ∈ Ioc 0 T, ∀ U, HasDerivAt (fun r => F r U) (Q t U) t)
    (hheat : ∀ t ∈ Ioc 0 T, Q t = specialUnitaryLaplacian b (F t))
    (hinit : ∀ U, F 0 U ≤ c) : ∀ U, F T U ≤ c := by
  have h := nonneg_of_compact_minimum_principle
    (F := fun t U => c - F t U) (Q := fun t U => -Q t U) hT
    (continuous_const.sub hF)
    (fun t ht U => (hd t ht U).const_sub c) ?_ (fun U => sub_nonneg.mpr (hinit U))
  · exact fun U => sub_nonneg.mp (h U)
  · intro t ht U hm
    have hm' : IsLocalMax (F t) U := Eventually.of_forall fun V =>
      (sub_le_sub_iff_left c).mp (hm V)
    change 0 ≤ -Q t U
    rw [hheat t ht]
    exact neg_nonneg.mpr (specialUnitary_laplacian_nonpos_at_max b (hf t ht) hm')

/-- Nonnegative initial data remain nonnegative; positivity is not an input hypothesis on the flow. -/
theorem specialUnitary_heat_nonneg
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {F Q : ℝ → Matrix.specialUnitaryGroup n ℂ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hF : Continuous (Function.uncurry F))
    (hf : ∀ t ∈ Ioc 0 T,
      ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ (F t))
    (hd : ∀ t ∈ Ioc 0 T, ∀ U, HasDerivAt (fun r => F r U) (Q t U) t)
    (hheat : ∀ t ∈ Ioc 0 T, Q t = specialUnitaryLaplacian b (F t))
    (hinit : ∀ U, 0 ≤ F 0 U) : ∀ U, 0 ≤ F T U :=
  specialUnitary_heat_lower_bound b hT hF hf hd hheat hinit

end LogSobolev
