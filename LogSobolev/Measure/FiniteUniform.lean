module

public import LogSobolev.Measure.Entropy
public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! # Entropy under finite uniform measures

These identities use Mathlib's `ProbabilityTheory.uniformOn Set.univ`.
They connect finite arithmetic averages to the same measure-theoretic entropy
used for Haar and interval probability measures.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LogSobolev

variable {α β : Type*} [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- Integration under the finite uniform measure is the arithmetic average. -/
theorem integral_uniformOn_univ (f : α → ℝ) :
    (∫ x, f x ∂uniformOn (Set.univ : Set α)) = (∑ x, f x) / Fintype.card α := by
  simp [uniformOn, ProbabilityTheory.cond, integral_smul_measure, Measure.count_univ,
    ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]

/-- Entropy under the finite uniform probability is the usual finite formula. -/
theorem entropy_uniformOn_univ (g : α → ℝ) :
    entropy (uniformOn (Set.univ : Set α)) g =
      (∑ x, g x * Real.log (g x)) / Fintype.card α -
        ((∑ x, g x) / Fintype.card α) * Real.log ((∑ x, g x) / Fintype.card α) := by
  simp only [entropy, integral_uniformOn_univ]

/-- Uniform measures on finite sets respect binary products. -/
theorem uniformOn_univ_prod :
    (uniformOn (Set.univ : Set α)).prod (uniformOn (Set.univ : Set β)) =
      uniformOn (Set.univ : Set (α × β)) := by
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  simp [uniformOn_univ, Fintype.card_prod, ENNReal.mul_inv]

/-- A finite bijection preserves uniform measure and hence entropy. -/
theorem entropy_uniformOn_equiv (e : α ≃ β) (g : β → ℝ) :
    entropy (uniformOn (Set.univ : Set α)) (g ∘ e) =
      entropy (uniformOn (Set.univ : Set β)) g := by
  rw [entropy_uniformOn_univ, entropy_uniformOn_univ, Fintype.card_congr e]
  simp only [Function.comp_apply]
  rw [e.sum_comp (fun x => g x * Real.log (g x)), e.sum_comp g]

end LogSobolev
