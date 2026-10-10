module

public import LogSobolev.Measure.Entropy
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Logarithmic Sobolev inequalities with specified energy

This is an abstract transport API, not a proof that any particular group has LSI.
Both the test-function class and energy are explicit parameters. All applications
require square and log-moment integrability, so totalized integrals cannot create
a spurious entropy bound from a divergent log moment.
-/

open MeasureTheory

namespace LogSobolev

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Finite-entropy LSI on a specified class and energy, in the `2C` convention.
The nonnegative constant is allowed to be zero for degenerate spaces. -/
def HasEnergyLSI (μ : Measure X) (Test : (X → ℝ) → Prop)
    (energy : (X → ℝ) → ℝ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ f, Test f → Integrable (fun x => f x ^ 2) μ →
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ →
    entropy μ (fun x => f x ^ 2) ≤ 2 * C * energy f

/-- Enlarging a nonnegative LSI constant preserves the bound when energy is nonnegative. -/
theorem HasEnergyLSI.mono {μ : Measure X} {Test : (X → ℝ) → Prop}
    {energy : (X → ℝ) → ℝ} {C D : ℝ} (h : HasEnergyLSI μ Test energy C)
    (hCD : C ≤ D) (he : ∀ f, Test f → 0 ≤ energy f) :
    HasEnergyLSI μ Test energy D := by
  refine ⟨h.1.trans hCD, fun f hf hi hl => (h.2 f hf hi hl).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCD (by norm_num)) (he f hf)

/-- Transport LSI along a measurable map with a proved pullback energy estimate.
For a `K`-Lipschitz map the intended value of `a` is `K²`. The test-class and
energy hypotheses are explicit: this theorem does not assume or supply an LSI
on the target space. -/
theorem HasEnergyLSI.map {μ : Measure X} {T : X → Y} (hT : Measurable T)
    {TestX : (X → ℝ) → Prop} {TestY : (Y → ℝ) → Prop}
    {EX : (X → ℝ) → ℝ} {EY : (Y → ℝ) → ℝ} {C a : ℝ}
    (h : HasEnergyLSI μ TestX EX C) (ha : 0 ≤ a)
    (hTest : ∀ f, TestY f → TestX (f ∘ T))
    (hEnergy : ∀ f, TestY f → EX (f ∘ T) ≤ a * EY f) :
    HasEnergyLSI (Measure.map T μ) TestY EY (a * C) := by
  refine ⟨mul_nonneg ha h.1, ?_⟩
  intro f hf hi hl
  have hs := h.2 (f ∘ T) (hTest f hf) (hi.comp_measurable hT) (hl.comp_measurable hT)
  rw [entropy_map μ hT hi.aestronglyMeasurable]
  calc
    _ ≤ 2 * C * EX (f ∘ T) := hs
    _ ≤ 2 * C * (a * EY f) :=
      mul_le_mul_of_nonneg_left (hEnergy f hf) (mul_nonneg (by norm_num) h.1)
    _ = 2 * (a * C) * EY f := by ring

/-- Scaling an explicit energy by a positive factor divides the LSI constant by that factor. -/
theorem HasEnergyLSI.scale_energy {μ : Measure X} {Test : (X → ℝ) → Prop}
    {E : (X → ℝ) → ℝ} {C a : ℝ} (h : HasEnergyLSI μ Test E C) (ha : 0 < a) :
    HasEnergyLSI μ Test (fun f => a * E f) (C / a) := by
  refine ⟨div_nonneg h.1 ha.le, fun f hf hi hl => ?_⟩
  convert h.2 f hf hi hl using 1
  field_simp

end LogSobolev
