module

public import LogSobolev.Analysis.UnitIntervalLSI
public import LogSobolev.Analysis.LipschitzIntervalEnergy

@[expose] public section

/-! # Unit-interval entropy bound for Lipschitz observables

The dyadic argument extends to Lipschitz functions through the fundamental
theorem for absolutely continuous functions. No smoothing or differentiability
at every point is assumed.
-/

open MeasureTheory Filter Finset
open scoped NNReal

namespace LogSobolev

/-- Unit-interval derivative-energy LSI for every globally Lipschitz real function. -/
theorem unitInterval_entropy_sq_le_of_lipschitzWith {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    entropy (volume.restrict (Set.Icc (0 : ℝ) 1)) (fun x => f x ^ 2) ≤
      (1 / 4 : ℝ) * ∫ x in (0 : ℝ)..1, deriv f x ^ 2 := by
  apply le_of_tendsto (tendsto_uniformGridEntropy_samples hf.continuous)
  apply Eventually.of_forall
  intro n
  have hm : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  have hmR : (0 : ℝ) < (2 ^ n : ℕ) := by exact_mod_cast hm
  calc
    _ ≤ (2 ^ n : ℕ) / 4 *
        ∑ i ∈ range (2 ^ n),
          (f (((i + 1 : ℕ) : ℝ) / (2 ^ n : ℕ)) - f ((i : ℝ) / (2 ^ n : ℕ))) ^ 2 :=
      uniformGridEntropy_pow_two_le_unweighted n (fun i => f ((i : ℝ) / (2 ^ n : ℕ)))
    _ ≤ (2 ^ n : ℕ) / 4 * ((1 / (2 ^ n : ℕ)) * ∫ x in (0 : ℝ)..1, deriv f x ^ 2) :=
      mul_le_mul_of_nonneg_left (sum_sq_uniform_increments_le_of_lipschitz (2 ^ n) hm hf)
        (by positivity)
    _ = _ := by field_simp

end LogSobolev
