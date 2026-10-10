module

public import LogSobolev.Analysis.DyadicEntropy
public import LogSobolev.Analysis.DyadicEnergy

@[expose] public section

/-! # Logarithmic Sobolev bounds on dyadic grids

Uniform probability on `2^n` ordered samples satisfies a weighted path-energy
LSI, proved by binary entropy decomposition and the interleaving energy bound.
The unweighted corollary has the coefficient needed for an interval limit.
-/

open MeasureTheory ProbabilityTheory Finset

namespace LogSobolev

/-- Entropy on a dyadic grid is controlled by its weighted path energy. -/
theorem uniformGridEntropy_pow_two_le (n : ℕ) (f : ℕ → ℝ) :
    uniformGridEntropy (2 ^ n) f ≤ discreteWeightedEnergy (2 ^ n) f / (2 ^ n : ℕ) := by
  induction n generalizing f with
  | zero => simp [uniformGridEntropy, discreteWeightedEnergy]
  | succ n ih =>
    have hm : 0 < 2 ^ n := pow_pos (by decide) _
    have hmR : (0 : ℝ) ≤ (2 ^ n : ℕ) := Nat.cast_nonneg _
    have h := uniformGridEntropy_double_le (2 ^ n) hm f
    rw [← Finset.sum_range (fun i : ℕ => (f (i * 2) - f (i * 2 + 1)) ^ 2)] at h
    rw [pow_succ]
    calc
      _ ≤ _ := h
      _ ≤ ((discreteWeightedEnergy (2 ^ n) (fun i => f (i * 2)) / (2 ^ n : ℕ) +
          discreteWeightedEnergy (2 ^ n) (fun i => f (i * 2 + 1)) / (2 ^ n : ℕ)) / 2) +
          (∑ i ∈ range (2 ^ n), (f (i * 2) - f (i * 2 + 1)) ^ 2) / (2 * (2 ^ n : ℕ)) := by
        exact add_le_add (div_le_div_of_nonneg_right
          (add_le_add (ih _) (ih _)) (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
      _ = (discreteWeightedEnergy (2 ^ n) (fun i => f (i * 2)) +
          discreteWeightedEnergy (2 ^ n) (fun i => f (i * 2 + 1)) +
          (∑ i ∈ range (2 ^ n), (f (i * 2) - f (i * 2 + 1)) ^ 2)) /
          (2 * (2 ^ n : ℕ)) := by ring
      _ ≤ discreteWeightedEnergy (2 ^ n * 2) f / (2 * (2 ^ n : ℕ)) :=
        div_le_div_of_nonneg_right (discreteWeightedEnergy_double_le (2 ^ n) f)
          (mul_nonneg (by norm_num) hmR)
      _ = _ := by push_cast; ring

/-- The path weights are bounded by one quarter of the squared grid size. -/
theorem discreteWeightedEnergy_le_unweighted (m : ℕ) (f : ℕ → ℝ) :
    discreteWeightedEnergy m f ≤
      (m : ℝ) ^ 2 / 4 * ∑ i ∈ range m, (f (i + 1) - f i) ^ 2 := by
  rw [discreteWeightedEnergy, mul_sum]
  apply sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  nlinarith [sq_nonneg ((m : ℝ) - 2 * ((i : ℝ) + 1))]

/-- Unweighted dyadic LSI, suitable for an interval Riemann-sum limit.
The final unused edge is permitted; all samples and signs are arbitrary. -/
theorem uniformGridEntropy_pow_two_le_unweighted (n : ℕ) (f : ℕ → ℝ) :
    uniformGridEntropy (2 ^ n) f ≤
      (2 ^ n : ℕ) / 4 * ∑ i ∈ range (2 ^ n), (f (i + 1) - f i) ^ 2 := by
  have hm : (0 : ℝ) < (2 ^ n : ℕ) := by exact_mod_cast (pow_pos (by decide : 0 < 2) n)
  calc
    _ ≤ discreteWeightedEnergy (2 ^ n) f / (2 ^ n : ℕ) := uniformGridEntropy_pow_two_le n f
    _ ≤ ((2 ^ n : ℕ) : ℝ) ^ 2 / 4 *
        (∑ i ∈ range (2 ^ n), (f (i + 1) - f i) ^ 2) / (2 ^ n : ℕ) :=
      div_le_div_of_nonneg_right (discreteWeightedEnergy_le_unweighted _ f) hm.le
    _ = _ := by field_simp

end LogSobolev
