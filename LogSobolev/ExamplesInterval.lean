module

public import LogSobolev

@[expose] public section

/-! Independent clients of the discrete and C¹ interval entropy bounds. -/

open MeasureTheory LogSobolev

-- Signed data, including zeros, on arbitrarily large dyadic grids.
example (n : ℕ) (f : ℕ → ℝ) :
    uniformGridEntropy (2 ^ n) f ≤
      (2 ^ n : ℕ) / 4 * ∑ i ∈ Finset.range (2 ^ n), (f (i + 1) - f i) ^ 2 :=
  uniformGridEntropy_pow_two_le_unweighted n f

-- The observable t - L/2 is nonconstant and has a zero inside the interval.
example (L : ℝ) (hL : 0 < L) :
    entropy (intervalUniform L) (fun t => ((t : ℝ) - L / 2) ^ 2) ≤ L ^ 2 / 4 := by
  letI : Fact (0 < L) := ⟨hL⟩
  have h := intervalUniform_entropy_sq_le_of_hasDerivAt L hL
    (f := fun t => t - L / 2) (g := fun _ => 1)
    (fun t => (hasDerivAt_id t).sub_const (L / 2)) continuous_const
  simpa using h

-- Integrability for that concrete observable is proved under actual normalized measure.
example (L : ℝ) (hL : 0 < L) :
    Integrable (fun t : Set.Icc (0 : ℝ) L => ((t : ℝ) - L / 2) ^ 2) (intervalUniform L) ∧
    Integrable (fun t : Set.Icc (0 : ℝ) L =>
      ((t : ℝ) - L / 2) ^ 2 * Real.log (((t : ℝ) - L / 2) ^ 2)) (intervalUniform L) := by
  letI : Fact (0 < L) := ⟨hL⟩
  have hc : Continuous (fun t : Set.Icc (0 : ℝ) L => ((t : ℝ) - L / 2) ^ 2) := by fun_prop
  exact ⟨hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
    (Real.continuous_mul_log.comp hc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)⟩

example (L : ℝ) (hL : 0 < L) :
    (0 : ℝ) - L / 2 ≠ L - L / 2 := by linarith
