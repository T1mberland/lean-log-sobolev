import LogSobolev.Analysis.DyadicLSI
import LogSobolev.Analysis.UniformGridLimit
import LogSobolev.Analysis.IntervalSquareIncrement

/-! # A one-dimensional logarithmic Sobolev bound

For a real continuously differentiable function on the line, its restriction
to the unit interval satisfies `Ent(f²) ≤ (1/4) ∫ f'²`. Thus the LSI constant
in the `2C` convention is `1/8`. This is a proved, nonoptimal interval bound;
the sharp constant `1/π²` is not asserted.

The proof uses the sharp two-point inequality, exact dyadic path weights,
Riemann-sum convergence for continuous integrands (including `f² log f²` at
zeros), and a verified squared-increment energy bound.
-/

open MeasureTheory Filter Finset
open scoped Topology

namespace LogSobolev

/-- Finite-sample squared entropy in terms of two ordinary sample averages. -/
theorem uniformGridEntropy_samples_eq (m : ℕ) (f : ℝ → ℝ) :
    uniformGridEntropy m (fun i => f ((i : ℝ) / m)) =
      uniformGridAverage m (fun x => f x ^ 2 * Real.log (f x ^ 2)) -
        uniformGridAverage m (fun x => f x ^ 2) *
          Real.log (uniformGridAverage m (fun x => f x ^ 2)) := by
  rw [uniformGridEntropy, entropy_uniformOn_univ]
  simp only [Fintype.card_fin]
  rw [← Finset.sum_range (fun i : ℕ => f ((i : ℝ) / m) ^ 2 * Real.log (f ((i : ℝ) / m) ^ 2)),
    ← Finset.sum_range (fun i : ℕ => f ((i : ℝ) / m) ^ 2)]
  rfl

/-- Dyadic sampled entropy converges to actual unit-interval entropy, even at zeros. -/
theorem tendsto_uniformGridEntropy_samples {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto (fun n => uniformGridEntropy (2 ^ n) (fun i => f ((i : ℝ) / (2 ^ n : ℕ))))
      atTop (𝓝 (entropy (volume.restrict (Set.Icc (0 : ℝ) 1)) (fun x => f x ^ 2))) := by
  have h1 := tendsto_uniformGridAverage_pow_two (hf.pow 2)
  have h2 := tendsto_uniformGridAverage_pow_two (Real.continuous_mul_log.comp (hf.pow 2))
  have h := h2.sub (Real.continuous_mul_log.continuousAt.tendsto.comp h1)
  simp only [Function.comp_def] at h
  simp only [uniformGridEntropy_samples_eq]
  convert h using 1
  simp only [entropy, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- Unit-interval LSI for continuously differentiable real functions, coefficient `1/4`.
The density may vanish and the observable may change sign. -/
theorem unitInterval_entropy_sq_le_of_hasDerivAt {f g : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g) :
    entropy (volume.restrict (Set.Icc (0 : ℝ) 1)) (fun x => f x ^ 2) ≤
      (1 / 4 : ℝ) * ∫ x in (0 : ℝ)..1, g x ^ 2 := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  apply le_of_tendsto (tendsto_uniformGridEntropy_samples hfc)
  apply Eventually.of_forall
  intro n
  have hm : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  have hmR : (0 : ℝ) < (2 ^ n : ℕ) := by exact_mod_cast hm
  calc
    _ ≤ (2 ^ n : ℕ) / 4 *
        ∑ i ∈ range (2 ^ n),
          (f (((i + 1 : ℕ) : ℝ) / (2 ^ n : ℕ)) - f ((i : ℝ) / (2 ^ n : ℕ))) ^ 2 :=
      uniformGridEntropy_pow_two_le_unweighted n (fun i => f ((i : ℝ) / (2 ^ n : ℕ)))
    _ ≤ (2 ^ n : ℕ) / 4 * ((1 / (2 ^ n : ℕ)) * ∫ x in (0 : ℝ)..1, g x ^ 2) :=
      mul_le_mul_of_nonneg_left (sum_sq_uniform_increments_le (2 ^ n) hm hf hg)
        (by positivity)
    _ = _ := by field_simp

end LogSobolev
