module

public import LogSobolev.Analysis.TwoPointEntropy
public import LogSobolev.Measure.FiniteUniform
public import LogSobolev.Measure.ProductEntropySubadditivity
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # Dyadic entropy decomposition

The sharp balanced two-point inequality and entropy subadditivity give a
recursive entropy estimate for uniformly sampled real observables. These are
actual finite probability measures, not an assumed interval inequality.
-/

open MeasureTheory ProbabilityTheory

namespace LogSobolev

/-- LSI for the balanced two-point probability, including signed values and zeros. -/
theorem entropy_uniformOn_fin_two_sq_le (f : Fin 2 → ℝ) :
    entropy (uniformOn (Set.univ : Set (Fin 2))) (fun i => f i ^ 2) ≤
      (f 0 - f 1) ^ 2 / 2 := by
  simpa [entropy_uniformOn_univ, Fin.sum_univ_two] using TwoPoint.sq_entropy_le (f 0) (f 1)

/-- Separate the last binary coordinate of a finite array. -/
theorem entropy_uniformOn_prod_fin_two_sq_le (m : ℕ) (hm : 0 < m)
    (f : Fin m × Fin 2 → ℝ) :
    entropy (uniformOn (Set.univ : Set (Fin m × Fin 2))) (fun p => f p ^ 2) ≤
      ((entropy (uniformOn (Set.univ : Set (Fin m))) (fun i => f (i, 0) ^ 2)) +
        entropy (uniformOn (Set.univ : Set (Fin m))) (fun i => f (i, 1) ^ 2)) / 2 +
      (∑ i : Fin m, (f (i, 0) - f (i, 1)) ^ 2) / (2 * m) := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hf : Continuous (fun p : Fin m × Fin 2 => f p ^ 2) := continuous_of_discreteTopology
  have h := entropy_prod_le_integral_entropy_add_of_continuous
    (μ := uniformOn (Set.univ : Set (Fin m)))
    (ν := uniformOn (Set.univ : Set (Fin 2)))
    (g := fun p => f p ^ 2) hf (fun _ => sq_nonneg _)
  rw [uniformOn_univ_prod] at h
  simp only [integral_uniformOn_univ, Fintype.card_fin, Fin.sum_univ_two, Nat.cast_ofNat] at h
  have hs : (∑ i : Fin m, entropy (uniformOn (Set.univ : Set (Fin 2)))
      (fun j => f (i, j) ^ 2)) ≤ ∑ i : Fin m, (f (i, 0) - f (i, 1)) ^ 2 / 2 :=
    Finset.sum_le_sum fun i _ => entropy_uniformOn_fin_two_sq_le (fun j => f (i, j))
  have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  rw [← Finset.sum_div, div_div] at hd
  calc
    _ ≤ _ := h
    _ ≤ _ := by linarith [hd]

/-- Entropy of the first `m` samples of a real sequence, under uniform probability. -/
noncomputable def uniformGridEntropy (m : ℕ) (f : ℕ → ℝ) : ℝ :=
  entropy (uniformOn (Set.univ : Set (Fin m))) (fun i => f i.val ^ 2)

/-- Interleaving the even and odd samples gives the binary entropy recursion. -/
theorem uniformGridEntropy_double_le (m : ℕ) (hm : 0 < m) (f : ℕ → ℝ) :
    uniformGridEntropy (m * 2) f ≤
      (uniformGridEntropy m (fun i => f (i * 2)) +
        uniformGridEntropy m (fun i => f (i * 2 + 1))) / 2 +
      (∑ i : Fin m, (f (i.val * 2) - f (i.val * 2 + 1)) ^ 2) / (2 * m) := by
  have h := entropy_uniformOn_prod_fin_two_sq_le m hm
    (fun p => f (p.1.val * 2 + p.2.val))
  have he := entropy_uniformOn_equiv
    (finProdFinEquiv : Fin m × Fin 2 ≃ Fin (m * 2)) (fun i => f i.val ^ 2)
  have he' : uniformGridEntropy (m * 2) f =
      entropy (uniformOn (Set.univ : Set (Fin m × Fin 2)))
        (fun p => f (p.1.val * 2 + p.2.val) ^ 2) := by
    simpa [uniformGridEntropy, Function.comp_def, finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using he.symm
  rw [he']
  simpa [uniformGridEntropy] using h

end LogSobolev
