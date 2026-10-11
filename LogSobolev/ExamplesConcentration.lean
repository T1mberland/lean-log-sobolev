module

public import LogSobolev

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Independent clients of the shared Herbst and concentration API.
The norm and distance examples are nonsmooth and nonconstant. -/

open MeasureTheory ProbabilityTheory LogSobolev
open scoped Matrix.Norms.Frobenius NNReal

-- An abstract compact metric probability space, with no group structure.
example {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {C K : ℝ≥0} (h : MetricLSI μ C) {f : X → ℝ} (hf : LipschitzWith K f) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂μ) (C * K ^ 2) μ :=
  h.hasSubgaussianMGF_of_compact hf

-- A concrete nonconstant coordinate on U(3), with variance proxy 2.
example : HasSubgaussianMGF
    (fun U => entryReal (0 : Fin 3) 0 U - ∫ V, entryReal (0 : Fin 3) 0 V ∂unitaryHaar (Fin 3))
    2 (unitaryHaar (Fin 3)) := by
  convert unitary_hasSubgaussianMGF 3 (by decide) (entryReal_lipschitz 0 0) using 1; norm_num

example (c : ℝ) : ¬ entryReal (0 : Fin 3) 0 =ᵐ[unitaryHaar (Fin 3)] (fun _ => c) :=
  entryReal_not_ae_constant 0 c

-- Nonsmooth distance on U(1); the positive-dimensional endpoint is included.
example {r : ℝ} (hr : 0 ≤ r) :
    (unitaryHaar (Fin 1)).real {U | r ≤ |dist U 1 - ∫ V, dist V 1 ∂unitaryHaar (Fin 1)|} ≤
      2 * Real.exp (-r ^ 2 / 12) := by
  convert unitary_measure_abs_ge_le 1 (by decide)
    (LipschitzWith.dist_left (1 : Matrix.unitaryGroup (Fin 1) ℂ)) hr using 1; norm_num

-- SU(2) has variance proxy 1 for its distance observable.
example : HasSubgaussianMGF
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      dist U 1 - ∫ V, dist V 1 ∂specialUnitaryHaar (Fin 2)) 1 (specialUnitaryHaar (Fin 2)) := by
  simpa using specialUnitary_hasSubgaussianMGF 2 (by decide)
    (LipschitzWith.dist_left (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))

-- Euclidean norm, nonsmooth at zero, in arbitrary dimension.
example (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (standardGaussian n).real {x | r ≤ |‖x‖ - ∫ y, ‖y‖ ∂standardGaussian n|} ≤
      2 * Real.exp (-r ^ 2 / 2) := by
  simpa using gaussian_measure_abs_ge_le
    (lipschitzWith_one_norm : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖)) hr

-- This Gaussian observable is nonconstant in positive dimension.
example : (fun x : EuclideanSpace ℝ (Fin 1) => ‖x‖) 0 ≠
    (fun x : EuclideanSpace ℝ (Fin 1) => ‖x‖) (EuclideanSpace.single 0 1) := by
  simp [EuclideanSpace.single]

-- Lower tails use the same sharp, dimension-free variance proxy.
example (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (standardGaussian n).real {x | r ≤ (∫ y, ‖y‖ ∂standardGaussian n) - ‖x‖} ≤
      Real.exp (-r ^ 2 / 2) := by
  simpa using gaussian_measure_le_le
    (lipschitzWith_one_norm : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖)) hr

-- Zero-dimensional Gaussian space needs no positivity hypothesis.
example {f : EuclideanSpace ℝ (Fin 0) → ℝ} (hf : LipschitzWith 1 f) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂standardGaussian 0) 1 (standardGaussian 0) := by
  simpa using gaussian_hasSubgaussianMGF hf

-- Zero Lipschitz constant has zero variance proxy, not an excluded endpoint.
example (n : ℕ) (a : ℝ) :
    HasSubgaussianMGF (fun _x : EuclideanSpace ℝ (Fin n) =>
      a - ∫ _ : EuclideanSpace ℝ (Fin n), a ∂standardGaussian n) 0 (standardGaussian n) := by
  simpa using gaussian_hasSubgaussianMGF (LipschitzWith.const a)

-- Explicit centered MGF inequality, rather than only an abstract predicate.
example {n : ℕ} {K : ℝ≥0} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LipschitzWith K f) (t : ℝ) :
    mgf (fun x => f x - ∫ y, f y ∂standardGaussian n) (standardGaussian n) t ≤
      Real.exp ((K : ℝ)^2 * t^2 / 2) :=
  (gaussian_hasSubgaussianMGF hf).mgf_le t
