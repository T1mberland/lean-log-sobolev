/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
Ported from AI4SLT d0f506f0a695018265dccb33bcb05e2f5ca1c876.
Modified for Lean 4.28.0 and the shared LogSobolev entropy/two-point API.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-! # Standard Gaussian measures

Selective port of the probability-measure definitions, Euclidean transport,
and coordinate marginals from AI4SLT. Unused MGF and concentration results
and their dependencies are omitted.
-/

open MeasureTheory ProbabilityTheory Real Finset BigOperators

namespace GaussianMeasure

variable {n : ℕ}

/-- Standard Gaussian product measure: the product of n independent standard Gaussians N(0,1) -/
noncomputable def stdGaussianPi (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => gaussianReal 0 1

/-! ## Gaussian Measure Properties -/

/-- `stdGaussianPi` is a probability measure. -/
instance stdGaussianPi_isProbabilityMeasure : IsProbabilityMeasure (stdGaussianPi n) := by
  unfold stdGaussianPi
  infer_instance

/-- `stdGaussianPi` is a finite measure. -/
instance stdGaussianPi_isFiniteMeasure : IsFiniteMeasure (stdGaussianPi n) :=
  inferInstance

/-- `stdGaussianPi` is sigma-finite. -/
instance stdGaussianPi_isSigmaFinite : SigmaFinite (stdGaussianPi n) := by
  unfold stdGaussianPi
  infer_instance

/-! ## Standard Gaussian on EuclideanSpace -/

/-- The standard Gaussian on EuclideanSpace as pushforward of stdGaussianPi via the equivalence. -/
noncomputable def stdGaussianE (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  Measure.map (EuclideanSpace.equiv (Fin n) ℝ).symm (stdGaussianPi n)

/-- `stdGaussianE` is a probability measure. -/
instance stdGaussianE_isProbabilityMeasure : IsProbabilityMeasure (stdGaussianE n) := by
  unfold stdGaussianE
  apply MeasureTheory.Measure.isProbabilityMeasure_map
  exact (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.measurable.aemeasurable

/-- Transfer of integrals: integrating f over stdGaussianE equals integrating f ∘ e.symm over stdGaussianPi. -/
lemma integral_stdGaussianE_eq (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ x, f x ∂(stdGaussianE n) = ∫ w, f ((EuclideanSpace.equiv (Fin n) ℝ).symm w) ∂(stdGaussianPi n) := by
  unfold stdGaussianE
  exact integral_map_equiv (EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph.toMeasurableEquiv f

/-! ## Independence and MGF Properties

The key insight is that coordinate projections from `stdGaussianPi n` are independent
standard Gaussians. -/

/-- The coordinate projections from stdGaussianPi are independent -/
lemma iIndepFun_eval_stdGaussianPi :
    iIndepFun (fun i (w : Fin n → ℝ) => w i) (stdGaussianPi n) := by
  unfold stdGaussianPi
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

/-- The pushforward of stdGaussianPi under coordinate projection is gaussianReal 0 1 -/
lemma map_eval_stdGaussianPi (i : Fin n) :
    (stdGaussianPi n).map (fun w => w i) = gaussianReal 0 1 := by
  unfold stdGaussianPi
  exact (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).map_eq


end GaussianMeasure
