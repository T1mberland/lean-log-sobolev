import LogSobolev.Unitary.CircleDecomposition
import LogSobolev.Unitary.ProductDomain
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Periodicity of the SU-averaged phase distribution

Although the matrix phase map itself is not periodic with the short interval
length in Meckes–Meckes, its distribution after averaging over SU Haar is.
The proof uses invariance under the central Nth root of unity, not an assumed
Haar decomposition. Integrals over translates of a short period consequently
agree.
-/

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

/-- The SU-Haar mixture at a fixed phase coordinate. -/
noncomputable def phaseSliceMeasure (N : ℕ) (t : ℝ) :
    Measure (Matrix.unitaryGroup (Fin N) ℂ) :=
  Measure.map (fun V : Matrix.specialUnitaryGroup (Fin N) ℂ =>
    circleSpecialUnitaryMap (Circle.exp (Real.sqrt (2 / (N : ℝ)) * t), V))
    (specialUnitaryHaar (Fin N))

/-- The short-interval phase increment has determinant one. -/
theorem phaseInterval_root (N : ℕ) (hN : 0 < N) :
    Circle.exp (Real.sqrt (2 / (N : ℝ)) * phaseIntervalLength N) ^ N = 1 := by
  rw [← Circle.exp_natCast_mul]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs := Real.sq_sqrt (show 0 ≤ 2 / (N : ℝ) by positivity)
  have he : (N : ℝ) * (Real.sqrt (2 / (N : ℝ)) * phaseIntervalLength N) =
      2 * Real.pi := by
    unfold phaseIntervalLength
    calc
      _ = Real.pi * ((N : ℝ) * Real.sqrt (2 / (N : ℝ)) ^ 2) := by ring
      _ = 2 * Real.pi := by rw [hs, mul_div_cancel₀ _ hNr]; ring
  rw [he, Circle.exp_two_pi]

/-- Distributional periodicity with the exact short interval of the paper. -/
theorem phaseSliceMeasure_periodic (N : ℕ) (hN : 0 < N) :
    Function.Periodic (phaseSliceMeasure N) (phaseIntervalLength N) := by
  intro t
  unfold phaseSliceMeasure
  simp only [mul_add, Circle.exp_add]
  apply map_circleSpecialUnitaryMap_mul_root
  simpa using phaseInterval_root N hN

/-- The scalar-circle and original matrix-phase formulas agree exactly. -/
theorem circleSpecialUnitaryMap_exp (N : ℕ) (t : ℝ)
    (V : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    circleSpecialUnitaryMap (Circle.exp (Real.sqrt (2 / (N : ℝ)) * t), V) =
      phaseMap N (WithLp.toLp 2 (t, V)) := by
  apply Subtype.ext
  change Complex.exp (((Real.sqrt (2 / (N : ℝ)) * t : ℝ) : ℂ) * Complex.I) • V.val =
    Complex.exp (Complex.I * ((Real.sqrt (2 / (N : ℝ)) * t : ℝ) : ℂ)) • V.val
  rw [mul_comm]

/-- The average of a measurable observable over SU is short-periodic. -/
theorem phaseAverage_periodic (N : ℕ) (hN : 0 < N)
    (f : Matrix.unitaryGroup (Fin N) ℂ → ℝ) (hf : Measurable f) :
    Function.Periodic (fun t => ∫ V, f (phaseMap N (WithLp.toLp 2 (t, V)))
      ∂specialUnitaryHaar (Fin N)) (phaseIntervalLength N) := by
  have he (t : ℝ) : (∫ U, f U ∂phaseSliceMeasure N t) =
      ∫ V, f (phaseMap N (WithLp.toLp 2 (t, V))) ∂specialUnitaryHaar (Fin N) := by
    unfold phaseSliceMeasure
    rw [integral_map]
    · simp only [circleSpecialUnitaryMap_exp]
    · exact (circleSpecialUnitaryMap_continuous.comp
        (continuous_const.prodMk continuous_id)).measurable.aemeasurable
    · exact hf.aestronglyMeasurable
  intro t
  dsimp only
  rw [← he, ← he, phaseSliceMeasure_periodic N hN t]

/-- Translating the phase integration window by any real amount preserves
its SU-averaged integral. No LSI assumption is involved. -/
theorem phaseAverage_intervalIntegral_translate (N : ℕ) (hN : 0 < N)
    (f : Matrix.unitaryGroup (Fin N) ℂ → ℝ) (hf : Measurable f) (s t : ℝ) :
    (∫ x in s..s + phaseIntervalLength N,
      ∫ V, f (phaseMap N (WithLp.toLp 2 (x, V))) ∂specialUnitaryHaar (Fin N)) =
    ∫ x in t..t + phaseIntervalLength N,
      ∫ V, f (phaseMap N (WithLp.toLp 2 (x, V))) ∂specialUnitaryHaar (Fin N) :=
  (phaseAverage_periodic N hN f hf).intervalIntegral_add_eq s t

end LogSobolev
