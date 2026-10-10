import LogSobolev

/-! # Independent usage examples

These examples validate geometry, normalization and nonconstant admissible
functions. They do not claim an LSI on U(N).
-/

open LogSobolev Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

example : unitaryHaar (Fin 1) Set.univ = 1 := measure_univ
example : unitaryHaar (Fin 3) Set.univ = 1 := measure_univ
example : specialUnitaryHaar (Fin 3) Set.univ = 1 := measure_univ

example : intervalUniform Real.pi Set.univ = 1 := intervalUniform_univ _ Real.pi_pos

example : IsProbabilityMeasure (phaseDomainMeasure 2) :=
  phaseDomainMeasure_probability 2 (by decide)

example : ‖(1 : Matrix (Fin 3) (Fin 3) ℂ)‖ = Real.sqrt 3 := by
  simpa using unitary_norm (1 : Matrix.unitaryGroup (Fin 3) ℂ)

example (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ((‖A‖ ^ 2 : ℝ) : ℂ) = Matrix.trace (star A * A) := frobenius_norm_sq_eq_trace A

example : LipschitzWith ⟨Real.sqrt 3, Real.sqrt_nonneg 3⟩ (phaseMap 1) :=
  phaseMap_lipschitz 1 (by decide)

example : LipschitzWith ⟨Real.sqrt 3, Real.sqrt_nonneg 3⟩ (phaseMap 4) :=
  phaseMap_lipschitz 4 (by decide)

example : LipschitzWith ⟨Real.sqrt 3, Real.sqrt_nonneg 3⟩ (intervalPhaseMap 2) :=
  intervalPhaseMap_lipschitz 2 (by decide)

example (N : ℕ) (hN : 0 < N) (c : ℝ) :
    ¬ entryReal (⟨0, hN⟩ : Fin N) ⟨0, hN⟩ =ᵐ[unitaryHaar (Fin N)] (fun _ => c) :=
  entryReal_not_ae_constant _ c

example : Integrable (fun U : Matrix.unitaryGroup (Fin 2) ℂ =>
    (localSlope (entryReal 0 0) U).toReal ^ 2) (unitaryHaar (Fin 2)) :=
  (unitary_regular (entryReal_lipschitz 0 0).locallyLipschitz).2.2

-- The transfer theorem is conditional on a source LSI, with that assumption visible.
example {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : Measure X) {T : X → Y} (hT : LipschitzWith 2 T)
    (h : MetricLSI μ 3) : MetricLSI (Measure.map T μ) 12 := by
  convert h.map hT using 1
  norm_num
