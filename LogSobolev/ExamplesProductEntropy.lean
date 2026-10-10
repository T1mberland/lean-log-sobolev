import LogSobolev

/-! Independent applications of the entropy subadditivity API. -/

open MeasureTheory LogSobolev
open scoped Matrix.Norms.Frobenius

-- Squared continuous observables may vanish; no log-integrability premise remains.
example {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X × Y → ℝ) (hf : Continuous f) :
    entropy (μ.prod ν) (fun p => f p ^ 2) ≤
      (∫ x, entropy ν (fun y => f (x, y) ^ 2) ∂μ) +
        ∫ y, entropy μ (fun x => f (x, y) ^ 2) ∂ν :=
  entropy_prod_le_integral_entropy_add_of_continuous (hf.pow 2) (fun _ => sq_nonneg _)

-- A joint interval/SU(2) observable with a zero at (0, identity).
example :
    let μ := intervalUniform 1
    let ν := specialUnitaryHaar (Fin 2)
    entropy (μ.prod ν)
      (fun p => ((p.1 : ℝ) + dist p.2 1) ^ 2) ≤
      (∫ t, entropy ν (fun U => ((t : ℝ) + dist U 1) ^ 2) ∂μ) +
        ∫ U, entropy μ (fun t => ((t : ℝ) + dist U 1) ^ 2) ∂ν := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  exact entropy_prod_le_integral_entropy_add_of_continuous
    (by fun_prop) (fun _ => sq_nonneg _)
