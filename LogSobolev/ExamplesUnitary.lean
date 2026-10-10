module

public import LogSobolev

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Independent clients of Meckes–Meckes Theorem 15 on the actual matrix U(N). -/
open Matrix MeasureTheory LogSobolev
open scoped Matrix.Norms.Frobenius NNReal ENNReal

example (N : ℕ) (hN : 0 < N) :
    MetricLSI (unitaryHaar (Fin N)) (6 / (N : NNReal)) := unitary_metricLSI N hN

-- The general theorem covers N=1, without a separate caller hypothesis.
example : MetricLSI (unitaryHaar (Fin 1)) 6 := by
  simpa using unitary_metricLSI 1 (by decide)

example (N : ℕ) (hN : 0 < N) (f : Matrix.unitaryGroup (Fin N) ℂ → ℝ)
    (hf : LocallyLipschitz f) :
    entropy (unitaryHaar (Fin N)) (fun U => f U ^ 2) ≤
      (12 / (N : ℝ)) * ∫ U, (localSlope f U).toReal ^ 2 ∂unitaryHaar (Fin N) :=
  unitary_entropy_sq_le_of_locallyLipschitz N hN hf

-- A nonsmooth distance observable with a zero at identity.
example : entropy (unitaryHaar (Fin 2)) (fun U => dist U 1 ^ 2) ≤
    6 * ∫ U, (localSlope (fun V : Matrix.unitaryGroup (Fin 2) ℂ => dist V 1) U).toReal ^ 2
      ∂unitaryHaar (Fin 2) := by
  convert unitary_entropy_sq_le_of_locallyLipschitz 2 (by decide)
    (LipschitzWith.dist_left (1 : Matrix.unitaryGroup (Fin 2) ℂ)).locallyLipschitz using 1; norm_num

-- That distance function is nonconstant on the actual group.
example : dist (negIdentity : Matrix.unitaryGroup (Fin 2) ℂ) 1 ≠
    dist (1 : Matrix.unitaryGroup (Fin 2) ℂ) 1 := by
  rw [dist_self, ne_eq, dist_eq_zero]
  intro h
  have he := congrArg (fun U : Matrix.unitaryGroup (Fin 2) ℂ => U.val 0 0) h
  norm_num [negIdentity] at he

-- A concrete matrix coordinate satisfies the inequality and is not Haar-a.e. constant.
example : entropy (unitaryHaar (Fin 3)) (fun U => entryReal (0 : Fin 3) 0 U ^ 2) ≤
    4 * ∫ U, (localSlope (entryReal (0 : Fin 3) 0) U).toReal ^ 2 ∂unitaryHaar (Fin 3) := by
  convert unitary_entropy_sq_le_of_locallyLipschitz 3 (by decide)
    (entryReal_lipschitz 0 0).locallyLipschitz using 1; norm_num

example (c : ℝ) : ¬ entryReal (0 : Fin 3) 0 =ᵐ[unitaryHaar (Fin 3)] (fun _ => c) :=
  entryReal_not_ae_constant 0 c

-- All integrability obligations are conclusions, rather than assumptions on the test.
example (N : ℕ) (f : Matrix.unitaryGroup (Fin N) ℂ → ℝ) (hf : LocallyLipschitz f) :
    Integrable (fun U => f U ^ 2) (unitaryHaar (Fin N)) ∧
    Integrable (fun U => f U ^ 2 * Real.log (f U ^ 2)) (unitaryHaar (Fin N)) ∧
    Integrable (fun U => (localSlope f U).toReal ^ 2) (unitaryHaar (Fin N)) :=
  unitary_regular hf

example (N : ℕ) (f : Matrix.unitaryGroup (Fin N) ℂ → ℝ) (hf : LocallyLipschitz f) :
    Measurable f ∧ Measurable (localSlope f) ∧ slopeEnergy (unitaryHaar (Fin N)) f ≠ ⊤ := by
  refine ⟨hf.continuous.measurable, measurable_localSlope hf.continuous, ?_⟩
  rw [slopeEnergy_eq_ofReal_integral hf]
  exact ENNReal.ofReal_ne_top

-- Normalized Haar and the unnormalized matrix metric are the actual structures used.
example (N : ℕ) : IsProbabilityMeasure (unitaryHaar (Fin N)) := inferInstance
example (N : ℕ) : Measure.IsHaarMeasure (unitaryHaar (Fin N)) := inferInstance
example (N : ℕ) (U V : Matrix.unitaryGroup (Fin N) ℂ) :
    dist U V = ‖(U : Matrix (Fin N) (Fin N) ℂ) - V‖ := by
  simp only [Subtype.dist_eq, dist_eq_norm]
example (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    ((‖A‖ ^ 2 : ℝ) : ℂ) = Matrix.trace (star A * A) := frobenius_norm_sq_eq_trace A
