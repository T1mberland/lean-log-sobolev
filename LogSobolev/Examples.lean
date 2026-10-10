import LogSobolev

/-! # Independent usage examples

These examples validate geometry, normalization and nonconstant admissible
functions. They do not claim an LSI on U(N).
-/

open LogSobolev Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius ContDiff

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

-- The exact short interval works in dimension one as well as higher dimensions.
example : Measure.map (intervalPhaseMap 1) (phaseDomainMeasure 1) = unitaryHaar (Fin 1) :=
  map_intervalPhaseMap 1 (by decide)

example : Measure.map (intervalPhaseMap 3) (phaseDomainMeasure 3) = unitaryHaar (Fin 3) :=
  map_intervalPhaseMap 3 (by decide)

example : Measure.map circleSpecialUnitaryMap
    (circleHaar.prod (specialUnitaryHaar (Fin 2))) = unitaryHaar (Fin 2) :=
  map_circleSpecialUnitaryMap (by decide)

-- Only the final transfer is claimed here, with the missing source LSI explicit.
example (h : MetricLSI (phaseDomainMeasure 2) 1) :
    MetricLSI (unitaryHaar (Fin 2)) 3 := by
  convert unitary_metricLSI_of_phaseDomain 2 (by decide) (by simpa using h) using 1
  norm_num

-- The entropy chain rule applies to locally Lipschitz squares on compact products.
example {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    [CompactSpace X] [CompactSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X × Y → ℝ) (hf : LocallyLipschitz f) :
    entropy (μ.prod ν) (fun p => f p ^ 2) =
      (∫ x, entropy ν (fun y => f (x, y) ^ 2) ∂μ) +
        entropy μ (fun x => ∫ y, f (x, y) ^ 2 ∂ν) :=
  entropy_prod_chain (Filter.Eventually.of_forall fun p => sq_nonneg (f p))
    (integrable_sq_of_locallyLipschitz hf) (integrable_sq_log_of_locallyLipschitz hf)

-- This checks the exact dimension coefficient in the SU algebra calculation.
example (A : specialUnitaryLieAlgebra (n := Fin 3)) :
    (∑ i : Fin 3, ∑ j : Fin 3, ‖⁅Matrix.single i j (1 : ℂ), A.val⁆‖ ^ 2) =
      6 * ‖A.val‖ ^ 2 := by
  convert specialUnitary_commutator_energy A using 1
  norm_num

-- A concrete nonzero element of the traceless skew-Hermitian algebra.
example : (Matrix.diagonal ![Complex.I, -Complex.I]) ∈
    (specialUnitaryLieAlgebra : LieSubalgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [mem_specialUnitaryLieAlgebra]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  · simp [Matrix.trace, Fin.sum_univ_two]

example : ‖(Matrix.diagonal ![Complex.I, -Complex.I] :
    Matrix (Fin 2) (Fin 2) ℂ)‖ ^ 2 = 2 := by
  rw [frobenius_norm_sq]
  norm_num [Fin.sum_univ_two, Matrix.diagonal]

-- Every algebra element is realized by an actual SU curve, with the exact speed.
example (A : specialUnitaryLieAlgebra (n := Fin 3)) :
    ∃ γ : ℝ → Matrix.specialUnitaryGroup (Fin 3) ℂ,
      γ 0 = 1 ∧ HasDerivAt (fun t => (γ t).val) A.val 0 :=
  (mem_specialUnitaryLieAlgebra_iff_curve_velocity A.val).mp A.prop

example (A : specialUnitaryLieAlgebra (n := Fin 2)) (t : ℝ) :
    ‖deriv (fun s => (specialUnitaryExpCurve A s).val) t‖ = ‖A.val‖ :=
  specialUnitaryExpCurve_speed A t

-- The determinant lemma also applies to trace-zero matrices that are not skew.
example (t : ℝ) :
    Matrix.det (NormedSpace.exp (t •
      (Matrix.diagonal ![(1 : ℂ), -1] : Matrix (Fin 2) (Fin 2) ℂ))) = 1 := by
  apply det_exp_smul_eq_one_of_trace_zero
  simp [Matrix.trace, Fin.sum_univ_two]

example (A : specialUnitaryLieAlgebra (n := Fin 2)) :
    LipschitzWith ‖A.val‖₊ (specialUnitaryExpCurve A) :=
  specialUnitaryExpCurve_lipschitz A

-- Real orthonormal contractions use the exact unnormalized HS metric.
example (A : specialUnitaryLieAlgebra (n := Fin 3)) :
    inner ℝ A A = ‖A.val‖ ^ 2 := by
  rw [specialUnitaryAlgebra_inner, specialUnitary_negTracePair_self]

example (U : Matrix.unitaryGroup (Fin 3) ℂ)
    (A B : specialUnitaryLieAlgebra (n := Fin 3)) :
    dist (specialUnitaryAdjointIsometry U A) (specialUnitaryAdjointIsometry U B) =
      dist A B := (specialUnitaryAdjointIsometry U).dist_map A B

example (A : specialUnitaryLieAlgebra (n := Fin 2)) :
    killingForm ℝ (specialUnitaryLieAlgebra (n := Fin 2)) A A =
      -(∑ i, ‖⁅A, stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 2)) i⁆‖ ^ 2) :=
  specialUnitary_killing_self _ A

-- The dimension factor now holds for the real Killing form, not only matrix units.
example (A : specialUnitaryLieAlgebra (n := Fin 3)) :
    killingForm ℝ (specialUnitaryLieAlgebra (n := Fin 3)) A A = -6 * ‖A.val‖ ^ 2 := by
  convert specialUnitary_killing_self_eq A using 1
  norm_num

example {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := Fin 3)))
    (A : specialUnitaryLieAlgebra (n := Fin 3)) :
    (∑ i, ‖⁅A, b i⁆‖ ^ 2) = 6 * ‖A‖ ^ 2 := by
  convert specialUnitary_orthonormal_commutator_energy b A using 1
  norm_num

-- A concrete witness rules out vacuity of the Killing calculation.
example : ∃ A : specialUnitaryLieAlgebra (n := Fin 2),
    killingForm ℝ (specialUnitaryLieAlgebra (n := Fin 2)) A A = -8 := by
  have hmem : (Matrix.diagonal ![Complex.I, -Complex.I]) ∈
      (specialUnitaryLieAlgebra : LieSubalgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ)) := by
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
    · simp [Matrix.trace, Fin.sum_univ_two]
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [specialUnitary_killing_self_eq, specialUnitaryAlgebra_norm, frobenius_norm_sq]
  norm_num [Fin.sum_univ_two, Matrix.diagonal]

-- Determinant-exponential identity has no skew or trace-zero hypotheses.
example (A : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix.det (NormedSpace.exp A) = Complex.exp (Matrix.trace A) := det_matrix_exp A

-- Every SU(2) matrix in a genuine open neighborhood of identity has an su generator.
example : ∃ t : Set (Matrix.specialUnitaryGroup (Fin 2) ℂ),
    IsOpen t ∧ 1 ∈ t ∧ ∀ V ∈ t,
      ∃ A : specialUnitaryLieAlgebra (n := Fin 2), NormedSpace.exp A.val = V.val := by
  obtain ⟨s, t, _, _, ht, ht1, e, he⟩ := exists_specialUnitary_exp_homeomorph (n := Fin 2)
  refine ⟨t, ht, ht1, ?_⟩
  intro V hV
  refine ⟨(e.symm ⟨V, hV⟩).val, ?_⟩
  have h := he (e.symm ⟨V, hV⟩)
  simpa only [e.apply_symm_apply] using h.symm

example : ContDiffAt ℝ ∞ (matrixExpLocalHomeomorph (n := Fin 3)).symm 1 :=
  matrixLog_contDiffAt_one ∞
