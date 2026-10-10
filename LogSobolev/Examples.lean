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

open scoped Manifold

-- The atlas is installed on the original matrix group, with the actual su model.
example : IsManifold 𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 2)) ∞
    (Matrix.specialUnitaryGroup (Fin 2) ℂ) := inferInstance

example (U : Matrix.specialUnitaryGroup (Fin 3) ℂ) :
    U ∈ (chartAt (specialUnitaryLieAlgebra (n := Fin 3)) U).source :=
  ChartedSpace.mem_chart_source U

example (U V : Matrix.specialUnitaryGroup (Fin 3) ℂ) :
    ContDiffOn ℝ ∞ ((specialUnitaryChartAt U).symm.trans (specialUnitaryChartAt V))
      ((specialUnitaryChartAt U).symm.trans (specialUnitaryChartAt V)).source :=
  specialUnitary_chart_transition_contDiffOn U V

-- Mathlib's generic Lie-group calculus works on the original SU(3) type.
example : LieGroup 𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 3)) ∞
    (Matrix.specialUnitaryGroup (Fin 3) ℂ) := inferInstance

example (V : Matrix.specialUnitaryGroup (Fin 3) ℂ) :
    ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 3))
      𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 3)) ∞
      (fun U : Matrix.specialUnitaryGroup (Fin 3) ℂ => U * V * U⁻¹) :=
  (contMDiff_id.mul contMDiff_const).mul contMDiff_id.inv

example : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 2))
    𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 2)) ∞
    (fun A : specialUnitaryLieAlgebra (n := Fin 2) => specialUnitaryExpCurve A 1) :=
  specialUnitary_exp_contMDiff

-- Tangent differentiation uses the actual inclusion into Frobenius matrices.
example (U : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (A : specialUnitaryLieAlgebra (n := Fin 2)) :
    mfderiv 𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 2))
      𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ)
      (Subtype.val : Matrix.specialUnitaryGroup (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) U A =
      U.val * A.val := by
  rw [(specialUnitary_val_hasMFDerivAt U).mfderiv]
  rfl

-- Repeated invariant derivatives remain legitimate smooth manifold tests.
example (A B : specialUnitaryLieAlgebra (n := Fin 3))
    {f : Matrix.specialUnitaryGroup (Fin 3) ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 3)) 𝓘(ℝ) ∞ f) :
    ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 3)) 𝓘(ℝ) ∞
      (specialUnitaryDeriv A (specialUnitaryDeriv B f)) :=
  specialUnitaryDeriv_contMDiff A (specialUnitaryDeriv_contMDiff B hf)

-- Concrete noncommuting SU(2) directions detect the sign and nonzero operator bracket.
example : ∃ A B : specialUnitaryLieAlgebra (n := Fin 2),
    (specialUnitaryDeriv A (specialUnitaryDeriv B
      (Subtype.val : Matrix.specialUnitaryGroup (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)) 1 -
     specialUnitaryDeriv B (specialUnitaryDeriv A Subtype.val) 1) 0 1 = 2 * Complex.I := by
  let A : specialUnitaryLieAlgebra (n := Fin 2) :=
    ⟨Matrix.diagonal ![Complex.I, -Complex.I], by
      constructor
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
      · simp [Matrix.trace, Fin.sum_univ_two]⟩
  let B : specialUnitaryLieAlgebra (n := Fin 2) := ⟨!![0, 1; -1, 0], by
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
    · simp [Matrix.trace, Fin.sum_univ_two]⟩
  refine ⟨A, B, ?_⟩
  rw [specialUnitaryDeriv_commutator A B specialUnitary_val_contMDiff.contMDiffAt]
  unfold specialUnitaryDeriv
  rw [(specialUnitary_val_hasMFDerivAt (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)).mfderiv]
  change ((1 : Matrix (Fin 2) (Fin 2) ℂ) *
    (A.val * B.val - B.val * A.val)) 0 1 = 2 * Complex.I
  norm_num [A, B, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal,
    Matrix.vecHead, Matrix.vecTail]
  ring

-- No basis-existence hypothesis: instantiate Mathlib's real orthonormal basis of su(2).
example {f : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ}
    {U : Matrix.specialUnitaryGroup (Fin 2) ℂ}
    (hf : ContMDiffAt 𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 2)) 𝓘(ℝ) ∞ f U) :
    let b := stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 2))
    (∑ i, (specialUnitaryDeriv (b i) f U) ^ 2) ≤
      ∑ i, ∑ j, (specialUnitaryDeriv (b i) (specialUnitaryDeriv (b j) f) U) ^ 2 := by
  simpa using specialUnitary_second_derivative_energy_lower_bound
    (stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 2))) hf

-- The generator-defined carré du champ is strictly positive on a concrete SU(2) test.
example : ∃ A : specialUnitaryLieAlgebra (n := Fin 2),
    ∃ f : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ,
      ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 2)) 𝓘(ℝ) ∞ f ∧
      specialUnitaryGamma (fun _ : Unit => A) f f 1 = 1 := by
  let A : specialUnitaryLieAlgebra (n := Fin 2) :=
    ⟨Matrix.diagonal ![Complex.I, -Complex.I], by
      constructor
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
      · simp [Matrix.trace, Fin.sum_univ_two]⟩
  let l : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℝ := Complex.imCLM.comp
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ 0 0))
  let f : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ := fun U => l U.val
  have hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 2)) 𝓘(ℝ) ∞ f :=
    l.contMDiff.comp specialUnitary_val_contMDiff
  refine ⟨A, f, hf, ?_⟩
  rw [specialUnitaryGamma_eq _ hf hf]
  simp only [Fintype.sum_unique]
  have hd : specialUnitaryDeriv A f 1 = 1 := by
    change specialUnitaryDeriv A (fun U => l U.val) 1 = 1
    rw [specialUnitaryDeriv_of_ambient A 1 l.differentiableAt]
    unfold rightMulDeriv
    rw [l.hasFDerivAt.fderiv]
    norm_num [l, A, Matrix.diagonal]
  rw [hd]
  norm_num

-- The SU(3) differential curvature estimate, expanded into its actual generator formula.
example {f : Matrix.specialUnitaryGroup (Fin 3) ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 3)) 𝓘(ℝ) ∞ f)
    (U : Matrix.specialUnitaryGroup (Fin 3) ℂ) :
    let b := stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 3))
    3 * specialUnitaryGamma b f f U ≤
      specialUnitaryLaplacian b (specialUnitaryGamma b f f) U -
        2 * specialUnitaryGamma b f (specialUnitaryLaplacian b f) U := by
  dsimp only
  have h := specialUnitaryGammaTwo_lower_bound
    (stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 3))) hf U
  norm_num only [Fintype.card_fin, Nat.cast_ofNat, specialUnitaryGammaTwo] at h
  linarith

-- The actual operator commutation also applies to iterated generators.
example {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := Fin 2)))
    (A : specialUnitaryLieAlgebra (n := Fin 2))
    {f : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 2)) 𝓘(ℝ) ∞ f) :
    specialUnitaryLaplacian b (specialUnitaryLaplacian b (specialUnitaryDeriv A f)) =
      specialUnitaryDeriv A (specialUnitaryLaplacian b (specialUnitaryLaplacian b f)) := by
  rw [specialUnitaryLaplacian_deriv b A hf]
  exact specialUnitaryLaplacian_deriv b A (specialUnitaryLaplacian_contMDiff b hf)

-- The pointwise SU(3) curvature bound now gives an actual normalized-Haar estimate.
example {f : Matrix.specialUnitaryGroup (Fin 3) ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 3)) 𝓘(ℝ) ∞ f) :
    let b := stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 3))
    (3 / 2 : ℝ) * (∫ U, specialUnitaryGamma b f f U ∂specialUnitaryHaar (Fin 3)) ≤
      ∫ U, (specialUnitaryLaplacian b f U) ^ 2 ∂specialUnitaryHaar (Fin 3) := by
  simpa using specialUnitary_integrated_gammaTwo_lower_bound
    (stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 3))) hf

-- Haar integration by parts applies to the nonconstant imaginary matrix-entry test.
example (A : specialUnitaryLieAlgebra (n := Fin 2)) :
    (∫ U : Matrix.specialUnitaryGroup (Fin 2) ℂ,
      specialUnitaryDeriv A (fun V => (V.val 0 0).im) U ∂specialUnitaryHaar (Fin 2)) = 0 := by
  let l : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℝ := Complex.imCLM.comp
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ 0 0))
  exact specialUnitary_integral_deriv_eq_zero A
    (l.contMDiff.comp specialUnitary_val_contMDiff)

-- The logarithmic curvature estimate applies to an everywhere-positive, nonconstant SU(2) test.
example :
    let f : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ := fun U => Real.exp (U.val 0 0).im
    let b := stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 2))
    (∫ U, specialUnitaryGamma b f f U / f U ∂specialUnitaryHaar (Fin 2)) ≤
      ∫ U, f U * specialUnitaryGammaTwo b (Real.log ∘ f) U ∂specialUnitaryHaar (Fin 2) := by
  let l : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℝ := Complex.imCLM.comp
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ 0 0))
  have hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 2)) 𝓘(ℝ) ∞
      (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ => Real.exp (l U.val)) :=
    Real.contDiff_exp.comp_contMDiff (l.contMDiff.comp specialUnitary_val_contMDiff)
  simpa using specialUnitary_weighted_gammaTwo_log_lower_bound
    (stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 2))) hf
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ => Real.exp_pos (l U.val))

-- The entropy differentiation API retains the mass correction for exponential families.
example {h : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ} (hc : Continuous h) (t : ℝ) :
    HasDerivAt
      (fun r => entropy (specialUnitaryHaar (Fin 2)) (fun U => Real.exp (r * h U)))
      ((∫ U, (Real.log (Real.exp (t * h U)) + 1) * (Real.exp (t * h U) * h U)
          ∂specialUnitaryHaar (Fin 2)) -
        (Real.log (∫ U, Real.exp (t * h U) ∂specialUnitaryHaar (Fin 2)) + 1) *
          (∫ U, Real.exp (t * h U) * h U ∂specialUnitaryHaar (Fin 2))) t := by
  apply hasDerivAt_entropy_of_compact (s := Set.univ)
    (F := fun r U => Real.exp (r * h U)) (Q := fun r U => Real.exp (r * h U) * h U)
  · exact Real.continuous_exp.comp (continuous_fst.mul (hc.comp continuous_snd))
  · exact (Real.continuous_exp.comp (continuous_fst.mul (hc.comp continuous_snd))).mul
      (hc.comp continuous_snd)
  · exact fun r U => Real.exp_pos _
  · intro r _ U
    simpa only [one_mul] using ((hasDerivAt_id r).mul_const (h U)).exp
  · simp

-- The spatial Fisher variation has the exact coefficient -3 on SU(3).
example {f : Matrix.specialUnitaryGroup (Fin 3) ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 3)) 𝓘(ℝ) ∞ f)
    (hpos : ∀ U, 0 < f U) :
    let b := stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 3))
    (∫ U, 2 * specialUnitaryGamma b f (specialUnitaryLaplacian b f) U / f U -
        specialUnitaryGamma b f f U * specialUnitaryLaplacian b f U / (f U) ^ 2
      ∂specialUnitaryHaar (Fin 3)) ≤
      -3 * (∫ U, specialUnitaryGamma b f f U / f U ∂specialUnitaryHaar (Fin 3)) := by
  simpa using specialUnitary_fisher_variation_le
    (stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 3))) hf hpos

-- A supplied positive family with nonzero time variation: Fisher information scales as exp(t).
-- This tests the differentiation theorem; this rescaling is not asserted to solve the heat equation.
example {ι : Type*} [Fintype ι]
    (b : ι → specialUnitaryLieAlgebra (n := Fin 2))
    {f : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 2)) 𝓘(ℝ) ∞ f)
    (hpos : ∀ U, 0 < f U) (t : ℝ) :
    let F : ℝ → Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ := fun r U => Real.exp r * f U
    HasDerivAt (fun r => ∫ U, specialUnitaryGamma b (F r) (F r) U / F r U
      ∂specialUnitaryHaar (Fin 2))
      (∫ U, specialUnitaryGamma b (F t) (F t) U / F t U ∂specialUnitaryHaar (Fin 2)) t := by
  let F : ℝ → Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ := fun r U => Real.exp r * f U
  have hF : Continuous (Function.uncurry F) :=
    (Real.continuous_exp.comp continuous_fst).mul (hf.continuous.comp continuous_snd)
  have hs r : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 2)) 𝓘(ℝ) ∞ (F r) :=
    contMDiff_const.mul hf
  have h0 r U : F r U ≠ 0 := ne_of_gt (mul_pos (Real.exp_pos r) (hpos U))
  have he (i : ι) (r : ℝ) (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      specialUnitaryDeriv (b i) (F r) U = Real.exp r * specialUnitaryDeriv (b i) f U := by
    exact DFunLike.congr_fun
      ((hf.mdifferentiableAt (by decide)).hasMFDerivAt.const_smul (Real.exp r)).mfderiv (b i)
  have hDF i : Continuous (fun p : ℝ × Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      specialUnitaryDeriv (b i) (F p.1) p.2) := by
    simp_rw [he]
    exact (Real.continuous_exp.comp continuous_fst).mul
      ((specialUnitaryDeriv_contMDiff (b i) hf).continuous.comp continuous_snd)
  have hd (r : ℝ) (_ : r ∈ Set.univ) (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      HasDerivAt (fun v => F v U) (F r U) r :=
    (Real.hasDerivAt_exp r).mul_const (f U)
  have hdD (i : ι) (r : ℝ) (_ : r ∈ Set.univ) (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      HasDerivAt (fun v => specialUnitaryDeriv (b i) (F v) U)
        (specialUnitaryDeriv (b i) (F r) U) r := by
    simp_rw [he]
    exact (Real.hasDerivAt_exp r).mul_const _
  have h := specialUnitary_hasDerivAt_fisher b hF hF h0 hs hs hDF hDF hd hdD t (by simp)
  convert h using 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro U
  change specialUnitaryGamma b (F t) (F t) U / F t U =
    2 * specialUnitaryGamma b (F t) (F t) U / F t U -
      specialUnitaryGamma b (F t) (F t) U * F t U / (F t U) ^ 2
  field_simp [h0 t U]
  ring

-- A constructed, nonconstant affine SU(2) heat solution stays positive at every forward time.
example (T : ℝ) (hT : 0 ≤ T) :
    let l : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℝ := Complex.imCLM.comp
      (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ 0 0))
    let b := stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 2))
    ∀ U, 0 < specialUnitaryLinearHeat b l 2 T U := by
  dsimp only
  apply specialUnitaryLinearHeat_pos _ _ 2 hT
  intro U
  change 0 < 2 + (U.val 0 0).im
  have hn : ‖U.val‖ = Real.sqrt 2 := by
    simpa using unitary_norm (specialUnitaryInclusion U)
  have hb := (Complex.abs_im_le_norm (U.val 0 0)).trans (norm_entry_le_frobenius U.val 0 0)
  rw [hn] at hb
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have ha := neg_abs_le (U.val 0 0).im
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

-- The actual PDE is checked directly, without a supplied heat trajectory or heat-equation premise.
example (t : ℝ) (U : Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (l : Matrix (Fin 3) (Fin 3) ℂ →L[ℝ] ℝ) :
    let b := stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 3))
    HasDerivAt (fun r => specialUnitaryLinearHeat b l 2 r U)
      (specialUnitaryLaplacian b (specialUnitaryLinearHeat b l 2 t) U) t :=
  specialUnitaryLinearHeat_hasDerivAt _ l 2 t U

-- A genuinely quadratic, strictly positive matrix observable on the actual SU(2).
private noncomputable def quadraticSU2 : specialUnitaryPolynomialSpace (n := Fin 2) 2 := by
  let l : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℝ := Complex.imCLM.comp
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ 0 0))
  let g := specialUnitaryAffineMap (n := Fin 2) (2, l)
  have hg : g ∈ specialUnitaryPolynomialSpace 1 := by
    change g ∈ specialUnitaryAffineSpace ^ 1
    rw [pow_one (specialUnitaryAffineSpace (n := Fin 2))]
    exact ⟨(2, l), rfl⟩
  exact ⟨g * g, specialUnitaryPolynomialSpace_mul_mem hg hg⟩

private theorem quadraticSU2_apply (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    quadraticSU2.val U = (2 + (U.val 0 0).im) ^ 2 := by
  change (2 + (U.val 0 0).im) * (2 + (U.val 0 0).im) = _
  ring

private theorem quadraticSU2_pos (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    0 < quadraticSU2.val U := by
  rw [quadraticSU2_apply]
  have hn : ‖U.val‖ = Real.sqrt 2 := by
    simpa using unitary_norm (specialUnitaryInclusion U)
  have hb := (Complex.abs_im_le_norm (U.val 0 0)).trans (norm_entry_le_frobenius U.val 0 0)
  rw [hn] at hb
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have ha := neg_abs_le (U.val 0 0).im
  have h : 0 < 2 + (U.val 0 0).im := by nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  exact sq_pos_of_pos h

-- Nonzero actual invariant derivative certifies that this test is not constant.
private theorem quadraticSU2_nonconstantDerivative : ∃ A : specialUnitaryLieAlgebra (n := Fin 2),
    specialUnitaryDeriv A quadraticSU2.val 1 = 4 := by
  let A : specialUnitaryLieAlgebra (n := Fin 2) :=
    ⟨Matrix.diagonal ![Complex.I, -Complex.I], by
      constructor
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
      · simp [Matrix.trace, Fin.sum_univ_two]⟩
  let l : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℝ := Complex.imCLM.comp
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ 0 0))
  let g := specialUnitaryAffineMap (n := Fin 2) (2, l)
  refine ⟨A, ?_⟩
  change specialUnitaryDeriv A (fun U => g U * g U) 1 = 4
  have hd : specialUnitaryDeriv A (fun U => g U * g U) 1 =
      g 1 * specialUnitaryDeriv A g 1 + g 1 * specialUnitaryDeriv A g 1 :=
    congrFun (specialUnitaryDeriv_mul A g.contMDiff g.contMDiff) 1
  rw [hd]
  change (2 + l 1) * specialUnitaryDeriv A (fun U => 2 + l U.val) 1 +
    (2 + l 1) * specialUnitaryDeriv A (fun U => 2 + l U.val) 1 = 4
  rw [specialUnitaryDeriv_affine]
  norm_num [l, A, Matrix.diagonal]

-- Actual polynomial heat preserves its normalized Haar mass at every time.
example (t : ℝ) :
    let b := stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 2))
    (∫ U, (specialUnitaryPolynomialHeat b 2 quadraticSU2 t).val U ∂specialUnitaryHaar (Fin 2)) =
      ∫ U, quadraticSU2.val U ∂specialUnitaryHaar (Fin 2) :=
  specialUnitaryPolynomialHeat_integral _ 2 quadraticSU2 t

-- Exponential Fisher decay, rate exactly 2, on this concrete nonconstant positive test.
example (t : ℝ) (ht : 0 ≤ t) :
    let b := stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 2))
    let P := specialUnitaryPolynomialForwardHeat b 2 quadraticSU2
    (∫ U, specialUnitaryGamma b (P t).val (P t).val U / (P t).val U
      ∂specialUnitaryHaar (Fin 2)) ≤
      Real.exp (-2 * t) * (∫ U, specialUnitaryGamma b quadraticSU2.val quadraticSU2.val U /
        quadraticSU2.val U ∂specialUnitaryHaar (Fin 2)) := by
  simpa using specialUnitaryPolynomialForwardHeat_fisher_le_exp
    (stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 2))) 2 quadraticSU2 quadraticSU2_pos ht


-- These use the original matrix topology with the Frobenius scope active.
example : ConnectedSpace (Matrix.unitaryGroup (Fin 3) ℂ) := inferInstance
example : ConnectedSpace (Matrix.specialUnitaryGroup (Fin 0) ℂ) := inferInstance
example : ConnectedSpace (Matrix.specialUnitaryGroup (Fin 1) ℂ) := inferInstance
example : ConnectedSpace (Matrix.specialUnitaryGroup (Fin 3) ℂ) := inferInstance

-- A concrete nonconstant positive quadratic has strictly positive Haar energy.
private theorem quadraticSU2_energy_pos :
    let b := stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 2))
    0 < ∫ U, specialUnitaryGamma b quadraticSU2.val quadraticSU2.val U
      ∂specialUnitaryHaar (Fin 2) := by
  dsimp only
  let b := stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 2))
  have hn : 0 ≤ ∫ U, specialUnitaryGamma b quadraticSU2.val quadraticSU2.val U
      ∂specialUnitaryHaar (Fin 2) :=
    integral_nonneg (fun U => specialUnitaryGamma_nonneg b quadraticSU2.val.contMDiff U)
  by_contra! h
  have hz := le_antisymm h hn
  obtain ⟨A, hA⟩ := quadraticSU2_nonconstantDerivative
  have h0 := specialUnitaryDeriv_eq_zero_of_integral_gamma_eq_zero b
    quadraticSU2.val.contMDiff hz A 1
  linarith

-- Harmonic smooth SU(3) functions are constant, with their value fixed by normalized Haar mass.
example {f : Matrix.specialUnitaryGroup (Fin 3) ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := Fin 3)) 𝓘(ℝ) ∞ f)
    (hL : specialUnitaryLaplacian
      (stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 3))) f = 0) :
    f = fun _ => ∫ U, f U ∂specialUnitaryHaar (Fin 3) :=
  specialUnitary_eq_mean_of_integral_gamma_eq_zero _ hf
    (specialUnitary_integral_gamma_eq_zero_of_laplacian_eq_zero _ hf hL)


-- Uniform convergence of an actual nonconstant quadratic heat flow to its Haar mean.
example :
    let b := stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 2))
    Filter.Tendsto (specialUnitaryPolynomialForwardHeat b 2 quadraticSU2) Filter.atTop
      (nhds (specialUnitaryPolynomialConst 2
        (∫ U, quadraticSU2.val U ∂specialUnitaryHaar (Fin 2)))) :=
  specialUnitaryPolynomialForwardHeat_tendsto_mean _ 2 (by decide) quadraticSU2 quadraticSU2_pos

-- The proved positive-density bound on the concrete quadratic test, with coefficient 1/2.
example :
    let b := stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 2))
    entropy (specialUnitaryHaar (Fin 2)) quadraticSU2.val ≤
      (1 / 2 : ℝ) * (∫ U, specialUnitaryGamma b quadraticSU2.val quadraticSU2.val U /
        quadraticSU2.val U ∂specialUnitaryHaar (Fin 2)) := by
  simpa using specialUnitaryPolynomial_entropy_le_fisher
    (stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 2))) 2 (by decide)
    quadraticSU2 quadraticSU2_pos

-- A test with a zero at the identity: strict positivity is absent from the squared-function LSI.
private noncomputable def centeredQuadraticSU2 : specialUnitaryPolynomialSpace (n := Fin 2) 2 :=
  quadraticSU2 - specialUnitaryPolynomialConst 2 4

example : centeredQuadraticSU2.val 1 = 0 := by
  change quadraticSU2.val 1 - (specialUnitaryPolynomialConst (n := Fin 2) 2 4).val 1 = 0
  rw [quadraticSU2_apply, specialUnitaryPolynomialConst_apply]
  norm_num

example :
    let b := stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 2))
    entropy (specialUnitaryHaar (Fin 2)) (fun U => centeredQuadraticSU2.val U ^ 2) ≤
      2 * (∫ U, specialUnitaryGamma b centeredQuadraticSU2.val centeredQuadraticSU2.val U
        ∂specialUnitaryHaar (Fin 2)) := by
  have h := specialUnitaryPolynomial_entropy_sq_le
    (stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 2))) 2 (by decide) centeredQuadraticSU2
  norm_num at h
  exact h

-- Exact N-dependence in the public squared-polynomial theorem, with no heat hypotheses.
example (N d : ℕ) (hN : 0 < N) (f : specialUnitaryPolynomialSpace (n := Fin N) d) :
    let b := stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin N))
    entropy (specialUnitaryHaar (Fin N)) (fun U => f.val U ^ 2) ≤
      (4 / (N : ℝ)) * (∫ U, specialUnitaryGamma b f.val f.val U ∂specialUnitaryHaar (Fin N)) := by
  simpa using specialUnitaryPolynomial_entropy_sq_le
    (stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin N))) d (by simpa using hN) f


-- The actual local metric slope, with a finite right-hand side, on a nonconstant SU(2) test.
example : slopeEnergy (specialUnitaryHaar (Fin 2)) quadraticSU2.val ≠ ⊤ :=
  specialUnitaryPolynomial_slopeEnergy_ne_top 2 quadraticSU2

example : 0 < slopeEnergy (specialUnitaryHaar (Fin 2)) quadraticSU2.val := by
  have he := ENNReal.ofReal_pos.mpr quadraticSU2_energy_pos
  exact he.trans_le (specialUnitary_integral_gamma_le_slopeEnergy
    (stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 2))) quadraticSU2.val.contMDiff)

-- This test vanishes at the identity; the metric LSI has no positivity hypothesis.
example : entropy (specialUnitaryHaar (Fin 2)) (fun U => centeredQuadraticSU2.val U ^ 2) ≤
    2 * (∫ U, (localSlope centeredQuadraticSU2.val U).toReal ^ 2 ∂specialUnitaryHaar (Fin 2)) := by
  have h := specialUnitaryPolynomial_entropy_sq_le_slope
    (stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin 2))) 2 (by decide) centeredQuadraticSU2
  norm_num at h
  exact h

-- Exact constant 2/N in the paper's extended local-slope formulation for every positive N.
example (N d : ℕ) (hN : 0 < N) (f : specialUnitaryPolynomialSpace (n := Fin N) d) :
    ENNReal.ofReal (entropy (specialUnitaryHaar (Fin N)) (fun U => f.val U ^ 2)) ≤
      2 * ((2 / (N : NNReal) : NNReal) : ENNReal) * slopeEnergy (specialUnitaryHaar (Fin N)) f.val := by
  simpa using specialUnitaryPolynomial_metric_entropy_sq_le
    (stdOrthonormalBasis ℝ (specialUnitaryLieAlgebra (n := Fin N))) d (by simpa using hN) f

-- Polynomial regularization accepts arbitrary continuous observables, not only polynomials.
example (N d : ℕ) (k : specialUnitaryPolynomialSpace (n := Fin N) d)
    (f : C(Matrix.specialUnitaryGroup (Fin N) ℂ, ℝ)) :
    ∃ p : specialUnitaryPolynomialSpace (n := Fin N) d,
      ∀ U, p.val U = ∫ V, f (U * V) * k.val V ∂specialUnitaryHaar (Fin N) :=
  specialUnitaryPolynomial_exists_averaging d k f

-- Uniform convergence of varying-degree functions suffices for entropy convergence.
example (N : ℕ) (d : ℕ → ℕ)
    (p : ∀ j, specialUnitaryPolynomialSpace (n := Fin N) (d j))
    (f : C(Matrix.specialUnitaryGroup (Fin N) ℂ, ℝ))
    (h : Filter.Tendsto (fun j => specialUnitaryPolynomialToContinuous (d j) (p j))
      Filter.atTop (nhds f)) :
    Filter.Tendsto
      (fun j => entropy (specialUnitaryHaar (Fin N)) (fun U => (p j).val U ^ 2))
      Filter.atTop (nhds (entropy (specialUnitaryHaar (Fin N)) (fun U => f U ^ 2))) :=
  tendsto_entropy_sq_of_tendsto_continuousMap (specialUnitaryHaar (Fin N))
    (f := fun j => specialUnitaryPolynomialToContinuous (d j) (p j)) (g := f) h

-- Explicit polynomial probability densities exist in every positive dimension.
example (N j : ℕ) (hN : 0 < N) :
    (∫ U, (specialUnitaryPowerKernel (n := Fin N) j).val U ∂specialUnitaryHaar (Fin N)) = 1 :=
  specialUnitaryPowerKernel_integral (by simpa using hN) j

-- The peak uses the unnormalized HS distance; in SU(2) the coefficient is 4.
example (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ‖U.val - 1‖ ^ 2 = 4 - 2 * U.val.trace.re := by
  have h := specialUnitary_norm_sub_one_sq U
  norm_num at h
  exact h

-- Uniform and entropy approximation apply to the distance-to-identity observable,
-- with no smoothness hypothesis at its zero.
example : ∃ p : ∀ j, specialUnitaryPolynomialSpace (n := Fin 2) j,
    Filter.Tendsto (fun j => specialUnitaryPolynomialToContinuous j (p j)) Filter.atTop
      (nhds (⟨fun U => dist U 1, continuous_id.dist continuous_const⟩ :
        C(Matrix.specialUnitaryGroup (Fin 2) ℂ, ℝ))) ∧
    Filter.Tendsto
      (fun j => entropy (specialUnitaryHaar (Fin 2)) (fun U => (p j).val U ^ 2))
      Filter.atTop (nhds (entropy (specialUnitaryHaar (Fin 2)) (fun U => dist U 1 ^ 2))) := by
  obtain ⟨p, _, hu, he⟩ := specialUnitaryPolynomial_exists_uniform_entropy_approximation
    (n := Fin 2) (by decide) ⟨fun U => dist U 1, continuous_id.dist continuous_const⟩
  exact ⟨p, hu, he⟩

-- Full SU(N) metric LSI: no polynomial, smoothness, heat, or energy hypothesis.
example (N : ℕ) (hN : 0 < N) :
    MetricLSI (specialUnitaryHaar (Fin N)) (2 / (N : NNReal)) := by
  simpa using specialUnitary_metricLSI (n := Fin N) (by simpa using hN)

-- The positive-dimension theorem includes SU(1).
example : MetricLSI (specialUnitaryHaar (Fin 1)) 2 := by
  simpa using specialUnitary_metricLSI (n := Fin 1) (by decide)

-- Every locally Lipschitz function has the exact real coefficient 4/N.
example (N : ℕ) (hN : 0 < N) (f : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hf : LocallyLipschitz f) :
    entropy (specialUnitaryHaar (Fin N)) (fun U => f U ^ 2) ≤
      (4 / (N : ℝ)) * ∫ U, (localSlope f U).toReal ^ 2 ∂specialUnitaryHaar (Fin N) := by
  simpa using specialUnitary_entropy_sq_le_of_locallyLipschitz (by simpa using hN) hf

-- An admissible distance function with a zero at identity, without assuming smoothness.
example : entropy (specialUnitaryHaar (Fin 2)) (fun U => dist U 1 ^ 2) ≤
    2 * ∫ U, (localSlope (fun V : Matrix.specialUnitaryGroup (Fin 2) ℂ => dist V 1) U).toReal ^ 2
      ∂specialUnitaryHaar (Fin 2) := by
  have h := specialUnitary_entropy_sq_le_of_locallyLipschitz (n := Fin 2) (by decide)
    (LipschitzWith.dist_left (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)).locallyLipschitz
  norm_num at h
  exact h

-- All integrability requirements and finite energy for that nonsmooth admissible test.
example :
    Integrable (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ => dist U 1 ^ 2) (specialUnitaryHaar (Fin 2)) ∧
    Integrable (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ => dist U 1 ^ 2 * Real.log (dist U 1 ^ 2))
      (specialUnitaryHaar (Fin 2)) ∧
    slopeEnergy (specialUnitaryHaar (Fin 2)) (fun U => dist U 1) ≠ ⊤ := by
  have hf := (LipschitzWith.dist_left (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)).locallyLipschitz
  refine ⟨integrable_sq_of_locallyLipschitz hf, integrable_sq_log_of_locallyLipschitz hf, ?_⟩
  rw [slopeEnergy_eq_ofReal_integral hf]
  exact ENNReal.ofReal_ne_top

private def negIdentitySU2 : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨-1, by
    constructor
    · constructor <;> simp
    · change Matrix.det (-(1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1
      simp [Matrix.det_neg]⟩

-- The distance observable is nonconstant on the actual group.
example : dist negIdentitySU2 1 ≠ dist (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) 1 := by
  rw [dist_self, ne_eq, dist_eq_zero]
  intro h
  have he := congrArg (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ => U.val 0 0) h
  norm_num [negIdentitySU2] at he
