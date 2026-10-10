import LogSobolev

/-! Independent clients of the combined-energy and entropy-approximation results. -/
open Matrix MeasureTheory LogSobolev Filter
open scoped Matrix.Norms.Frobenius NNReal ENNReal Topology

-- Entropy approximation applies directly to a nonsmooth distance observable on U(2).
example : Tendsto
    (fun d => entropy (unitaryHaar (Fin 2)) (fun U =>
      unitarySUConvolution d
        ⟨fun V => dist V 1, continuous_id.dist continuous_const⟩ U ^ 2)) atTop
    (𝓝 (entropy (unitaryHaar (Fin 2)) (fun U => dist U 1 ^ 2))) :=
  tendsto_entropy_sq_unitarySUConvolution (by decide) _

-- Every locally Lipschitz observable has approximants with the proved combined energy bound.
example (N : ℕ) (hN : 0 < N) (d : ℕ) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := Fin N)))
    {f : Matrix.unitaryGroup (Fin N) ℂ → ℝ} (hf : LocallyLipschitz f) :
    ∃ (K : NNReal) (p : ℝ → specialUnitaryPolynomialSpace (n := Fin N) d),
      (∀ t U, (p t).val U = ∫ V,
        f (phaseMul (Real.sqrt (2 / (N : ℝ))) t (specialUnitaryInclusion (U * V))) *
          (specialUnitaryPowerKernel d).val V ∂specialUnitaryHaar (Fin N)) ∧
      LipschitzWith K p ∧
      (∫⁻ t, ∫⁻ U, ENNReal.ofReal ((deriv p t.val).val U ^ 2 / 2 +
          specialUnitaryGamma b (p t.val).val (p t.val).val U)
        ∂specialUnitaryHaar (Fin N) ∂intervalUniform (phaseIntervalLength N)) ≤
        slopeEnergy (unitaryHaar (Fin N)) f :=
  unitary_exists_phase_polynomial_energy N hN d b hf

-- The metric bound has the exact orthogonal quadratic speed, not a sum of speeds.
example (N : ℕ) (hN : 0 < N) (t c : ℝ)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) (A : specialUnitaryLieAlgebra (n := Fin N)) :
    LipschitzWith (Real.toNNReal (Real.sqrt (‖A.val‖ ^ 2 + 2 * c ^ 2)))
      (unitaryPhaseFlow N t c U A) :=
  unitaryPhaseFlow_lipschitz N hN t c U A
