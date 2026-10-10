module

public import LogSobolev.Unitary.PolynomialPhaseEntropy
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Entropy controlled by the combined phase/SU energy

At the paper's interval length, the nonsharp interval bound and SU bound
combine with coefficient `π²/N`. This is sufficient for the requested `12/N`
because the phase and traceless energies use their exact orthogonal scaling.
-/

open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.Frobenius NNReal ENNReal

namespace LogSobolev

/-- The entropy of a polynomial phase family is controlled by its combined energy. -/
theorem phase_entropy_sq_le_energy (N : ℕ) (hN : 0 < N) (d : ℕ)
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := Fin N)))
    {K : NNReal} {p : ℝ → specialUnitaryPolynomialSpace (n := Fin N) d} (hp : LipschitzWith K p) :
    ENNReal.ofReal (entropy ((intervalUniform (phaseIntervalLength N)).prod
      (specialUnitaryHaar (Fin N))) (fun z => (p z.1.val).val z.2 ^ 2)) ≤
      ENNReal.ofReal (Real.pi ^ 2 / N) *
        ∫⁻ t, ∫⁻ U, ENNReal.ofReal ((deriv p t.val).val U ^ 2 / 2 +
          specialUnitaryGamma b (p t.val).val (p t.val).val U)
          ∂specialUnitaryHaar (Fin N) ∂intervalUniform (phaseIntervalLength N) := by
  let L := phaseIntervalLength N
  have hL : 0 < L := phaseIntervalLength_pos N hN
  letI : Fact (0 < L) := ⟨hL⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let Q : Icc (0 : ℝ) L × Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ := fun z =>
    (deriv p z.1.val).val z.2 ^ 2 / 2 + specialUnitaryGamma b (p z.1.val).val (p z.1.val).val z.2
  have hpc : Continuous (fun t : Icc (0 : ℝ) L => p t.val) :=
    hp.continuous.comp continuous_subtype_val
  have hGi := (specialUnitaryPolynomialFamily_gamma_continuous d b hpc).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := (intervalUniform L).prod (specialUnitaryHaar (Fin N)))
  have hDi := specialUnitaryPolynomialFamily_deriv_sq_integrable d L hL hp
  have hQi : Integrable Q ((intervalUniform L).prod (specialUnitaryHaar (Fin N))) :=
    (hDi.div_const 2).add hGi
  have hQn (z) : 0 ≤ Q z := add_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
    (specialUnitaryGamma_nonneg b (p z.1.val).val.contMDiff z.2)
  have hQint : (∫ z, Q z ∂(intervalUniform L).prod (specialUnitaryHaar (Fin N))) =
      (∫ t, ∫ U, (deriv p t.val).val U ^ 2 ∂specialUnitaryHaar (Fin N) ∂intervalUniform L) / 2 +
      ∫ t, ∫ U, specialUnitaryGamma b (p t.val).val (p t.val).val U
        ∂specialUnitaryHaar (Fin N) ∂intervalUniform L := by
    dsimp only [Q]
    rw [integral_add (hDi.div_const 2) hGi, integral_div, integral_prod _ hDi, integral_prod _ hGi]
  have hc : (4 : ℝ) / N ≤ Real.pi ^ 2 / N := by
    apply div_le_div_of_nonneg_right _ hNr.le
    nlinarith [Real.pi_gt_three]
  have hlen : L ^ 2 / 4 = (Real.pi ^ 2 / (N : ℝ)) / 2 := by
    dsimp [L, phaseIntervalLength]
    rw [mul_pow, Real.sq_sqrt (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hNr.le)]
    ring
  have hGnonneg : 0 ≤ ∫ t, ∫ U, specialUnitaryGamma b (p t.val).val (p t.val).val U
      ∂specialUnitaryHaar (Fin N) ∂intervalUniform L :=
    integral_nonneg fun t => integral_nonneg fun U => specialUnitaryGamma_nonneg b (p t.val).val.contMDiff U
  have hr := polynomialPhase_entropy_sq_le d L hL (by simpa using hN) b hp
  simp only [Fintype.card_fin] at hr
  rw [hlen] at hr
  have he : entropy ((intervalUniform L).prod (specialUnitaryHaar (Fin N)))
      (fun z => (p z.1.val).val z.2 ^ 2) ≤
        (Real.pi ^ 2 / N) * ∫ z, Q z ∂(intervalUniform L).prod (specialUnitaryHaar (Fin N)) := by
    rw [hQint]
    have hmul := mul_le_mul_of_nonneg_right hc hGnonneg
    nlinarith
  have hh := ENNReal.ofReal_le_ofReal he
  rw [ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal hQi (Eventually.of_forall hQn)] at hh
  have hprod := lintegral_prod (fun z => ENNReal.ofReal (Q z))
    hQi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [hprod] at hh
  exact hh

end LogSobolev
