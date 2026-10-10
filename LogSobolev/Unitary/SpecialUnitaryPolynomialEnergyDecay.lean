import LogSobolev.Unitary.SpecialUnitaryPolynomialDissipation

/-! # Decay of integrated energy for polynomial heat

The preserved upper bound on a positive density converts Fisher decay into
vanishing integrated carré du champ. This energy has a continuous extension to
all polynomial observables, including possible limits of the heat orbit.
-/

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

/-- A bounded positive smooth density has Dirichlet energy at most its upper bound times Fisher information. -/
theorem specialUnitary_integral_gamma_le_mul_fisher
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hpos : ∀ U, 0 < f U) {M : ℝ} (hM : ∀ U, f U ≤ M) :
    (∫ U, specialUnitaryGamma b f f U ∂specialUnitaryHaar n) ≤
      M * (∫ U, specialUnitaryGamma b f f U / f U ∂specialUnitaryHaar n) := by
  rw [← integral_const_mul]
  apply integral_mono
    (specialUnitary_integrable_of_continuous (specialUnitaryGamma_contMDiff b hf hf).continuous)
    ((specialUnitary_integrable_fisher b hf (fun U => ne_of_gt (hpos U))).const_mul M)
  intro U
  have h := mul_le_mul_of_nonneg_right (hM U)
    (div_nonneg (specialUnitaryGamma_nonneg b hf U) (hpos U).le)
  simpa only [mul_div_cancel₀ _ (ne_of_gt (hpos U))] using h

/-- Polynomial heat energy inherits exponential decay from Fisher information. -/
theorem specialUnitaryPolynomialForwardHeat_energy_le_exp
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n))) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) (hpos : ∀ U, 0 < f.val U)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ U, specialUnitaryGamma b (specialUnitaryPolynomialForwardHeat b d f t).val
      (specialUnitaryPolynomialForwardHeat b d f t).val U ∂specialUnitaryHaar n) ≤
      ‖f‖ * (Real.exp (-(Fintype.card n : ℝ) * t) *
        (∫ U, specialUnitaryGamma b f.val f.val U / f.val U ∂specialUnitaryHaar n)) := by
  have hb : ∀ U, (specialUnitaryPolynomialForwardHeat b d f t).val U ≤ ‖f‖ := by
    rw [specialUnitaryPolynomialForwardHeat_eq b d f ht]
    exact specialUnitaryPolynomialHeat_upper_bound b d f ht
      (fun U => (specialUnitaryPolynomialToContinuous d f).apply_le_norm U)
  exact (specialUnitary_integral_gamma_le_mul_fisher b
    (specialUnitaryPolynomialForwardHeat b d f t).val.contMDiff
    (specialUnitaryPolynomialForwardHeat_pos b d f hpos t) hb).trans
      (mul_le_mul_of_nonneg_left
        (specialUnitaryPolynomialForwardHeat_fisher_le_exp b d f hpos ht) (norm_nonneg f))

/-- In positive matrix dimension, the constructed polynomial heat energy tends to zero. -/
theorem specialUnitaryPolynomialForwardHeat_energy_tendsto_zero
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n))) (d : ℕ)
    (hN : 0 < Fintype.card n)
    (f : specialUnitaryPolynomialSpace (n := n) d) (hpos : ∀ U, 0 < f.val U) :
    Tendsto (fun t => ∫ U,
      specialUnitaryGamma b (specialUnitaryPolynomialForwardHeat b d f t).val
        (specialUnitaryPolynomialForwardHeat b d f t).val U ∂specialUnitaryHaar n)
      atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-(Fintype.card n : ℝ) * t)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by exact_mod_cast hN : 0 < (Fintype.card n : ℝ)))
    simpa only [neg_mul] using h
  have hh := (he.mul_const
    (∫ U, specialUnitaryGamma b f.val f.val U / f.val U ∂specialUnitaryHaar n)).const_mul ‖f‖
  simp only [mul_zero, zero_mul] at hh
  apply squeeze_zero' ?_ ?_ hh
  · exact Eventually.of_forall fun t => integral_nonneg
      (fun U => specialUnitaryGamma_nonneg b (specialUnitaryPolynomialForwardHeat b d f t).val.contMDiff U)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact specialUnitaryPolynomialForwardHeat_energy_le_exp b d f hpos ht

end LogSobolev
