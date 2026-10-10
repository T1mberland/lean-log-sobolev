module

public import LogSobolev.Analysis.IntervalDerivativeLSI
public import LogSobolev.Unitary.SpecialUnitaryPolynomialFamilyRegularity
public import LogSobolev.Unitary.SpecialUnitaryPolynomialLSI
public import LogSobolev.Measure.ProductEntropySubadditivity

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Entropy of a polynomial phase family

The interval derivative LSI and the proved SU polynomial LSI bound the two
slice entropies. Product entropy subadditivity and verified Fubini then yield
the weighted sum of the phase and SU energies.
-/

open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.Frobenius NNReal

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Interval entropy of each fixed SU evaluation of a Lipschitz polynomial family. -/
theorem polynomialPhase_interval_entropy_sq_le (d : ℕ) (L : ℝ) (hL : 0 < L)
    {K : NNReal} {p : ℝ → specialUnitaryPolynomialSpace (n := n) d} (hp : LipschitzWith K p)
    (U : Matrix.specialUnitaryGroup n ℂ) :
    entropy (intervalUniform L) (fun t => (p t.val).val U ^ 2) ≤
      (L ^ 2 / 4) * ∫ t, (deriv p t.val).val U ^ 2 ∂intervalUniform L := by
  apply intervalUniform_entropy_sq_le_of_ae_hasDerivAt L hL
    (f := fun t => (p t).val U) (g := fun t => (deriv p t).val U)
    ((specialUnitaryPolynomialEval d U).lipschitz.comp hp)
    (specialUnitaryPolynomialFamily_deriv_sq_integrable_slice d L hL hp U)
  filter_upwards [specialUnitaryPolynomialFamily_ae_differentiable d hp] with t ht
  exact (specialUnitaryPolynomialEval d U).hasFDerivAt.comp_hasDerivAt t ht.hasDerivAt

/-- Product entropy is bounded by the sum of its weighted phase and SU energies. -/
theorem polynomialPhase_entropy_sq_le (d : ℕ) (L : ℝ) (hL : 0 < L)
    (hN : 0 < Fintype.card n) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {K : NNReal} {p : ℝ → specialUnitaryPolynomialSpace (n := n) d} (hp : LipschitzWith K p) :
    entropy ((intervalUniform L).prod (specialUnitaryHaar n))
      (fun z => (p z.1.val).val z.2 ^ 2) ≤
      (4 / (Fintype.card n : ℝ)) *
        (∫ t, ∫ U, specialUnitaryGamma b (p t.val).val (p t.val).val U
          ∂specialUnitaryHaar n ∂intervalUniform L) +
      (L ^ 2 / 4) * (∫ t, ∫ U, (deriv p t.val).val U ^ 2
        ∂specialUnitaryHaar n ∂intervalUniform L) := by
  letI : Fact (0 < L) := ⟨hL⟩
  have hpc : Continuous (fun t : Icc (0 : ℝ) L => p t.val) :=
    hp.continuous.comp continuous_subtype_val
  have hF := (specialUnitaryPolynomialFamily_continuous d hpc).pow 2
  have hG := specialUnitaryPolynomialFamily_gamma_continuous d b hpc
  have hGi := hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := (intervalUniform L).prod (specialUnitaryHaar n))
  have hDi := specialUnitaryPolynomialFamily_deriv_sq_integrable d L hL hp
  have hE1 : Continuous (fun t : Icc (0 : ℝ) L =>
      entropy (specialUnitaryHaar n) (fun U => (p t.val).val U ^ 2)) :=
    continuous_parametric_entropy hF
  have hE2 : Continuous (fun U : Matrix.specialUnitaryGroup n ℂ =>
      entropy (intervalUniform L) (fun t => (p t.val).val U ^ 2)) :=
    continuous_parametric_entropy (hF.comp continuous_swap)
  have hs := entropy_prod_le_integral_entropy_add_of_continuous
    (μ := intervalUniform L) (ν := specialUnitaryHaar n) hF (fun z => sq_nonneg _)
  apply hs.trans
  have h1 : (∫ t, entropy (specialUnitaryHaar n) (fun U => (p t.val).val U ^ 2)
      ∂intervalUniform L) ≤
      ∫ t, (4 / (Fintype.card n : ℝ)) * (∫ U,
        specialUnitaryGamma b (p t.val).val (p t.val).val U ∂specialUnitaryHaar n)
          ∂intervalUniform L := by
    apply integral_mono
      (hE1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hGi.integral_prod_left.const_mul _)
    intro t
    exact specialUnitaryPolynomial_entropy_sq_le b d hN (p t.val)
  have h2 : (∫ U, entropy (intervalUniform L) (fun t => (p t.val).val U ^ 2)
      ∂specialUnitaryHaar n) ≤
      ∫ U, (L ^ 2 / 4) * (∫ t, (deriv p t.val).val U ^ 2 ∂intervalUniform L)
        ∂specialUnitaryHaar n := by
    apply integral_mono
      (hE2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hDi.integral_prod_right.const_mul _)
    intro U
    exact polynomialPhase_interval_entropy_sq_le d L hL hp U
  have h := add_le_add h1 h2
  have hswap : (∫ t, ∫ U, (deriv p t.val).val U ^ 2
      ∂specialUnitaryHaar n ∂intervalUniform L) =
      ∫ U, ∫ t, (deriv p t.val).val U ^ 2 ∂intervalUniform L ∂specialUnitaryHaar n :=
    integral_integral_swap hDi
  rw [integral_const_mul, integral_const_mul, ← hswap] at h
  exact h

end LogSobolev
