import LogSobolev.Unitary.SpecialUnitaryPolynomialFamily
import LogSobolev.Unitary.SpecialUnitaryPolynomialFunctionals
import LogSobolev.Measure.IntervalAlmostEverywhere
import Mathlib.MeasureTheory.Integral.Prod

/-! # Joint regularity of polynomial phase families

Uniform evaluation bounds make phase-derivative squares integrable on the
actual interval/SU product. Invariant SU energy is jointly continuous. These
facts justify the two integrations in the slice-entropy argument.
-/

open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.Frobenius NNReal

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Polynomial evaluation is bounded by the induced uniform norm. -/
theorem specialUnitaryPolynomial_norm_eval_le (d : ℕ)
    (q : specialUnitaryPolynomialSpace (n := n) d) (U : Matrix.specialUnitaryGroup n ℂ) :
    ‖q.val U‖ ≤ ‖q‖ :=
  (specialUnitaryPolynomialToContinuous d q).norm_coe_le_norm U

/-- Joint evaluation along a continuous polynomial-valued parameter. -/
theorem specialUnitaryPolynomialFamily_continuous (d : ℕ)
    {X : Type*} [TopologicalSpace X]
    {p : X → specialUnitaryPolynomialSpace (n := n) d} (hp : Continuous p) :
    Continuous (fun z : X × Matrix.specialUnitaryGroup n ℂ => (p z.1).val z.2) :=
  (specialUnitaryPolynomial_clm_eval_continuous d (ContinuousLinearMap.id ℝ _)).comp
    ((hp.comp continuous_fst).prodMk continuous_snd)

/-- The totalized phase derivative is jointly measurable with the SU evaluation point. -/
theorem specialUnitaryPolynomialFamily_deriv_measurable (d : ℕ)
    (p : ℝ → specialUnitaryPolynomialSpace (n := n) d) :
    Measurable (fun z : ℝ × Matrix.specialUnitaryGroup n ℂ => (deriv p z.1).val z.2) := by
  borelize ↥(specialUnitaryPolynomialSpace (n := n) d)
  exact (specialUnitaryPolynomial_clm_eval_continuous d
    (ContinuousLinearMap.id ℝ _)).measurable.comp
      (((measurable_deriv p).comp measurable_fst).prodMk measurable_snd)

/-- The phase derivative has a uniform scalar evaluation bound. -/
theorem specialUnitaryPolynomialFamily_deriv_sq_le (d : ℕ) {K : NNReal}
    {p : ℝ → specialUnitaryPolynomialSpace (n := n) d} (hp : LipschitzWith K p)
    (t : ℝ) (U : Matrix.specialUnitaryGroup n ℂ) :
    (deriv p t).val U ^ 2 ≤ (K : ℝ) ^ 2 := by
  have h := (specialUnitaryPolynomial_norm_eval_le d (deriv p t) U).trans
    (norm_deriv_le_of_lipschitz hp)
  simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) h 2

/-- Squared phase derivatives are integrable over the normalized interval/SU product. -/
theorem specialUnitaryPolynomialFamily_deriv_sq_integrable (d : ℕ) (L : ℝ) (hL : 0 < L)
    {K : NNReal} {p : ℝ → specialUnitaryPolynomialSpace (n := n) d} (hp : LipschitzWith K p) :
    Integrable (fun z : Icc (0 : ℝ) L × Matrix.specialUnitaryGroup n ℂ =>
      (deriv p z.1.val).val z.2 ^ 2) ((intervalUniform L).prod (specialUnitaryHaar n)) := by
  letI : Fact (0 < L) := ⟨hL⟩
  have hm : Measurable (fun z : Icc (0 : ℝ) L × Matrix.specialUnitaryGroup n ℂ =>
      (deriv p z.1.val).val z.2) :=
    (specialUnitaryPolynomialFamily_deriv_measurable d p).comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  apply (integrable_const ((K : ℝ) ^ 2)).mono' (hm.pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact specialUnitaryPolynomialFamily_deriv_sq_le d hp z.1.val z.2

/-- Every fixed SU evaluation has integrable phase-derivative square. -/
theorem specialUnitaryPolynomialFamily_deriv_sq_integrable_slice (d : ℕ) (L : ℝ) (hL : 0 < L)
    {K : NNReal} {p : ℝ → specialUnitaryPolynomialSpace (n := n) d} (hp : LipschitzWith K p)
    (U : Matrix.specialUnitaryGroup n ℂ) :
    Integrable (fun t : Icc (0 : ℝ) L => (deriv p t.val).val U ^ 2) (intervalUniform L) := by
  letI : Fact (0 < L) := ⟨hL⟩
  have hm : Measurable (fun t : Icc (0 : ℝ) L => (deriv p t.val).val U) :=
    (specialUnitaryPolynomialFamily_deriv_measurable d p).comp
      (measurable_subtype_coe.prodMk (measurable_const (a := U)))
  apply (integrable_const ((K : ℝ) ^ 2)).mono' (hm.pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact specialUnitaryPolynomialFamily_deriv_sq_le d hp t.val U

/-- SU carré-du-champ energy is jointly continuous along any continuous polynomial family. -/
theorem specialUnitaryPolynomialFamily_gamma_continuous (d : ℕ)
    {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι]
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {p : X → specialUnitaryPolynomialSpace (n := n) d} (hp : Continuous p) :
    Continuous (fun z : X × Matrix.specialUnitaryGroup n ℂ =>
      specialUnitaryGamma b (p z.1).val (p z.1).val z.2) := by
  simp_rw [specialUnitaryGamma_eq b (p _).val.contMDiff (p _).val.contMDiff]
  apply continuous_finset_sum
  intro i _
  have hD := specialUnitaryPolynomialFamily_continuous d
    ((specialUnitaryPolynomialDerivCLM (b i) d).continuous.comp hp)
  exact hD.mul hD

end LogSobolev
