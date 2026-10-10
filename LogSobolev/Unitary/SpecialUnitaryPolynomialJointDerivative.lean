import LogSobolev.Unitary.SpecialUnitaryPolynomialFamily
import LogSobolev.Unitary.SpecialUnitaryFlow

/-! # Joint differentiation of a polynomial family along an SU flow

Finite-dimensional coordinates justify differentiating a moving polynomial
at a moving group point. This combines the parameter derivative and actual
invariant SU derivative without assuming joint smoothness of the family.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Leibniz rule for evaluating a differentiable polynomial curve on an exponential curve. -/
theorem specialUnitaryPolynomial_hasDerivAt_moving_eval (d : ℕ)
    {p : ℝ → specialUnitaryPolynomialSpace (n := n) d}
    {p' : specialUnitaryPolynomialSpace (n := n) d} (hp : HasDerivAt p p' 0)
    (A : specialUnitaryLieAlgebra (n := n)) (U : Matrix.specialUnitaryGroup n ℂ) :
    HasDerivAt (fun s => (p s).val (U * specialUnitaryExpCurve A s))
      (p'.val U + specialUnitaryDeriv A (p 0).val U) 0 := by
  classical
  let P := specialUnitaryPolynomialSpace (n := n) d
  let b := Module.finBasis ℝ P
  have he (v : P) (L : P →L[ℝ] ℝ) :
      (∑ i, b.repr v i * L (b i)) = L v := by
    simpa only [map_sum, map_smul, smul_eq_mul] using congrArg L (b.sum_repr v)
  have hcoord (i) : HasDerivAt (fun s => b.repr (p s) i) (b.repr p' i) 0 :=
    ((b.coord i).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0 hp
  have hspace (i) : HasDerivAt (fun s => (b i).val (U * specialUnitaryExpCurve A s))
      (specialUnitaryDeriv A (b i).val U) 0 := by
    simpa only [specialUnitaryExpCurve_zero, mul_one] using
      specialUnitary_hasDerivAt_mul_exp A U (b i).val.contMDiff 0
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hcoord i).mul (hspace i))
  have hfun : (fun s => ∑ i, b.repr (p s) i * (b i).val (U * specialUnitaryExpCurve A s)) =
      (fun s => (p s).val (U * specialUnitaryExpCurve A s)) := by
    funext s
    exact he (p s) (specialUnitaryPolynomialEval d (U * specialUnitaryExpCurve A s))
  simp only [Pi.mul_apply] at hsum
  rw [hfun] at hsum
  simp only [specialUnitaryExpCurve_zero, mul_one, Finset.sum_add_distrib] at hsum
  have h1 := he p' (specialUnitaryPolynomialEval d U)
  have h2 := he (p 0) ((specialUnitaryPolynomialEval d U).comp
    (specialUnitaryPolynomialDerivCLM A d))
  change (∑ i, b.repr p' i * (b i).val U) = p'.val U at h1
  change (∑ i, b.repr (p 0) i * specialUnitaryDeriv A (b i).val U) =
    specialUnitaryDeriv A (p 0).val U at h2
  rwa [h1, h2] at hsum

/-- The joint rule at an arbitrary phase, with an arbitrary phase speed. -/
theorem specialUnitaryPolynomial_hasDerivAt_phase_flow (d : ℕ)
    {p : ℝ → specialUnitaryPolynomialSpace (n := n) d}
    {p' : specialUnitaryPolynomialSpace (n := n) d} {t : ℝ} (hp : HasDerivAt p p' t)
    (c : ℝ) (A : specialUnitaryLieAlgebra (n := n)) (U : Matrix.specialUnitaryGroup n ℂ) :
    HasDerivAt (fun s => (p (t + c * s)).val (U * specialUnitaryExpCurve A s))
      (c * p'.val U + specialUnitaryDeriv A (p t).val U) 0 := by
  have harg : HasDerivAt (fun s : ℝ => t + c * s) c 0 := by
    simpa only [Pi.add_apply, zero_add, mul_one] using (hasDerivAt_const 0 t).add ((hasDerivAt_id 0).const_mul c)
  have hp0 : HasDerivAt p p' (t + c * 0) := by simpa using hp
  have hq : HasDerivAt (fun s => p (t + c * s)) (c • p') 0 := hp0.scomp 0 harg
  simpa using specialUnitaryPolynomial_hasDerivAt_moving_eval d hq A U

end LogSobolev
