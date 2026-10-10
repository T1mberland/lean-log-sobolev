module

public import LogSobolev.Geometry.SecondDerivativeExtrema
public import LogSobolev.Unitary.SpecialUnitaryFlow
public import LogSobolev.Unitary.SpecialUnitaryGenerator

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Maximum principle for the actual SU generator

At a local extremum, each invariant first derivative vanishes and each squared
invariant derivative has the appropriate sign. This follows by restricting the
function to the actual curves `U exp(tA)`, whose derivatives are already proved.
The generator maximum principle is needed for positivity of a constructed heat
evolution; it does not presume such an evolution exists.
-/

open Matrix
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {f : Matrix.specialUnitaryGroup n ℂ → ℝ} {U : Matrix.specialUnitaryGroup n ℂ}

/-- An invariant first derivative vanishes at a local minimum. -/
theorem specialUnitaryDeriv_eq_zero_at_min
    (A : specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hm : IsLocalMin f U) : specialUnitaryDeriv A f U = 0 := by
  have hc : ContinuousAt (fun t => U * specialUnitaryExpCurve A t) 0 :=
    continuousAt_const.mul (specialUnitaryExpCurve_lipschitz A).continuous.continuousAt
  have hm' : IsLocalMin f (U * specialUnitaryExpCurve A 0) := by simpa using hm
  have h := (hm'.comp_continuous (g := fun t => U * specialUnitaryExpCurve A t) (b := 0) hc).hasDerivAt_eq_zero
    (specialUnitary_hasDerivAt_mul_exp A U hf 0)
  simpa only [specialUnitaryExpCurve_zero, mul_one] using h

/-- Each squared invariant derivative is nonnegative at a local minimum. -/
theorem specialUnitaryDeriv_twice_nonneg_at_min
    (A : specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hm : IsLocalMin f U) : 0 ≤ specialUnitaryDeriv A (specialUnitaryDeriv A f) U := by
  have hc : ContinuousAt (fun t => U * specialUnitaryExpCurve A t) 0 :=
    continuousAt_const.mul (specialUnitaryExpCurve_lipschitz A).continuous.continuousAt
  have hm' : IsLocalMin f (U * specialUnitaryExpCurve A 0) := by simpa using hm
  have h := secondDerivative_nonneg_of_isLocalMin (hm'.comp_continuous (g := fun t => U * specialUnitaryExpCurve A t) (b := 0) hc)
    (fun t => specialUnitary_hasDerivAt_mul_exp A U hf t)
    (specialUnitary_hasDerivAt_mul_exp A U (specialUnitaryDeriv_contMDiff A hf) 0)
  simpa only [specialUnitaryExpCurve_zero, mul_one] using h

/-- Each squared invariant derivative is nonpositive at a local maximum. -/
theorem specialUnitaryDeriv_twice_nonpos_at_max
    (A : specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hm : IsLocalMax f U) : specialUnitaryDeriv A (specialUnitaryDeriv A f) U ≤ 0 := by
  have hc : ContinuousAt (fun t => U * specialUnitaryExpCurve A t) 0 :=
    continuousAt_const.mul (specialUnitaryExpCurve_lipschitz A).continuous.continuousAt
  have hm' : IsLocalMax f (U * specialUnitaryExpCurve A 0) := by simpa using hm
  have h := secondDerivative_nonpos_of_isLocalMax (hm'.comp_continuous (g := fun t => U * specialUnitaryExpCurve A t) (b := 0) hc)
    (fun t => specialUnitary_hasDerivAt_mul_exp A U hf t)
    (specialUnitary_hasDerivAt_mul_exp A U (specialUnitaryDeriv_contMDiff A hf) 0)
  simpa only [specialUnitaryExpCurve_zero, mul_one] using h

variable {ι : Type*} [Fintype ι]

/-- Positive minimum principle for the actual sum-of-squares generator. -/
theorem specialUnitary_laplacian_nonneg_at_min
    (b : ι → specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hm : IsLocalMin f U) : 0 ≤ specialUnitaryLaplacian b f U :=
  Finset.sum_nonneg fun i _ => specialUnitaryDeriv_twice_nonneg_at_min (b i) hf hm

/-- Negative maximum principle for the actual sum-of-squares generator. -/
theorem specialUnitary_laplacian_nonpos_at_max
    (b : ι → specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hm : IsLocalMax f U) : specialUnitaryLaplacian b f U ≤ 0 :=
  Finset.sum_nonpos fun i _ => specialUnitaryDeriv_twice_nonpos_at_max (b i) hf hm

/-- The actual carré du champ vanishes at a local minimum. -/
theorem specialUnitaryGamma_eq_zero_at_min
    (b : ι → specialUnitaryLieAlgebra (n := n))
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hm : IsLocalMin f U) : specialUnitaryGamma b f f U = 0 := by
  rw [specialUnitaryGamma_eq b hf hf]
  simp only [specialUnitaryDeriv_eq_zero_at_min _ hf hm, zero_mul, Finset.sum_const_zero]

end LogSobolev
