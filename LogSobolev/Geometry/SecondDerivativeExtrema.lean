module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-! # Necessary second-derivative conditions at local extrema

The usual sign condition is deduced from Mathlib's second-derivative test.
If the sign were wrong, the function would have both a local minimum and a
local maximum, hence would be locally constant, contradicting that sign.
-/

open Filter Topology

namespace LogSobolev

/-- The second derivative at a local minimum is nonnegative. The derivative
operators are Mathlib's totalized derivatives; continuity at the point suffices. -/
theorem secondDeriv_nonneg_of_isLocalMin {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMin f x) (hc : ContinuousAt f x) : 0 ≤ deriv (deriv f) x := by
  by_contra hn
  have hneg : deriv (deriv f) x < 0 := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hm, hmax] with y hy hy'
    exact le_antisymm hy' hy
  have hz := he.deriv.deriv_eq
  simp only [deriv_const'] at hz
  linarith

/-- A version with explicit first and second derivatives, convenient for curves. -/
theorem secondDerivative_nonneg_of_isLocalMin {f g : ℝ → ℝ} {x a : ℝ}
    (hm : IsLocalMin f x) (hf : ∀ y, HasDerivAt f (g y) y)
    (hg : HasDerivAt g a x) : 0 ≤ a := by
  have h := secondDeriv_nonneg_of_isLocalMin hm (hf x).continuousAt
  rw [deriv_eq hf, hg.deriv] at h
  exact h

/-- The corresponding necessary sign condition at a local maximum. -/
theorem secondDerivative_nonpos_of_isLocalMax {f g : ℝ → ℝ} {x a : ℝ}
    (hm : IsLocalMax f x) (hf : ∀ y, HasDerivAt f (g y) y)
    (hg : HasDerivAt g a x) : a ≤ 0 := by
  have h := secondDerivative_nonneg_of_isLocalMin hm.neg (fun y => (hf y).neg) hg.neg
  exact neg_nonneg.mp h

end LogSobolev
