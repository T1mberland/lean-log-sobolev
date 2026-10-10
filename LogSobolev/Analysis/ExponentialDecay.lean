module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! # Integrating a scalar differential decay inequality

Continuity at time zero suffices; no two-sided derivative at the endpoint is
required. The integrating-factor argument uses Mathlib's derivative criterion
for monotonicity on convex sets.
-/

namespace LogSobolev

/-- `f' ≤ -a f` on positive times implies exponential decay from time zero. -/
theorem le_exp_mul_of_deriv_le {f : ℝ → ℝ} {a : ℝ}
    (hc : ContinuousOn f (Set.Ici 0))
    (hd : ∀ t, 0 < t → DifferentiableAt ℝ f t)
    (hle : ∀ t, 0 < t → deriv f t ≤ -a * f t)
    {t : ℝ} (ht : 0 ≤ t) : f t ≤ Real.exp (-a * t) * f 0 := by
  let g : ℝ → ℝ := fun s => Real.exp (a * s) * f s
  have hg (s : ℝ) (hs : 0 < s) : HasDerivAt g
      (Real.exp (a * s) * (a * f s + deriv f s)) s := by
    convert (((hasDerivAt_id s).const_mul a).exp).mul (hd s hs).hasDerivAt using 1 <;> try rfl
    dsimp [g]
    ring
  have hm : AntitoneOn g (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul hc)
    · intro s hs
      have hs' : 0 < s := by simpa only [interior_Ici, Set.mem_Ioi] using hs
      exact (hg s hs').differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : 0 < s := by simpa only [interior_Ici, Set.mem_Ioi] using hs
      change deriv g s ≤ 0
      rw [(hg s hs').deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [hle s hs'])
  have hb : Real.exp (a * t) * f t ≤ f 0 := by
    simpa only [g, mul_zero, Real.exp_zero, one_mul] using hm (show (0 : ℝ) ∈ Set.Ici 0 by simp) ht ht
  have hh := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-a * t)).le
  have he : Real.exp (-a * t) * Real.exp (a * t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  simpa only [← mul_assoc, he, one_mul] using hh

end LogSobolev
