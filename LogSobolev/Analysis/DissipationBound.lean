module

public import LogSobolev.Analysis.ExponentialDecay

@[expose] public section

/-! # An initial bound from dissipation, decay, and a zero limit

A scalar entropy trajectory with derivative `-I`, exponentially bounded
information `I`, and a proved zero limit satisfies the integrated initial bound.
The comparison argument uses derivative monotonicity and continuity at zero;
no improper integral or abstract semigroup criterion is assumed.
-/

open Filter Topology

namespace LogSobolev

/-- Dissipation with exponentially decaying information and zero limiting entropy
implies `E(0) ≤ K/a`. All hypotheses concern explicitly given scalar functions. -/
theorem initial_le_div_of_dissipation_decay {E I : ℝ → ℝ} {a K : ℝ}
    (ha : 0 < a) (hc : ContinuousOn E (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt E (-I t) t)
    (hI : ∀ t, 0 < t → I t ≤ Real.exp (-a * t) * K)
    (hlim : Tendsto E atTop (𝓝 0)) : E 0 ≤ K / a := by
  let g : ℝ → ℝ := fun t => E t - Real.exp (-a * t) * (K / a)
  have hg (t : ℝ) (ht : 0 < t) :
      HasDerivAt g (-I t + Real.exp (-a * t) * K) t := by
    convert (hd t ht).sub ((((hasDerivAt_id t).const_mul (-a)).exp).mul_const (K / a)) using 1 <;> try rfl
    dsimp
    field_simp [ne_of_gt ha]
    ring
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (hc.sub ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        continuous_const).continuousOn)
    · intro t ht
      have ht' : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
      exact (hg t ht').differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
      change 0 ≤ deriv g t
      rw [(hg t ht').deriv]
      linarith [hI t ht']
  have he : Tendsto (fun t : ℝ => Real.exp (-a * t)) atTop (𝓝 0) := by
    simpa only [neg_mul, Function.comp_def, id_eq] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop ha)
  have hglim : Tendsto g atTop (𝓝 0) := by
    simpa only [zero_mul, sub_zero] using hlim.sub (he.mul_const (K / a))
  have hb : g 0 ≤ 0 := ge_of_tendsto hglim (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hmono (by simp) ht ht)
  simpa only [g, mul_zero, Real.exp_zero, one_mul, sub_nonpos] using hb

end LogSobolev
