import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Order.Compact

/-! # Positivity from a compact-space minimum principle

A differentiable evolution whose time derivative is nonnegative at each spatial
minimum preserves nonnegative initial values. Compactness supplies a minimum on
space-time rectangles; adding a small positive linear time function makes the
argument strict. This is an elementary maximum principle, not a heat-existence
or semigroup assumption.
-/

open Filter Set Topology

namespace LogSobolev

/-- At a minimum relative to a left interval, a two-sided derivative is nonpositive. -/
theorem HasDerivAt.nonpos_of_min_on_left {f : ℝ → ℝ} {a t v : ℝ}
    (hd : HasDerivAt f v t) (hat : a < t) (hm : ∀ r ∈ Icc a t, f t ≤ f r) : v ≤ 0 := by
  apply le_of_tendsto (hd.tendsto_slope.mono_left (nhdsLT_le_nhdsNE t))
  filter_upwards [(eventually_gt_nhds hat).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with r har hrt
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hm r ⟨har.le, hrt.le⟩))
    (sub_nonpos.mpr hrt.le)

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Strict minimum principle for a supplied evolution on a compact space. -/
theorem nonneg_of_compact_strict_minimum_principle
    {F Q : ℝ → X → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hF : Continuous (Function.uncurry F))
    (hd : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivAt (fun r => F r x) (Q t x) t)
    (hmin : ∀ t ∈ Ioc 0 T, ∀ x, (∀ y, F t x ≤ F t y) → 0 < Q t x)
    (hinit : ∀ x, 0 ≤ F 0 x) : ∀ x, 0 ≤ F T x := by
  intro x
  by_contra hn
  have hn' : F T x < 0 := lt_of_not_ge hn
  obtain ⟨p, hp, hmp⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set X))).exists_isMinOn
    ⟨(0, x), ⟨⟨le_rfl, hT⟩, mem_univ _⟩⟩ hF.continuousOn
  have hmp' := isMinOn_iff.mp hmp
  have hpT : Function.uncurry F p ≤ Function.uncurry F (T, x) :=
    hmp' (T, x) ⟨⟨hT, le_rfl⟩, mem_univ x⟩
  have hneg : F p.1 p.2 < 0 := lt_of_le_of_lt hpT hn'
  have hp0 : 0 < p.1 := by
    have hne : p.1 ≠ 0 := by
      intro he
      have hi := hinit p.2
      rw [he] at hneg
      linarith
    exact lt_of_le_of_ne hp.1.1 (Ne.symm hne)
  have hsp : ∀ y, F p.1 p.2 ≤ F p.1 y := fun y => hmp' (p.1, y) ⟨hp.1, mem_univ y⟩
  have hleft : ∀ r ∈ Icc 0 p.1, F p.1 p.2 ≤ F r p.2 := by
    intro r hr
    exact hmp' (r, p.2) ⟨⟨hr.1, hr.2.trans hp.1.2⟩, mem_univ _⟩
  have hle := HasDerivAt.nonpos_of_min_on_left (hd p.1 ⟨hp0, hp.1.2⟩ p.2) hp0 hleft
  exact (not_lt_of_ge hle) (hmin p.1 ⟨hp0, hp.1.2⟩ p.2 hsp)

/-- The non-strict compact minimum principle, proved using a positive time perturbation. -/
theorem nonneg_of_compact_minimum_principle
    {F Q : ℝ → X → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hF : Continuous (Function.uncurry F))
    (hd : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivAt (fun r => F r x) (Q t x) t)
    (hmin : ∀ t ∈ Ioc 0 T, ∀ x, (∀ y, F t x ≤ F t y) → 0 ≤ Q t x)
    (hinit : ∀ x, 0 ≤ F 0 x) : ∀ x, 0 ≤ F T x := by
  have he (ε : ℝ) (hε : 0 < ε) : ∀ x, 0 ≤ F T x + ε * T := by
    apply nonneg_of_compact_strict_minimum_principle
      (F := fun t x => F t x + ε * t) (Q := fun t x => Q t x + ε) hT
      (hF.add ((continuous_const (y := ε)).mul continuous_fst))
    · intro t ht x
      simpa only [mul_one] using (hd t ht x).add ((hasDerivAt_id t).const_mul ε)
    · intro t ht x hx
      have hx' : ∀ y, F t x ≤ F t y := fun y => (add_le_add_iff_right _).mp (hx y)
      have h := hmin t ht x hx'
      linarith
    · intro x
      simpa using hinit x
  intro x
  have hlim : Tendsto (fun ε : ℝ => F T x + ε * T) (𝓝[>] 0) (𝓝 (F T x)) := by
    simpa using (continuous_const.add (continuous_id.mul continuous_const)).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact he ε hε x

end LogSobolev
