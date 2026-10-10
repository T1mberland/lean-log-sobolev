module

public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Order.Filter.ENNReal
public import Mathlib.Topology.Instances.ENNReal.Lemmas

@[expose] public section

/-! # Local metric slope

The upper local metric slope from Meckes–Meckes, Appendix, takes values in
`ℝ≥0∞`. At the base point the difference quotient is zero. Taking the limsup
over the full neighborhood filter thus gives zero at isolated points and the
usual punctured limsup elsewhere. Keeping the extended value avoids silently
turning an infinite slope into zero.
-/

open Filter
open scoped Topology ENNReal NNReal

namespace LogSobolev

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- Upper local slope, with value zero at isolated points. -/
noncomputable def localSlope (f : X → ℝ) (x : X) : ℝ≥0∞ :=
  limsup (fun y => ENNReal.ofReal (dist (f y) (f x) / dist y x)) (𝓝 x)

/-- The full-neighborhood convention equals the punctured limsup, including
isolated points (where the extended-order limsup over the bottom filter is zero). -/
theorem localSlope_eq_limsup_nhdsNE (f : X → ℝ) (x : X) :
    localSlope f x =
      limsup (fun y => ENNReal.ofReal (dist (f y) (f x) / dist y x)) (𝓝[≠] x) := by
  unfold localSlope
  rw [← nhdsNE_sup_pure x, limsup_sup_filter]
  simp [limsup, limsSup]

@[simp] theorem localSlope_const (c : ℝ) (x : X) :
    localSlope (fun _ => c) x = 0 := by
  simp [localSlope]

/-- A global Lipschitz constant bounds every local slope. -/
theorem localSlope_le_of_lipschitz {f : X → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (x : X) : localSlope f x ≤ K := by
  apply limsup_le_of_le (by isBoundedDefault)
  apply Eventually.of_forall
  intro y
  apply (ENNReal.ofReal_le_coe).2
  by_cases h : y = x
  · simp [h]
  · exact (div_le_iff₀ (dist_pos.mpr h)).2 (hf.dist_le_mul y x)

/-- Local Lipschitz regularity guarantees finite slope, without a global constant. -/
theorem localSlope_le_of_lipschitzOn {f : X → ℝ} {K : ℝ≥0} {s : Set X} {x : X}
    (hK : LipschitzOnWith K f s) (hs : s ∈ 𝓝 x) : localSlope f x ≤ K := by
  have hx : x ∈ s := mem_of_mem_nhds hs
  apply limsup_le_of_le (by isBoundedDefault)
  filter_upwards [hs] with y hy
  apply (ENNReal.ofReal_le_coe).2
  by_cases h : y = x
  · simp [h]
  · exact (div_le_iff₀ (dist_pos.mpr h)).2 (hK.dist_le_mul y hy x hx)

/-- Local Lipschitz regularity guarantees finite slope, without a global constant. -/
theorem localSlope_lt_top {f : X → ℝ} (hf : LocallyLipschitz f) (x : X) :
    localSlope f x < ⊤ := by
  obtain ⟨K, s, hs, hK⟩ := hf x
  exact (localSlope_le_of_lipschitzOn hK hs).trans_lt ENNReal.coe_lt_top

/-- Pointwise chain bound for local slope under a Lipschitz map.
No differentiability, injectivity, or measure hypotheses are needed. -/
theorem localSlope_comp_le {T : X → Y} {K : ℝ≥0} (hT : LipschitzWith K T)
    (f : Y → ℝ) (x : X) :
    localSlope (f ∘ T) x ≤ (K : ℝ≥0∞) * localSlope f (T x) := by
  have hquot (y : X) :
      dist (f (T y)) (f (T x)) / dist y x ≤
        (K : ℝ) * (dist (f (T y)) (f (T x)) / dist (T y) (T x)) := by
    by_cases hy : y = x
    · simp [hy]
    by_cases ht : T y = T x
    · simp [ht]
    have hd := hT.dist_le_mul y x
    have hxpos := dist_pos.mpr hy
    have htpos := dist_pos.mpr ht
    apply (div_le_iff₀ hxpos).2
    calc
      dist (f (T y)) (f (T x)) =
          (dist (f (T y)) (f (T x)) / dist (T y) (T x)) * dist (T y) (T x) :=
        (div_mul_cancel₀ _ htpos.ne').symm
      _ ≤ (dist (f (T y)) (f (T x)) / dist (T y) (T x)) *
          ((K : ℝ) * dist y x) :=
        mul_le_mul_of_nonneg_left hd (div_nonneg dist_nonneg dist_nonneg)
      _ = _ := by ring
  unfold localSlope
  calc
    _ ≤ limsup (fun y => (K : ℝ≥0∞) *
        ENNReal.ofReal (dist (f (T y)) (f (T x)) / dist (T y) (T x))) (𝓝 x) := by
      refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
      apply Eventually.of_forall
      intro y
      simpa only [Function.comp_apply, ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal]
        using ENNReal.ofReal_le_ofReal (hquot y)
    _ = (K : ℝ≥0∞) * limsup
        (fun y => ENNReal.ofReal (dist (f (T y)) (f (T x)) / dist (T y) (T x)))
        (𝓝 x) := ENNReal.limsup_const_mul_of_ne_top ENNReal.coe_ne_top
    _ ≤ _ := by
      apply mul_le_mul_right
      exact limsup_le_limsup_of_le (u := fun y : Y =>
        ENNReal.ofReal (dist (f y) (f (T x)) / dist y (T x))) (hT.continuous.tendsto x)

/-- Local slope is invariant under a surjective isometry of the domain. -/
theorem localSlope_comp_isometryEquiv (e : X ≃ᵢ Y) (f : Y → ℝ) (x : X) :
    localSlope (f ∘ e) x = localSlope f (e x) := by
  apply le_antisymm
  · simpa using localSlope_comp_le e.isometry.lipschitz f x
  · simpa [Function.comp_def] using
      localSlope_comp_le e.symm.isometry.lipschitz (f ∘ e) (e x)

end LogSobolev
