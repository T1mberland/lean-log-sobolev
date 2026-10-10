import LogSobolev.Measure.ProductEntropy
import LogSobolev.Measure.EntropyVariational
import LogSobolev.Measure.ParametricEntropy
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Binary entropy subadditivity

The variational entropy bound controls the entropy of a marginal by the
average entropy of the opposite slices. This supplies the measure-theoretic
step of LSI tensorization independently of derivatives and metric slopes.
-/

open MeasureTheory Filter
open scoped Topology

namespace LogSobolev

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {g : X × Y → ℝ}

/-- Entropy is convex under averaging. This version assumes a positive marginal
and an integrable cross log moment; both hold for positive continuous densities
on compact product spaces. No energy or logarithmic Sobolev bound is assumed. -/
theorem entropy_marginal_le_integral_entropy
    (hg : 0 ≤ᵐ[μ.prod ν] g) (hi : Integrable g (μ.prod ν))
    (hl : Integrable (fun p => g p * Real.log (g p)) (μ.prod ν))
    (hm : ∀ᵐ x ∂μ, 0 < ∫ y, g (x, y) ∂ν)
    (hM : 0 < ∫ p, g p ∂μ.prod ν)
    (hc : Integrable (fun p => g p * Real.log (∫ y, g (p.1, y) ∂ν)) (μ.prod ν)) :
    entropy μ (fun x => ∫ y, g (x, y) ∂ν) ≤
      ∫ y, entropy μ (fun x => g (x, y)) ∂ν := by
  let m : X → ℝ := fun x => ∫ y, g (x, y) ∂ν
  let M : ℝ := ∫ p, g p ∂μ.prod ν
  let T : X → ℝ := fun x => m x / M
  have hmi : Integrable m μ := hi.integral_prod_left
  have hmass : ∫ x, m x ∂μ = M := (integral_prod _ hi).symm
  have hTi : Integrable T μ := hmi.div_const M
  have hTm : ∫ x, T x ∂μ = 1 := by
    rw [show T = fun x => m x / M from rfl, integral_div, hmass, div_self hM.ne']
  have hTp : ∀ᵐ x ∂μ, 0 < T x := hm.mono fun x hx => div_pos hx hM
  have hlog : ∀ᵐ x ∂μ, Real.log (T x) = Real.log (m x) - Real.log M :=
    hm.mono fun x hx => Real.log_div hx.ne' hM.ne'
  have hcross : Integrable (fun p => g p * Real.log (T p.1)) (μ.prod ν) := by
    apply (hc.sub (hi.mul_const (Real.log M))).congr
    have hlae : ∀ᵐ p ∂μ.prod ν, Real.log (T p.1) = Real.log (m p.1) - Real.log M :=
      (measurePreserving_fst (μ := μ) (ν := ν)).quasiMeasurePreserving.ae hlog
    filter_upwards [hlae] with p hp
    simp only [Pi.sub_apply]
    rw [hp]
    ring
  have hgs : 0 ≤ᵐ[ν.prod μ] (fun p : Y × X => g (p.2, p.1)) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hg
  have hs : ∀ᵐ y ∂ν, (∫ x, g (x, y) * Real.log (T x) ∂μ) ≤
      entropy μ (fun x => g (x, y)) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hgs, hi.prod_left_ae,
      hl.prod_left_ae, hcross.prod_left_ae] with y hgy hiy hly hcy
    exact integral_mul_log_le_entropy hgy hiy hly hTp hTi hTm hcy
  have hbound := integral_mono_ae hcross.integral_prod_right
    (integrable_slice_entropy hgs hi.swap hl.swap) hs
  have hswap : (∫ y, ∫ x, g (x, y) * Real.log (T x) ∂μ ∂ν) =
      ∫ x, m x * Real.log (T x) ∂μ := by
    rw [← integral_integral_swap hcross]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => integral_mul_const _ _
  rw [hswap] at hbound
  have hml := integrable_marginal_mul_log hg hi hl
  have he : (∫ x, m x * Real.log (T x) ∂μ) = entropy μ m := by
    calc
      _ = ∫ x, m x * Real.log (m x) - m x * Real.log M ∂μ := by
        apply integral_congr_ae
        filter_upwards [hlog] with x hx
        rw [hx, mul_sub]
      _ = _ := by
        rw [integral_sub hml (hmi.mul_const _), integral_mul_const]
        simp only [entropy, hmass]
        rfl
  rwa [he] at hbound

/-- Binary entropy tensorization under the explicit marginal log hypotheses. -/
theorem entropy_prod_le_integral_entropy_add
    (hg : 0 ≤ᵐ[μ.prod ν] g) (hi : Integrable g (μ.prod ν))
    (hl : Integrable (fun p => g p * Real.log (g p)) (μ.prod ν))
    (hm : ∀ᵐ x ∂μ, 0 < ∫ y, g (x, y) ∂ν)
    (hM : 0 < ∫ p, g p ∂μ.prod ν)
    (hc : Integrable (fun p => g p * Real.log (∫ y, g (p.1, y) ∂ν)) (μ.prod ν)) :
    entropy (μ.prod ν) g ≤
      (∫ x, entropy ν (fun y => g (x, y)) ∂μ) +
        ∫ y, entropy μ (fun x => g (x, y)) ∂ν := by
  rw [entropy_prod_chain hg hi hl]
  exact add_le_add le_rfl (entropy_marginal_le_integral_entropy hg hi hl hm hM hc)

section Compact

variable [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
  [BorelSpace X] [BorelSpace Y]

/-- On compact metric probability spaces, a positive continuous joint density
satisfies binary entropy subadditivity. All integrability and marginal positivity
conditions are established here. -/
theorem entropy_prod_le_integral_entropy_add_of_continuous_pos
    (hg : Continuous g) (hpos : ∀ p, 0 < g p) :
    entropy (μ.prod ν) g ≤
      (∫ x, entropy ν (fun y => g (x, y)) ∂μ) +
        ∫ y, entropy μ (fun x => g (x, y)) ∂ν := by
  have hi : Integrable g (μ.prod ν) := hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hl : Integrable (fun p => g p * Real.log (g p)) (μ.prod ν) :=
    (Real.continuous_mul_log.comp hg).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hmc : Continuous (fun x => ∫ y, g (x, y) ∂ν) := by
    simpa using continuous_parametric_integral_of_continuous
      (μ := ν) (f := fun x y => g (x, y)) hg isCompact_univ
  have hmp (x : X) : 0 < ∫ y, g (x, y) ∂ν := by
    have hiy : Integrable (fun y => g (x, y)) ν := (hg.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    apply (integral_pos_iff_support_of_nonneg (fun y => (hpos (x, y)).le) hiy).mpr
    have hs : Function.support (fun y => g (x, y)) = Set.univ := by
      ext y
      simp [Function.mem_support, (hpos (x, y)).ne']
    simp [hs]
  have hM : 0 < ∫ p, g p ∂μ.prod ν := by
    apply (integral_pos_iff_support_of_nonneg (fun p => (hpos p).le) hi).mpr
    have hs : Function.support g = Set.univ := by
      ext p
      simp [Function.mem_support, (hpos p).ne']
    simp [hs]
  have hc : Integrable (fun p => g p * Real.log (∫ y, g (p.1, y) ∂ν)) (μ.prod ν) :=
    (hg.mul ((hmc.log (fun x => (hmp x).ne')).comp continuous_fst)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact entropy_prod_le_integral_entropy_add
    (Eventually.of_forall fun p => (hpos p).le) hi hl (Eventually.of_forall hmp) hM hc

/-- Binary entropy subadditivity for every nonnegative continuous density on
compact metric probability spaces, including densities with zeros. -/
theorem entropy_prod_le_integral_entropy_add_of_continuous
    (hg : Continuous g) (hn : ∀ p, 0 ≤ g p) :
    entropy (μ.prod ν) g ≤
      (∫ x, entropy ν (fun y => g (x, y)) ∂μ) +
        ∫ y, entropy μ (fun x => g (x, y)) ∂ν := by
  have hleft : Continuous (fun t : ℝ => entropy (μ.prod ν) (fun p => g p + t)) :=
    continuous_parametric_entropy (g := fun t p => g p + t) ((hg.comp continuous_snd).add continuous_fst)
  have hfirst : Continuous (fun t : ℝ => ∫ x, entropy ν (fun y => g (x, y) + t) ∂μ) := by
    have he : Continuous (fun q : ℝ × X => entropy ν (fun y => g (q.2, y) + q.1)) :=
      continuous_parametric_entropy (g := fun (q : ℝ × X) y => g (q.2, y) + q.1)
        ((hg.comp (continuous_fst.snd.prodMk continuous_snd)).add continuous_fst.fst)
    simpa using continuous_parametric_integral_of_continuous (μ := μ)
      (f := fun t x => entropy ν (fun y => g (x, y) + t)) he isCompact_univ
  have hsecond : Continuous (fun t : ℝ => ∫ y, entropy μ (fun x => g (x, y) + t) ∂ν) := by
    have he : Continuous (fun q : ℝ × Y => entropy μ (fun x => g (x, q.2) + q.1)) :=
      continuous_parametric_entropy (g := fun (q : ℝ × Y) x => g (x, q.2) + q.1)
        ((hg.comp (continuous_snd.prodMk continuous_fst.snd)).add continuous_fst.fst)
    simpa using continuous_parametric_integral_of_continuous (μ := ν)
      (f := fun t y => entropy μ (fun x => g (x, y) + t)) he isCompact_univ
  have heps : ∀ᶠ t : ℝ in 𝓝[>] 0,
      entropy (μ.prod ν) (fun p => g p + t) ≤
        (∫ x, entropy ν (fun y => g (x, y) + t) ∂μ) +
          ∫ y, entropy μ (fun x => g (x, y) + t) ∂ν := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact entropy_prod_le_integral_entropy_add_of_continuous_pos
      (hg.add continuous_const) (fun p => add_pos_of_nonneg_of_pos (hn p) ht)
  have h := le_of_tendsto_of_tendsto
    (hleft.continuousAt.mono_left nhdsWithin_le_nhds)
    ((hfirst.add hsecond).continuousAt.mono_left nhdsWithin_le_nhds) heps
  simpa only [Pi.add_apply, add_zero] using h

end Compact

end LogSobolev
