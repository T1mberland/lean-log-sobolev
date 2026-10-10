module

public import LogSobolev.Unitary.PhasePeriodicity
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-! # The short-interval Haar decomposition

The proof of Meckes–Meckes Lemma 16 uses SU-Haar invariance and periodicity
of the averaged phase distribution. All measures are the concrete normalized
measures constructed in this project.
-/

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius BoundedContinuousFunction

namespace LogSobolev

/-- Integration against the short-interval phase pushforward, written as
an ordinary normalized iterated integral. -/
theorem integral_map_intervalPhaseMap (N : ℕ) (hN : 0 < N)
    (f : Matrix.unitaryGroup (Fin N) ℂ →ᵇ ℝ) :
    (∫ U, f U ∂Measure.map (intervalPhaseMap N) (phaseDomainMeasure N)) =
      (phaseIntervalLength N)⁻¹ * ∫ t in 0..phaseIntervalLength N,
        ∫ V, f (phaseMap N (WithLp.toLp 2 (t, V))) ∂specialUnitaryHaar (Fin N) := by
  letI : Fact (0 < phaseIntervalLength N) := ⟨phaseIntervalLength_pos N hN⟩
  have hc := (intervalPhaseMap_lipschitz N hN).continuous
  rw [integral_map hc.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  unfold phaseDomainMeasure
  rw [integral_map (WithLp.measurable_toLp 2 _).aemeasurable
    (show AEStronglyMeasurable (fun x : PhaseDomain N => f (intervalPhaseMap N x)) _ from
      (f.continuous.comp hc).aestronglyMeasurable)]
  have hi : Integrable (fun p : PhaseInterval N × Matrix.specialUnitaryGroup (Fin N) ℂ =>
      f (intervalPhaseMap N (WithLp.toLp 2 p)))
      ((intervalUniform (phaseIntervalLength N)).prod (specialUnitaryHaar (Fin N))) := by
    exact (f.compContinuous ⟨_, hc.comp (WithLp.prod_continuous_toLp 2 _ _)⟩).integrable _
  rw [integral_prod _ hi]
  change (∫ t : PhaseInterval N, ∫ V,
    f (phaseMap N (WithLp.toLp 2 (t.val, V))) ∂specialUnitaryHaar (Fin N)
    ∂intervalUniform (phaseIntervalLength N)) = _
  rw [intervalUniform, integral_smul_measure, integral_subtype_comap measurableSet_Icc
      (fun t => ∫ V, f (phaseMap N (WithLp.toLp 2 (t, V))) ∂specialUnitaryHaar (Fin N)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
      (phaseIntervalLength_pos N hN).le]
  simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal (phaseIntervalLength_pos N hN).le]

/-- SU averaging absorbs left multiplication in SU. -/
theorem circleAverage_mul_left {n : Type*} [Fintype n] [DecidableEq n] (w z : Circle)
    (W : Matrix.specialUnitaryGroup n ℂ)
    (f : Matrix.unitaryGroup n ℂ → ℝ) :
    (∫ V, f (circleSpecialUnitaryMap (w, W) * circleSpecialUnitaryMap (z, V))
      ∂specialUnitaryHaar n) =
    ∫ V, f (circleSpecialUnitaryMap (w * z, V)) ∂specialUnitaryHaar n := by
  simp_rw [← map_mul]
  exact integral_mul_left_eq_self (fun V => f (circleSpecialUnitaryMap (w * z, V))) W

/-- Left translation on U becomes a shift of the SU-averaged phase coordinate. -/
theorem phaseAverage_mul_left (N : ℕ) (hN : 0 < N)
    (g : Matrix.unitaryGroup (Fin N) ℂ) :
    ∃ s : ℝ, ∀ (f : Matrix.unitaryGroup (Fin N) ℂ → ℝ) (t : ℝ),
      (∫ V, f (g * phaseMap N (WithLp.toLp 2 (t, V))) ∂specialUnitaryHaar (Fin N)) =
      ∫ V, f (phaseMap N (WithLp.toLp 2 (t + s, V))) ∂specialUnitaryHaar (Fin N) := by
  obtain ⟨⟨w, W⟩, rfl⟩ := circleSpecialUnitaryMap_surjective
    (n := Fin N) (by simpa using hN) g
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff (w : ℂ)).mp (Circle.norm_coe w)
  have hw : Circle.exp θ = w := Circle.ext hθ
  have ha : Real.sqrt (2 / (N : ℝ)) ≠ 0 := ne_of_gt (by positivity)
  refine ⟨θ / Real.sqrt (2 / (N : ℝ)), ?_⟩
  intro f t
  simp_rw [← circleSpecialUnitaryMap_exp]
  rw [circleAverage_mul_left, ← hw, ← Circle.exp_add]
  have he : θ + Real.sqrt (2 / (N : ℝ)) * t =
      Real.sqrt (2 / (N : ℝ)) * (t + θ / Real.sqrt (2 / (N : ℝ))) := by
    rw [mul_add, mul_div_cancel₀ θ ha, add_comm]
  rw [he]

/-- Meckes–Meckes Lemma 16 on the exact interval and L² product domain.
The image is normalized Haar on the actual U(N), including N = 1.
This measure identity asserts no logarithmic Sobolev inequality. -/
theorem map_intervalPhaseMap (N : ℕ) (hN : 0 < N) :
    Measure.map (intervalPhaseMap N) (phaseDomainMeasure N) = unitaryHaar (Fin N) := by
  let μ := Measure.map (intervalPhaseMap N) (phaseDomainMeasure N)
  letI := phaseDomainMeasure_probability N hN
  letI : IsProbabilityMeasure μ := inferInstance
  haveI : TopologicalSpace.PseudoMetrizableSpace (Matrix.unitaryGroup (Fin N) ℂ) :=
    ⟨⟨inferInstance, rfl, inferInstance⟩⟩
  have hinv : μ.IsMulLeftInvariant := by
    constructor
    intro g
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    rw [integral_map (measurable_const_mul g).aemeasurable
      f.continuous.aestronglyMeasurable]
    let fg := f.compContinuous ⟨fun U => g * U, continuous_const.mul continuous_id⟩
    change (∫ U, fg U ∂μ) = ∫ U, f U ∂μ
    rw [integral_map_intervalPhaseMap N hN fg, integral_map_intervalPhaseMap N hN f]
    obtain ⟨s, hs⟩ := phaseAverage_mul_left N hN g
    congr 1
    change (∫ t in 0..phaseIntervalLength N,
      ∫ V, f (g * phaseMap N (WithLp.toLp 2 (t, V))) ∂specialUnitaryHaar (Fin N)) = _
    simp_rw [hs]
    rw [intervalIntegral.integral_comp_add_right
      (fun t => ∫ V, f (phaseMap N (WithLp.toLp 2 (t, V))) ∂specialUnitaryHaar (Fin N)) s]
    simpa only [zero_add, add_zero, add_comm] using
      phaseAverage_intervalIntegral_translate N hN f f.continuous.measurable s 0
  letI := hinv
  exact eq_unitaryHaar μ

end LogSobolev
