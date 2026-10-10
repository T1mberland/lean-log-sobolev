module

public import LogSobolev.Geometry.IntervalMetricLSI
public import LogSobolev.Unitary.PhaseHaar
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Logarithmic Sobolev inequality on U(1)

The proved interval LSI and the exact Haar decomposition give U(1) the
constant `π²/2`, hence the requested constant `6`, for all locally Lipschitz
real observables. The metric is the unnormalized Hilbert–Schmidt metric on
the actual one-dimensional matrix unitary group. No circle LSI is assumed.
-/

open MeasureTheory Matrix
open scoped Matrix.Norms.Frobenius NNReal ENNReal

namespace LogSobolev

/-- The actual matrix group SU(1) contains only identity. -/
theorem specialUnitary_fin_one_eq_one (V : Matrix.specialUnitaryGroup (Fin 1) ℂ) : V = 1 := by
  apply Subtype.ext
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  have hd := V.prop.2
  simpa [Matrix.det_fin_one] using hd

/-- The phase map on the paper's one-dimensional interval. -/
noncomputable def unitaryOnePhaseMap (t : PhaseInterval 1) : Matrix.unitaryGroup (Fin 1) ℂ :=
  phaseMul (Real.sqrt 2) t.val 1

/-- Fixing the trivial SU factor gives the sharper `sqrt(2)` Lipschitz constant. -/
theorem unitaryOnePhaseMap_lipschitz :
    LipschitzWith ⟨Real.sqrt 2, Real.sqrt_nonneg 2⟩ unitaryOnePhaseMap := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change dist (unitaryOnePhaseMap s) (unitaryOnePhaseMap t) ≤ Real.sqrt 2 * dist s t
  have h := phaseMul_dist_le (Real.sqrt 2) s.val t.val
    (1 : Matrix.unitaryGroup (Fin 1) ℂ) 1
  simpa [unitaryOnePhaseMap, abs_of_nonneg (Real.sqrt_nonneg 2), Subtype.dist_eq, NNReal.coe_mk, Real.dist_eq] using h

/-- The phase map pushes actual normalized interval measure to actual U(1) Haar. -/
theorem map_unitaryOnePhaseMap :
    Measure.map unitaryOnePhaseMap (intervalUniform (phaseIntervalLength 1)) = unitaryHaar (Fin 1) := by
  have he : (intervalPhaseMap 1 ∘ (WithLp.toLp 2 :
      PhaseInterval 1 × Matrix.specialUnitaryGroup (Fin 1) ℂ → PhaseDomain 1)) =
      unitaryOnePhaseMap ∘ Prod.fst := by
    funext p
    change phaseMul (Real.sqrt (2 / (Fintype.card (Fin 1) : ℝ))) p.1.val (specialUnitaryInclusion p.2) =
      phaseMul (Real.sqrt 2) p.1.val 1
    rw [specialUnitary_fin_one_eq_one p.2, map_one]
    norm_num
  calc
    _ = Measure.map unitaryOnePhaseMap (Measure.map Prod.fst
        ((intervalUniform (phaseIntervalLength 1)).prod (specialUnitaryHaar (Fin 1)))) := by simp
    _ = Measure.map (unitaryOnePhaseMap ∘ Prod.fst)
        ((intervalUniform (phaseIntervalLength 1)).prod (specialUnitaryHaar (Fin 1))) :=
      Measure.map_map unitaryOnePhaseMap_lipschitz.continuous.measurable measurable_fst
    _ = Measure.map (intervalPhaseMap 1) (phaseDomainMeasure 1) := by
      rw [phaseDomainMeasure, Measure.map_map
        (intervalPhaseMap_lipschitz 1 (by decide)).continuous.measurable
        (WithLp.measurable_toLp 2 _), he]
    _ = _ := map_intervalPhaseMap 1 (by decide)

/-- U(1) has metric LSI constant `π²/2`, a bound sufficient for Theorem 15. -/
theorem unitary_fin_one_metricLSI_pi :
    MetricLSI (unitaryHaar (Fin 1)) (Real.toNNReal (Real.pi ^ 2 / 2)) := by
  have h := (intervalUniform_metricLSI (phaseIntervalLength 1)
    (phaseIntervalLength_pos 1 (by decide))).map unitaryOnePhaseMap_lipschitz
  rw [map_unitaryOnePhaseMap] at h
  let k : NNReal := ⟨Real.sqrt 2, Real.sqrt_nonneg 2⟩
  have hc : k ^ 2 *
      Real.toNNReal (phaseIntervalLength 1 ^ 2 / 8) = Real.toNNReal (Real.pi ^ 2 / 2) := by
    apply NNReal.eq
    change (Real.sqrt 2) ^ 2 * (Real.toNNReal (phaseIntervalLength 1 ^ 2 / 8) : ℝ) =
      (Real.toNNReal (Real.pi ^ 2 / 2) : ℝ)
    rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
    simp only [phaseIntervalLength, Nat.cast_one, div_one, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  change MetricLSI (unitaryHaar (Fin 1)) (k ^ 2 * _) at h
  rwa [hc] at h

/-- The N=1 case of the requested U(N) LSI, for all locally Lipschitz observables. -/
theorem unitary_fin_one_metricLSI : MetricLSI (unitaryHaar (Fin 1)) 6 := by
  apply unitary_fin_one_metricLSI_pi.mono
  change Real.toNNReal (Real.pi ^ 2 / 2) ≤ (6 : NNReal)
  apply NNReal.coe_le_coe.mp
  change (Real.toNNReal (Real.pi ^ 2 / 2) : ℝ) ≤ 6
  rw [Real.coe_toNNReal _ (by positivity)]
  have hp := mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d4
  nlinarith

/-- Real entropy form of Theorem 15 in dimension one, with coefficient `12`. -/
theorem unitary_fin_one_entropy_sq_le {f : Matrix.unitaryGroup (Fin 1) ℂ → ℝ}
    (hf : LocallyLipschitz f) :
    entropy (unitaryHaar (Fin 1)) (fun U => f U ^ 2) ≤
      12 * ∫ U, (localSlope f U).toReal ^ 2 ∂unitaryHaar (Fin 1) := by
  convert unitary_fin_one_metricLSI.real_form hf using 1; norm_num

end LogSobolev
