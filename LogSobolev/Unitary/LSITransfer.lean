import LogSobolev.Unitary.PhaseHaar
import LogSobolev.Geometry.CompactRegularity

/-! # Conditional final transfer to U(N)

The geometric and measure-theoretic parts of the reference proof are complete.
The source LSI below is an explicit, still-unproved analytic hypothesis. This
module does not establish LSI on the interval, SU, their product, or U.
-/

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius NNReal

namespace LogSobolev

/-- Conditional assembly of Theorem 15: a proved LSI with constant `2/N` on
the exact interval × SU source would give constant `6/N` on U(N).
The source inequality is explicitly a hypothesis, not an available instance. -/
theorem unitary_metricLSI_of_phaseDomain (N : ℕ) (hN : 0 < N)
    (hsource : MetricLSI (phaseDomainMeasure N) ((2 : ℝ≥0) / (N : ℝ≥0))) :
    MetricLSI (unitaryHaar (Fin N)) ((6 : ℝ≥0) / (N : ℝ≥0)) := by
  have h := hsource.map (intervalPhaseMap_lipschitz N hN)
  rw [map_intervalPhaseMap N hN] at h
  let K : ℝ≥0 := ⟨Real.sqrt 3, Real.sqrt_nonneg 3⟩
  have hc : K ^ 2 * ((2 : ℝ≥0) / (N : ℝ≥0)) =
      (6 : ℝ≥0) / (N : ℝ≥0) := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div,
      NNReal.coe_ofNat, NNReal.coe_natCast]
    change Real.sqrt 3 ^ 2 * (2 / (N : ℝ)) = 6 / (N : ℝ)
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  change MetricLSI (unitaryHaar (Fin N)) (K ^ 2 * (2 / (N : ℝ≥0))) at h
  rwa [hc] at h

end LogSobolev
