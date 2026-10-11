module

public import LogSobolev.Concentration.Metric
public import LogSobolev.Unitary.UnitaryLSI
public import LogSobolev.Unitary.SpecialUnitaryLSI

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Haar concentration in the unnormalized Hilbert–Schmidt metric

Meckes–Meckes Theorem 15 and the verified Herbst argument give variance proxy
`6 K²/N` on U(N). The SU(N) proxy is `2 K²/N`. These are conclusions for the
actual normalized Haar measures and all globally Lipschitz real observables.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.Frobenius NNReal

namespace LogSobolev

/-- Centered MGF on U(N), including dimension one. -/
theorem unitary_hasSubgaussianMGF (N : ℕ) (hN : 0 < N) {K : ℝ≥0}
    {f : Matrix.unitaryGroup (Fin N) ℂ → ℝ} (hf : LipschitzWith K f) :
    HasSubgaussianMGF (fun U => f U - ∫ V, f V ∂unitaryHaar (Fin N))
      ((6 / (N : ℝ≥0)) * K ^ 2) (unitaryHaar (Fin N)) :=
  (unitary_metricLSI N hN).hasSubgaussianMGF_of_compact hf

/-- Upper Haar tail on U(N): `exp(-N r²/(12 K²))` when `K > 0`. The
unsimplified denominator also handles `K = 0` and `r = 0` without exclusions. -/
theorem unitary_measure_ge_le (N : ℕ) (hN : 0 < N) {K : ℝ≥0}
    {f : Matrix.unitaryGroup (Fin N) ℂ → ℝ} (hf : LipschitzWith K f)
    {r : ℝ} (hr : 0 ≤ r) :
    (unitaryHaar (Fin N)).real {U | r ≤ f U - ∫ V, f V ∂unitaryHaar (Fin N)} ≤
      Real.exp (-r ^ 2 / (2 * ((6 / (N : ℝ)) * (K : ℝ) ^ 2))) := by
  simpa using (unitary_hasSubgaussianMGF N hN hf).measure_ge_le hr

/-- Lower Haar tail on U(N). -/
theorem unitary_measure_le_le (N : ℕ) (hN : 0 < N) {K : ℝ≥0}
    {f : Matrix.unitaryGroup (Fin N) ℂ → ℝ} (hf : LipschitzWith K f)
    {r : ℝ} (hr : 0 ≤ r) :
    (unitaryHaar (Fin N)).real {U | r ≤ (∫ V, f V ∂unitaryHaar (Fin N)) - f U} ≤
      Real.exp (-r ^ 2 / (2 * ((6 / (N : ℝ)) * (K : ℝ) ^ 2))) := by
  simpa only [Pi.neg_apply, neg_sub, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_pow,
    NNReal.coe_ofNat, NNReal.coe_natCast] using
    (unitary_hasSubgaussianMGF N hN hf).neg.measure_ge_le hr

/-- Two-sided Haar concentration on U(N). -/
theorem unitary_measure_abs_ge_le (N : ℕ) (hN : 0 < N) {K : ℝ≥0}
    {f : Matrix.unitaryGroup (Fin N) ℂ → ℝ} (hf : LipschitzWith K f)
    {r : ℝ} (hr : 0 ≤ r) :
    (unitaryHaar (Fin N)).real {U | r ≤ |f U - ∫ V, f V ∂unitaryHaar (Fin N)|} ≤
      2 * Real.exp (-r ^ 2 / (2 * ((6 / (N : ℝ)) * (K : ℝ) ^ 2))) := by
  simpa using measure_abs_ge_le_of_hasSubgaussianMGF (unitary_hasSubgaussianMGF N hN hf) hr

/-- Centered MGF on SU(N), including the trivial group SU(1). -/
theorem specialUnitary_hasSubgaussianMGF (N : ℕ) (hN : 0 < N) {K : ℝ≥0}
    {f : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ} (hf : LipschitzWith K f) :
    HasSubgaussianMGF (fun U => f U - ∫ V, f V ∂specialUnitaryHaar (Fin N))
      ((2 / (N : ℝ≥0)) * K ^ 2) (specialUnitaryHaar (Fin N)) := by
  simpa using (specialUnitary_metricLSI (n := Fin N) (by simpa using hN)).hasSubgaussianMGF_of_compact hf

/-- Upper Haar concentration on SU(N). -/
theorem specialUnitary_measure_ge_le (N : ℕ) (hN : 0 < N) {K : ℝ≥0}
    {f : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ} (hf : LipschitzWith K f)
    {r : ℝ} (hr : 0 ≤ r) :
    (specialUnitaryHaar (Fin N)).real {U | r ≤ f U - ∫ V, f V ∂specialUnitaryHaar (Fin N)} ≤
      Real.exp (-r ^ 2 / (2 * ((2 / (N : ℝ)) * (K : ℝ) ^ 2))) := by
  simpa using (specialUnitary_hasSubgaussianMGF N hN hf).measure_ge_le hr

/-- Lower Haar concentration on SU(N). -/
theorem specialUnitary_measure_le_le (N : ℕ) (hN : 0 < N) {K : ℝ≥0}
    {f : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ} (hf : LipschitzWith K f)
    {r : ℝ} (hr : 0 ≤ r) :
    (specialUnitaryHaar (Fin N)).real {U | r ≤ (∫ V, f V ∂specialUnitaryHaar (Fin N)) - f U} ≤
      Real.exp (-r ^ 2 / (2 * ((2 / (N : ℝ)) * (K : ℝ) ^ 2))) := by
  simpa only [Pi.neg_apply, neg_sub, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_pow,
    NNReal.coe_ofNat, NNReal.coe_natCast] using
    (specialUnitary_hasSubgaussianMGF N hN hf).neg.measure_ge_le hr

/-- Two-sided Haar concentration on SU(N). -/
theorem specialUnitary_measure_abs_ge_le (N : ℕ) (hN : 0 < N) {K : ℝ≥0}
    {f : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ} (hf : LipschitzWith K f)
    {r : ℝ} (hr : 0 ≤ r) :
    (specialUnitaryHaar (Fin N)).real {U | r ≤ |f U - ∫ V, f V ∂specialUnitaryHaar (Fin N)|} ≤
      2 * Real.exp (-r ^ 2 / (2 * ((2 / (N : ℝ)) * (K : ℝ) ^ 2))) := by
  simpa using measure_abs_ge_le_of_hasSubgaussianMGF (specialUnitary_hasSubgaussianMGF N hN hf) hr

end LogSobolev
