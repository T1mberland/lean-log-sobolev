import LogSobolev.Unitary.SpecialUnitaryChainRules
import LogSobolev.Unitary.SpecialUnitaryIntegratedGammaTwo
import LogSobolev.Measure.EntropyDifferentiation

/-! # Entropy dissipation in the actual SU generator direction

For a positive differentiable family, if its time derivative at the specified
time equals the constructed SU Laplacian, entropy has derivative minus Fisher
information. Differentiation under Haar integration and the logarithmic energy
identity are proved. This theorem does not construct a heat trajectory or assume
entropy decay: its explicit hypotheses concern the family and its derivative.
-/

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

/-- Fisher-information density is integrable for every nowhere-zero smooth SU test. -/
theorem specialUnitary_integrable_fisher
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (h0 : ∀ U, f U ≠ 0) :
    Integrable (fun U => specialUnitaryGamma b f f U / f U) (specialUnitaryHaar n) :=
  specialUnitary_integrable_of_continuous
    ((specialUnitaryGamma_contMDiff b hf hf).continuous.div hf.continuous h0)

/-- Entropy dissipation is derived from the heat equation at a specified time.
The family is differentiated only on a neighborhood of that time, allowing
application at positive times without requiring a backwards heat solution. -/
theorem specialUnitary_hasDerivAt_entropy
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {F Q : ℝ → Matrix.specialUnitaryGroup n ℂ → ℝ} {s : Set ℝ}
    (hF : Continuous (Function.uncurry F))
    (hQ : Continuous (Function.uncurry Q))
    (hpos : ∀ t U, 0 < F t U)
    (hd : ∀ t ∈ s, ∀ U, HasDerivAt (fun r => F r U) (Q t U) t)
    (t : ℝ) (hs : s ∈ 𝓝 t)
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ (F t))
    (hheat : Q t = specialUnitaryLaplacian b (F t)) :
    HasDerivAt (fun r => entropy (specialUnitaryHaar n) (F r))
      (-(∫ U, specialUnitaryGamma b (F t) (F t) U / F t U ∂specialUnitaryHaar n)) t := by
  have hz : (∫ U, Q t U ∂specialUnitaryHaar n) = 0 := by
    rw [hheat]
    exact specialUnitary_integral_laplacian_eq_zero b hf
  have h := hasDerivAt_entropy_of_compact_of_integral_eq_zero hF hQ hpos hd t hs hz
  rw [hheat, specialUnitary_integral_log_mul_laplacian b hf (fun U => ne_of_gt (hpos t U))] at h
  exact h

/-- Entropy cannot increase instantaneously in the actual heat direction at a positive test. -/
theorem specialUnitary_entropy_deriv_nonpos
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {F Q : ℝ → Matrix.specialUnitaryGroup n ℂ → ℝ} {s : Set ℝ}
    (hF : Continuous (Function.uncurry F))
    (hQ : Continuous (Function.uncurry Q))
    (hpos : ∀ t U, 0 < F t U)
    (hd : ∀ t ∈ s, ∀ U, HasDerivAt (fun r => F r U) (Q t U) t)
    (t : ℝ) (hs : s ∈ 𝓝 t)
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ (F t))
    (hheat : Q t = specialUnitaryLaplacian b (F t)) :
    deriv (fun r => entropy (specialUnitaryHaar n) (F r)) t ≤ 0 := by
  rw [(specialUnitary_hasDerivAt_entropy b hF hQ hpos hd t hs hf hheat).deriv]
  exact neg_nonpos.mpr (integral_nonneg fun U =>
    div_nonneg (specialUnitaryGamma_nonneg b hf U) (hpos t U).le)

/-- The proved Γ₂ bound applied to `log f`, integrated against the positive weight `f`.
This is the curvature estimate needed for Fisher-information decay, not a
claim that a heat trajectory exists or satisfies a time-derivative formula. -/
theorem specialUnitary_weighted_gammaTwo_log_lower_bound
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hpos : ∀ U, 0 < f U) :
    (Fintype.card n : ℝ) / 2 *
        (∫ U, specialUnitaryGamma b f f U / f U ∂specialUnitaryHaar n) ≤
      ∫ U, f U * specialUnitaryGammaTwo b (Real.log ∘ f) U ∂specialUnitaryHaar n := by
  have h0 U := ne_of_gt (hpos U)
  have hlog := specialUnitary_log_contMDiff hf h0
  rw [← integral_const_mul]
  apply integral_mono ((specialUnitary_integrable_fisher b hf h0).const_mul _)
    (specialUnitary_integrable_of_continuous (hf.continuous.mul
      (specialUnitaryGammaTwo_contMDiff b hlog).continuous))
  intro U
  calc
    (Fintype.card n : ℝ) / 2 * (specialUnitaryGamma b f f U / f U) =
        f U * ((Fintype.card n : ℝ) / 2 *
          specialUnitaryGamma b (Real.log ∘ f) (Real.log ∘ f) U) := by
      rw [specialUnitaryGamma_log b hf h0]
      field_simp [h0 U]
    _ ≤ _ := mul_le_mul_of_nonneg_left (specialUnitaryGammaTwo_lower_bound b hlog U)
      (hpos U).le

end LogSobolev
