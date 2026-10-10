import LogSobolev.Unitary.SpecialUnitaryFisherIdentity

/-! # Differentiation of SU Fisher information for regular families

For a supplied smooth spatial family, joint continuity and explicit time
derivatives of the invariant first derivatives imply the Fisher derivative
formula. These regularity assumptions are stated individually; no heat solution,
Fisher decay, or entropy inequality is assumed. Establishing this regularity
for a constructed heat family remains part of the heat-construction obligation.
-/

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

/-- Differentiate the actual Fisher integral. Time differentiation of the
invariant derivatives is an explicit regularity hypothesis, not an assumed
formula for Fisher information. -/
theorem specialUnitary_hasDerivAt_fisher
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {F Q : ℝ → Matrix.specialUnitaryGroup n ℂ → ℝ} {s : Set ℝ}
    (hF : Continuous (Function.uncurry F))
    (hQ : Continuous (Function.uncurry Q))
    (h0 : ∀ t U, F t U ≠ 0)
    (hf : ∀ t, ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ (F t))
    (hq : ∀ t, ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ (Q t))
    (hDF : ∀ i, Continuous (fun p : ℝ × Matrix.specialUnitaryGroup n ℂ =>
      specialUnitaryDeriv (b i) (F p.1) p.2))
    (hDQ : ∀ i, Continuous (fun p : ℝ × Matrix.specialUnitaryGroup n ℂ =>
      specialUnitaryDeriv (b i) (Q p.1) p.2))
    (hd : ∀ t ∈ s, ∀ U, HasDerivAt (fun r => F r U) (Q t U) t)
    (hdD : ∀ i t, t ∈ s → ∀ U,
      HasDerivAt (fun r => specialUnitaryDeriv (b i) (F r) U)
        (specialUnitaryDeriv (b i) (Q t) U) t)
    (t : ℝ) (hs : s ∈ 𝓝 t) :
    HasDerivAt
      (fun r => ∫ U, specialUnitaryGamma b (F r) (F r) U / F r U ∂specialUnitaryHaar n)
      (∫ U, 2 * specialUnitaryGamma b (F t) (Q t) U / F t U -
        specialUnitaryGamma b (F t) (F t) U * Q t U / (F t U) ^ 2 ∂specialUnitaryHaar n) t := by
  have hG : Continuous (fun p : ℝ × Matrix.specialUnitaryGroup n ℂ =>
      specialUnitaryGamma b (F p.1) (F p.1) p.2) := by
    simp_rw [specialUnitaryGamma_eq b (hf _) (hf _)]
    exact continuous_finset_sum _ (fun i _ => (hDF i).mul (hDF i))
  have hGQ : Continuous (fun p : ℝ × Matrix.specialUnitaryGroup n ℂ =>
      specialUnitaryGamma b (F p.1) (Q p.1) p.2) := by
    simp_rw [specialUnitaryGamma_eq b (hf _) (hq _)]
    exact continuous_finset_sum _ (fun i _ => (hDF i).mul (hDQ i))
  have hGD (r : ℝ) (hr : r ∈ s) (U : Matrix.specialUnitaryGroup n ℂ) :
      HasDerivAt (fun v => specialUnitaryGamma b (F v) (F v) U)
        (2 * specialUnitaryGamma b (F r) (Q r) U) r := by
    simp_rw [specialUnitaryGamma_eq b (hf _) (hf _), specialUnitaryGamma_eq b (hf _) (hq _)]
    convert HasDerivAt.sum (u := Finset.univ)
      (fun i _ => (hdD i r hr U).mul (hdD i r hr U)) using 1
    · funext v
      simp only [Finset.sum_apply, Pi.mul_apply]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
  apply hasDerivAt_integral_of_compact (s := s)
    (F := fun r U => specialUnitaryGamma b (F r) (F r) U / F r U)
    (Q := fun r U => 2 * specialUnitaryGamma b (F r) (Q r) U / F r U -
      specialUnitaryGamma b (F r) (F r) U * Q r U / (F r U) ^ 2)
    (hG.div hF (fun p => h0 p.1 p.2))
    ((((continuous_const (y := (2 : ℝ))).mul hGQ).div hF (fun p => h0 p.1 p.2)).sub
      ((hG.mul hQ).div (hF.pow 2) (fun p => pow_ne_zero 2 (h0 p.1 p.2))))
    ?_ t hs
  intro r hr U
  convert (hGD r hr U).div (hd r hr U) (h0 r U) using 1
  field_simp [h0 r U]

/-- Fisher dissipation in the actual heat direction, under the explicitly stated
regularity and mixed-derivative hypotheses of `specialUnitary_hasDerivAt_fisher`. -/
theorem specialUnitary_hasDerivAt_fisher_of_heat
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {F Q : ℝ → Matrix.specialUnitaryGroup n ℂ → ℝ} {s : Set ℝ}
    (hF : Continuous (Function.uncurry F))
    (hQ : Continuous (Function.uncurry Q))
    (h0 : ∀ t U, F t U ≠ 0)
    (hf : ∀ t, ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ (F t))
    (hq : ∀ t, ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ (Q t))
    (hDF : ∀ i, Continuous (fun p : ℝ × Matrix.specialUnitaryGroup n ℂ =>
      specialUnitaryDeriv (b i) (F p.1) p.2))
    (hDQ : ∀ i, Continuous (fun p : ℝ × Matrix.specialUnitaryGroup n ℂ =>
      specialUnitaryDeriv (b i) (Q p.1) p.2))
    (hd : ∀ t ∈ s, ∀ U, HasDerivAt (fun r => F r U) (Q t U) t)
    (hdD : ∀ i t, t ∈ s → ∀ U,
      HasDerivAt (fun r => specialUnitaryDeriv (b i) (F r) U)
        (specialUnitaryDeriv (b i) (Q t) U) t)
    (t : ℝ) (hs : s ∈ 𝓝 t)
    (hheat : Q t = specialUnitaryLaplacian b (F t)) :
    HasDerivAt
      (fun r => ∫ U, specialUnitaryGamma b (F r) (F r) U / F r U ∂specialUnitaryHaar n)
      (-2 * (∫ U, F t U * specialUnitaryGammaTwo b (Real.log ∘ F t) U
        ∂specialUnitaryHaar n)) t := by
  have h := specialUnitary_hasDerivAt_fisher b hF hQ h0 hf hq hDF hDQ hd hdD t hs
  rw [hheat, specialUnitary_fisher_variation_identity b (hf t) (h0 t)] at h
  exact h

/-- The Fisher differential inequality has coefficient `N` for a real HS orthonormal basis.
Heat existence and the mixed time/spatial regularity are not concluded by this theorem. -/
theorem specialUnitary_fisher_deriv_le
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {F Q : ℝ → Matrix.specialUnitaryGroup n ℂ → ℝ} {s : Set ℝ}
    (hF : Continuous (Function.uncurry F))
    (hQ : Continuous (Function.uncurry Q))
    (hpos : ∀ t U, 0 < F t U)
    (hf : ∀ t, ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ (F t))
    (hq : ∀ t, ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ (Q t))
    (hDF : ∀ i, Continuous (fun p : ℝ × Matrix.specialUnitaryGroup n ℂ =>
      specialUnitaryDeriv (b i) (F p.1) p.2))
    (hDQ : ∀ i, Continuous (fun p : ℝ × Matrix.specialUnitaryGroup n ℂ =>
      specialUnitaryDeriv (b i) (Q p.1) p.2))
    (hd : ∀ t ∈ s, ∀ U, HasDerivAt (fun r => F r U) (Q t U) t)
    (hdD : ∀ i t, t ∈ s → ∀ U,
      HasDerivAt (fun r => specialUnitaryDeriv (b i) (F r) U)
        (specialUnitaryDeriv (b i) (Q t) U) t)
    (t : ℝ) (hs : s ∈ 𝓝 t)
    (hheat : Q t = specialUnitaryLaplacian b (F t)) :
    deriv (fun r => ∫ U, specialUnitaryGamma b (F r) (F r) U / F r U
      ∂specialUnitaryHaar n) t ≤
      -(Fintype.card n : ℝ) *
        (∫ U, specialUnitaryGamma b (F t) (F t) U / F t U ∂specialUnitaryHaar n) := by
  rw [(specialUnitary_hasDerivAt_fisher b hF hQ (fun r U => ne_of_gt (hpos r U))
    hf hq hDF hDQ hd hdD t hs).deriv, hheat]
  exact specialUnitary_fisher_variation_le b (hf t) (hpos t)

end LogSobolev
