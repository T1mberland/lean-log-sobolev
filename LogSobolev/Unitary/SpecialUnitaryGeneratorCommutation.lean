import LogSobolev.Geometry.CasimirCommutation
import LogSobolev.Unitary.SpecialUnitaryOperatorAlgebra

/-! # Commutation of the actual SU generator with invariant derivatives

The skew coefficient matrix comes from the verified ad-invariance of the real
Hilbert–Schmidt inner product. The representation consists of the actual
operators on smooth functions, so Casimir commutation is proved for the
constructed generator without a geometric or diffusion assumption.
-/

open Matrix
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

/-- The true invariant differential operators have a central sum of squares. -/
theorem specialUnitaryCasimir_commute
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    (A : specialUnitaryLieAlgebra (n := n)) :
    (∑ i, specialUnitaryDerivEnd (b i) * specialUnitaryDerivEnd (b i)) *
        specialUnitaryDerivEnd A =
      specialUnitaryDerivEnd A *
        (∑ i, specialUnitaryDerivEnd (b i) * specialUnitaryDerivEnd (b i)) := by
  let c : ι → ι → ℝ := fun i j => inner ℝ (b j) ⁅b i, A⁆
  apply sum_squares_commute_of_skew_coefficients _ _ c
  · intro i
    rw [specialUnitaryDerivEnd_commutator]
    have he : (∑ j, c i j • b j) = ⁅b i, A⁆ := by
      simpa only [OrthonormalBasis.repr_apply_apply] using b.sum_repr ⁅b i, A⁆
    have hd := congrArg (specialUnitaryDerivRepresentation (n := n)) he.symm
    simpa only [map_sum, map_smul] using hd
  · intro i j
    dsimp only [c]
    rw [← lie_skew (b j) A, inner_neg_right, ← lie_skew (b i) A, inner_neg_right, neg_neg]
    exact (specialUnitary_ad_skew A (b i) (b j)).symm.trans (real_inner_comm _ _)

/-- The sum-of-squares operator commutes with every invariant derivative on smooth tests. -/
theorem specialUnitaryLaplacian_deriv
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    (A : specialUnitaryLieAlgebra (n := n))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f) :
    specialUnitaryLaplacian b (specialUnitaryDeriv A f) =
      specialUnitaryDeriv A (specialUnitaryLaplacian b f) := by
  let F : specialUnitarySmoothFunctions n := ⟨f, hf⟩
  have h := congrArg (fun g : specialUnitarySmoothFunctions n =>
    (g : Matrix.specialUnitaryGroup n ℂ → ℝ))
    (DFunLike.congr_fun (specialUnitaryCasimir_commute b A) F)
  have hs (g : specialUnitarySmoothFunctions n) :
      ⇑((∑ i, specialUnitaryDerivEnd (b i) * specialUnitaryDerivEnd (b i)) g) =
        specialUnitaryLaplacian b g := by
    funext U
    rw [LinearMap.sum_apply]
    change (ContMDiffMap.evalRingHom U : specialUnitarySmoothFunctions n →+* ℝ)
      (∑ i, (specialUnitaryDerivEnd (b i) * specialUnitaryDerivEnd (b i)) g) = _
    rw [map_sum]
    rfl
  change ⇑((∑ i, specialUnitaryDerivEnd (b i) * specialUnitaryDerivEnd (b i))
      (specialUnitaryDerivEnd A F)) =
    ⇑(specialUnitaryDerivEnd A ((∑ i, specialUnitaryDerivEnd (b i) *
      specialUnitaryDerivEnd (b i)) F)) at h
  rw [hs] at h
  change specialUnitaryLaplacian b (specialUnitaryDeriv A f) =
    specialUnitaryDeriv A ⇑((∑ i, specialUnitaryDerivEnd (b i) *
      specialUnitaryDerivEnd (b i)) F) at h
  rwa [hs] at h

end LogSobolev
