import LogSobolev.Unitary.SpecialUnitaryPolynomialConvolution
import Mathlib.Analysis.Calculus.Rademacher

/-! # Lipschitz families of polynomial averages

A nonnegative polynomial kernel of mass one contracts the uniform norm.
Consequently averaging a Lipschitz family produces a Lipschitz curve in a
single finite-dimensional polynomial space. Rademacher gives a simultaneous
almost-everywhere derivative in that space, not point-dependent exceptional sets.
-/

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius NNReal

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A normalized positive polynomial average contracts uniform distances. -/
theorem specialUnitaryPolynomial_averaging_dist_le (d : ℕ)
    (k : specialUnitaryPolynomialSpace (n := n) d)
    (hk : ∀ V, 0 ≤ k.val V) (hm : ∫ V, k.val V ∂specialUnitaryHaar n = 1)
    (f g : C(Matrix.specialUnitaryGroup n ℂ, ℝ))
    (p q : specialUnitaryPolynomialSpace (n := n) d)
    (hp : ∀ U, p.val U = ∫ V, f (U * V) * k.val V ∂specialUnitaryHaar n)
    (hq : ∀ U, q.val U = ∫ V, g (U * V) * k.val V ∂specialUnitaryHaar n) :
    dist p q ≤ dist f g := by
  rw [dist_eq_norm, dist_eq_norm]
  change ‖specialUnitaryPolynomialToContinuous d (p - q)‖ ≤ ‖f - g‖
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro U
  change ‖p.val U - q.val U‖ ≤ ‖f - g‖
  rw [hp, hq]
  have hi (a : C(Matrix.specialUnitaryGroup n ℂ, ℝ)) :
      Integrable (fun V => a (U * V) * k.val V) (specialUnitaryHaar n) :=
    ((a.continuous.comp (continuous_const.mul continuous_id)).mul
      k.val.contMDiff.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub (hi f) (hi g)]
  calc
    _ ≤ ∫ V, ‖f (U * V) * k.val V - g (U * V) * k.val V‖ ∂specialUnitaryHaar n :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ V, ‖f - g‖ * k.val V ∂specialUnitaryHaar n := by
      apply integral_mono ((hi f).sub (hi g)).norm
        ((continuous_const.mul k.val.contMDiff.continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
      intro V
      change ‖f (U * V) * k.val V - g (U * V) * k.val V‖ ≤ ‖f - g‖ * k.val V
      rw [← sub_mul, norm_mul, Real.norm_eq_abs (k.val V), abs_of_nonneg (hk V)]
      exact mul_le_mul_of_nonneg_right ((f - g).norm_coe_le_norm (U * V)) (hk V)
    _ = _ := by rw [integral_const_mul, hm, mul_one]

/-- A Lipschitz family admits polynomial averages with the same uniform Lipschitz constant. -/
theorem specialUnitaryPolynomial_exists_lipschitz_averaging (d : ℕ)
    (k : specialUnitaryPolynomialSpace (n := n) d)
    (hk : ∀ V, 0 ≤ k.val V) (hm : ∫ V, k.val V ∂specialUnitaryHaar n = 1)
    {K : NNReal} (f : ℝ → C(Matrix.specialUnitaryGroup n ℂ, ℝ)) (hf : LipschitzWith K f) :
    ∃ p : ℝ → specialUnitaryPolynomialSpace (n := n) d,
      (∀ t U, (p t).val U = ∫ V, f t (U * V) * k.val V ∂specialUnitaryHaar n) ∧
      LipschitzWith K p := by
  choose p hp using fun t => specialUnitaryPolynomial_exists_averaging d k (f t)
  refine ⟨p, hp, LipschitzWith.of_dist_le_mul fun s t => ?_⟩
  exact (specialUnitaryPolynomial_averaging_dist_le d k hk hm (f s) (f t)
    (p s) (p t) (hp s) (hp t)).trans (hf.dist_le_mul s t)

/-- The derivative of a Lipschitz polynomial curve exists almost everywhere simultaneously
in all evaluation coordinates, by finite-dimensional Rademacher. -/
theorem specialUnitaryPolynomialFamily_ae_differentiable (d : ℕ) {K : NNReal}
    {p : ℝ → specialUnitaryPolynomialSpace (n := n) d} (hp : LipschitzWith K p) :
    ∀ᵐ t ∂volume, DifferentiableAt ℝ p t :=
  hp.ae_differentiableAt

end LogSobolev
