import LogSobolev.Unitary.SpecialUnitaryPolynomialPullback
import LogSobolev.Unitary.SpecialUnitaryPolynomialNorm
import LogSobolev.Unitary.SpecialUnitaryHaarCalculus
import LogSobolev.Measure.EntropyContinuity
import Mathlib.MeasureTheory.Integral.Prod

/-! # Polynomial convolution on SU

Convolving a continuous observable with a polynomial kernel gives an actual
polynomial of the same degree. The proof integrates continuous functions in
the closed, finite-dimensional polynomial subspace. This is an algebraic
regularization result; it does not yet assert approximation or energy control.
-/

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Convolution against a polynomial kernel lies in the same polynomial space.
The formula uses normalized Haar probability on the actual SU group. -/
theorem specialUnitaryPolynomial_exists_convolution (d : ℕ)
    (k : specialUnitaryPolynomialSpace (n := n) d)
    (f : C(Matrix.specialUnitaryGroup n ℂ, ℝ)) :
    ∃ p : specialUnitaryPolynomialSpace (n := n) d,
      ∀ U, p.val U = ∫ V, f V * k.val (U⁻¹ * V) ∂specialUnitaryHaar n := by
  let K : Matrix.specialUnitaryGroup n ℂ → C(Matrix.specialUnitaryGroup n ℂ, ℝ) :=
    fun V => ⟨fun U => f V * k.val (U⁻¹ * V),
      continuous_const.mul (k.val.contMDiff.continuous.comp
        (continuous_inv.mul continuous_const))⟩
  have hK : Continuous K := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (f.continuous.comp continuous_fst).mul
      (k.val.contMDiff.continuous.comp (continuous_snd.inv.mul continuous_fst))
  have hi : Integrable K (specialUnitaryHaar n) :=
    hK.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let S := (specialUnitaryPolynomialToContinuous (n := n) d).range
  have hmem : ∀ V, K V ∈ S := by
    intro V
    obtain ⟨p, hp⟩ := specialUnitaryPolynomial_exists_inv_mul V d k
    refine ⟨f V • p, ?_⟩
    ext U
    change f V * p.val U = f V * k.val (U⁻¹ * V)
    rw [hp]
  have hclosed : IsClosed (S : Set C(Matrix.specialUnitaryGroup n ℂ, ℝ)) := by
    haveI := (specialUnitaryPolynomialToContinuous (n := n) d).finiteDimensional_range
    exact S.closed_of_finiteDimensional
  obtain ⟨p, hp⟩ := S.convex.integral_mem hclosed
    (Filter.Eventually.of_forall hmem) hi
  refine ⟨p, fun U => ?_⟩
  have he := DFunLike.congr_fun hp U
  exact he.trans (ContinuousMap.integral_apply hi U)

/-- The equivalent averaging formula, obtained from verified Haar invariance. -/
theorem specialUnitaryPolynomial_exists_averaging (d : ℕ)
    (k : specialUnitaryPolynomialSpace (n := n) d)
    (f : C(Matrix.specialUnitaryGroup n ℂ, ℝ)) :
    ∃ p : specialUnitaryPolynomialSpace (n := n) d,
      ∀ U, p.val U = ∫ V, f (U * V) * k.val V ∂specialUnitaryHaar n := by
  obtain ⟨p, hp⟩ := specialUnitaryPolynomial_exists_convolution d k f
  refine ⟨p, fun U => ?_⟩
  rw [hp]
  have h := integral_mul_left_eq_self (μ := specialUnitaryHaar n)
    (fun V => f V * k.val (U⁻¹ * V)) U
  simpa only [inv_mul_cancel_left] using h.symm

/-- Averaging against a kernel of mass one preserves the Haar mean. -/
theorem specialUnitary_averaging_integral
    (k f : C(Matrix.specialUnitaryGroup n ℂ, ℝ))
    (hk : ∫ V, k V ∂specialUnitaryHaar n = 1) :
    (∫ U, (∫ V, f (U * V) * k V ∂specialUnitaryHaar n) ∂specialUnitaryHaar n) =
      ∫ U, f U ∂specialUnitaryHaar n := by
  have hc : Continuous (fun p : Matrix.specialUnitaryGroup n ℂ ×
      Matrix.specialUnitaryGroup n ℂ => f (p.1 * p.2) * k p.2) :=
    (f.continuous.comp (continuous_fst.mul continuous_snd)).mul
      (k.continuous.comp continuous_snd)
  rw [integral_integral_swap
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  simp_rw [integral_mul_const]
  simp_rw [integral_mul_right_eq_self (μ := specialUnitaryHaar n) (fun U => f U)]
  rw [integral_const_mul, hk, mul_one]

/-- Nonnegative kernels of mass one preserve pointwise upper bounds. -/
theorem specialUnitary_averaging_le
    (k f : C(Matrix.specialUnitaryGroup n ℂ, ℝ))
    (hk : ∀ V, 0 ≤ k V) (hm : ∫ V, k V ∂specialUnitaryHaar n = 1)
    (M : ℝ) (hf : ∀ U, f U ≤ M) (U : Matrix.specialUnitaryGroup n ℂ) :
    (∫ V, f (U * V) * k V ∂specialUnitaryHaar n) ≤ M := by
  have hi : Integrable (fun V => f (U * V) * k V) (specialUnitaryHaar n) :=
    ((f.continuous.comp (continuous_const.mul continuous_id)).mul k.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun V => M * k V) (specialUnitaryHaar n) :=
    (continuous_const.mul k.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ V, M * k V ∂specialUnitaryHaar n :=
      integral_mono hi hj (fun V => mul_le_mul_of_nonneg_right (hf _) (hk V))
    _ = M := by rw [integral_const_mul, hm, mul_one]

end LogSobolev
