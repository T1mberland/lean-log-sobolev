module

public import LogSobolev.Unitary.SpecialUnitaryPowerKernel
public import LogSobolev.Measure.PowerKernelApproximation

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Uniform polynomial approximation by positive convolution on SU

The explicit normalized-power kernels produce polynomial approximants of degree
at most `j` for every continuous real observable. Convergence is in the actual
supremum norm, and squared entropy converges as well. Energy control for locally
Lipschitz observables is a separate obligation, not asserted here.
-/

open Matrix MeasureTheory Filter
open scoped Matrix.Norms.Frobenius Manifold ContDiff Topology

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Averaging by the explicit polynomial kernels converges uniformly to the
original continuous observable. The approximants retain their convolution formula. -/
theorem specialUnitaryPolynomial_exists_uniform_approximation
    (hN : 0 < Fintype.card n) (f : C(Matrix.specialUnitaryGroup n ℂ, ℝ)) :
    ∃ p : ∀ j, specialUnitaryPolynomialSpace (n := n) j,
      (∀ j U, (p j).val U =
        ∫ V, f (U * V) * (specialUnitaryPowerKernel j).val V ∂specialUnitaryHaar n) ∧
      Tendsto (fun j => specialUnitaryPolynomialToContinuous j (p j)) atTop (𝓝 f) := by
  classical
  choose p hp using fun j => specialUnitaryPolynomial_exists_averaging j
    (specialUnitaryPowerKernel (n := n) j) f
  refine ⟨p, hp, ?_⟩
  let H : Matrix.specialUnitaryGroup n ℂ → C(Matrix.specialUnitaryGroup n ℂ, ℝ) :=
    fun V => ⟨fun U => f (U * V), f.continuous.comp (continuous_id.mul continuous_const)⟩
  have hH : Continuous H := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact f.continuous.comp (continuous_snd.mul continuous_fst)
  have h1 : H 1 = f := by ext U; change f (U * 1) = f U; rw [mul_one]
  have ht := tendsto_integral_powerKernel_smul (specialUnitaryHaar n)
    specialUnitaryPeak.val.contMDiff.continuous specialUnitaryPeak_nonneg
    (specialUnitaryPeak_one hN) (specialUnitaryPeak_lt_one hN) (⟨H, hH⟩ : C(_, C(_, ℝ)))
  have he (j : ℕ) :
      (∫ V, powerKernel (specialUnitaryHaar n) specialUnitaryPeak.val j V • H V
        ∂specialUnitaryHaar n) = specialUnitaryPolynomialToContinuous j (p j) := by
    ext U
    rw [ContinuousMap.integral_apply (f := fun V =>
      powerKernel (specialUnitaryHaar n) specialUnitaryPeak.val j V • H V)
      (((continuous_powerKernel (specialUnitaryHaar n) specialUnitaryPeak.val.contMDiff.continuous j).smul hH).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    change (∫ V, powerKernel (specialUnitaryHaar n) specialUnitaryPeak.val j V * f (U * V)
      ∂specialUnitaryHaar n) = (p j).val U
    rw [hp]
    apply integral_congr_ae
    exact Eventually.of_forall fun V => by
      change powerKernel (specialUnitaryHaar n) specialUnitaryPeak.val j V * f (U * V) =
        f (U * V) * (specialUnitaryPowerKernel j).val V
      rw [specialUnitaryPowerKernel_apply, mul_comm]
  simpa only [he, h1, ContinuousMap.coe_mk] using ht

/-- The polynomial approximation also converges in squared entropy, including
for observables with zeros. This does not yet bound the approximants' energies. -/
theorem specialUnitaryPolynomial_exists_uniform_entropy_approximation
    (hN : 0 < Fintype.card n) (f : C(Matrix.specialUnitaryGroup n ℂ, ℝ)) :
    ∃ p : ∀ j, specialUnitaryPolynomialSpace (n := n) j,
      (∀ j U, (p j).val U =
        ∫ V, f (U * V) * (specialUnitaryPowerKernel j).val V ∂specialUnitaryHaar n) ∧
      Tendsto (fun j => specialUnitaryPolynomialToContinuous j (p j)) atTop (𝓝 f) ∧
      Tendsto (fun j => entropy (specialUnitaryHaar n) (fun U => (p j).val U ^ 2)) atTop
        (𝓝 (entropy (specialUnitaryHaar n) (fun U => f U ^ 2))) := by
  obtain ⟨p, hp, ht⟩ := specialUnitaryPolynomial_exists_uniform_approximation hN f
  refine ⟨p, hp, ht, ?_⟩
  exact tendsto_entropy_sq_of_tendsto_continuousMap (specialUnitaryHaar n)
    (f := fun j => specialUnitaryPolynomialToContinuous j (p j)) (g := f) ht

end LogSobolev
