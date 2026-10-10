module

public import LogSobolev.Unitary.SpecialUnitaryDifferentialOperators

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Invariant differentiation along actual exponential curves

For a smooth SU test, differentiation along `U exp(tA)` is its actual invariant
manifold derivative. The proof uses the verified local ambient extension and
matrix-exponential derivative, with no assumption about a flow or generator.
-/

open Matrix Filter Topology
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative along right multiplication by the exponential curve equals invariant differentiation. -/
theorem specialUnitary_hasDerivAt_mul_exp
    (A : specialUnitaryLieAlgebra (n := n)) (U : Matrix.specialUnitaryGroup n ℂ)
    {f : Matrix.specialUnitaryGroup n ℂ → F}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ, F) ∞ f) (t : ℝ) :
    HasDerivAt (fun s => f (U * specialUnitaryExpCurve A s))
      (specialUnitaryDeriv A f (U * specialUnitaryExpCurve A t)) t := by
  let W := U * specialUnitaryExpCurve A t
  obtain ⟨g, hg, hfg⟩ := specialUnitary_exists_local_smooth_extension (hf (x := W))
  have hc : ContinuousAt (fun s => U * specialUnitaryExpCurve A s) t :=
    continuousAt_const.mul (specialUnitaryExpCurve_lipschitz A).continuous.continuousAt
  have he : (fun s => f (U * specialUnitaryExpCurve A s)) =ᶠ[𝓝 t]
      (fun s => g (U * specialUnitaryExpCurve A s).val) := hfg.comp_tendsto hc
  have hD : specialUnitaryDeriv A f W = rightMulDeriv A.val g W.val :=
    (specialUnitaryDeriv_congr A hfg).trans
      (specialUnitaryDeriv_of_ambient A W (hg.differentiableAt (by decide)))
  have hd : HasDerivAt (fun s => g (U * specialUnitaryExpCurve A s).val)
      (specialUnitaryDeriv A f W) t := by
    rw [hD]
    simpa only [rightMulDeriv, W, Function.comp_def, Submonoid.coe_mul, ← mul_assoc] using
      (hg.differentiableAt (by decide)).hasFDerivAt.comp_hasDerivAt t
        ((specialUnitaryExpCurve_hasDerivAt A t).const_mul U.val)
  exact hd.congr_of_eventuallyEq he

end LogSobolev
