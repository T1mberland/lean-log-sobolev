import LogSobolev.Geometry.AlgebraVectorFields
import LogSobolev.Unitary.SpecialUnitaryInvariantFields
import LogSobolev.Unitary.SpecialUnitarySmoothExtension

/-! # Actual directional derivatives on SU

Directional derivatives are defined using `mfderiv` on the verified SU manifold.
Their commutator is the directional derivative along the matrix commutator
for every smooth SU test, via the proved local ambient extension. No curvature
criterion or LSI is assumed or asserted.
-/

open Matrix Filter Topology
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Derivative along the actual left-invariant SU field with identity coordinate `A`. -/
noncomputable def specialUnitaryDeriv (A : specialUnitaryLieAlgebra (n := n))
    (f : Matrix.specialUnitaryGroup n ℂ → F) (U : Matrix.specialUnitaryGroup n ℂ) : F :=
  mfderiv 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ, F) f U A

/-- Restricting an ambient differentiable function gives the expected directional derivative. -/
theorem specialUnitaryDeriv_of_ambient (A : specialUnitaryLieAlgebra (n := n))
    (U : Matrix.specialUnitaryGroup n ℂ) {f : Matrix n n ℂ → F}
    (hf : DifferentiableAt ℝ f U.val) :
    specialUnitaryDeriv A (fun V => f V.val) U = rightMulDeriv A.val f U.val := by
  have h := hf.hasFDerivAt.hasMFDerivAt.comp U (specialUnitary_val_hasMFDerivAt U)
  exact DFunLike.congr_fun h.mfderiv A

/-- Directional derivatives depend only on the germ of the function. -/
theorem specialUnitaryDeriv_congr (A : specialUnitaryLieAlgebra (n := n))
    {f g : Matrix.specialUnitaryGroup n ℂ → F} {U : Matrix.specialUnitaryGroup n ℂ}
    (h : f =ᶠ[𝓝 U] g) : specialUnitaryDeriv A f U = specialUnitaryDeriv A g U :=
  DFunLike.congr_fun (h.mfderiv_eq (I := 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)))
    (I' := 𝓘(ℝ, F))) A

/-- Equality on a neighborhood implies equality of directional derivatives on a neighborhood. -/
theorem specialUnitaryDeriv_eventuallyEq (A : specialUnitaryLieAlgebra (n := n))
    {f g : Matrix.specialUnitaryGroup n ℂ → F} {U : Matrix.specialUnitaryGroup n ℂ}
    (h : f =ᶠ[𝓝 U] g) : specialUnitaryDeriv A f =ᶠ[𝓝 U] specialUnitaryDeriv A g := by
  filter_upwards [h.eventuallyEq_nhds] with V hV
  exact specialUnitaryDeriv_congr A hV

/-- Ambient comparison holds on a neighborhood whenever the ambient test is locally `C¹`. -/
theorem specialUnitaryDeriv_of_ambient_eventually (A : specialUnitaryLieAlgebra (n := n))
    (U : Matrix.specialUnitaryGroup n ℂ) {f : Matrix n n ℂ → F}
    (hf : ContDiffAt ℝ 1 f U.val) :
    specialUnitaryDeriv A (fun V => f V.val) =ᶠ[𝓝 U]
      (fun V => rightMulDeriv A.val f V.val) := by
  have hh := continuous_subtype_val.continuousAt.tendsto.eventually
    (hf.eventually (by norm_num))
  filter_upwards [hh] with V hV
  exact specialUnitaryDeriv_of_ambient A V (hV.differentiableAt (by norm_num))

/-- Invariant differentiation preserves smoothness on the actual SU manifold. -/
theorem specialUnitaryDeriv_contMDiffAt (A : specialUnitaryLieAlgebra (n := n))
    {f : Matrix.specialUnitaryGroup n ℂ → F} {U : Matrix.specialUnitaryGroup n ℂ}
    (hf : ContMDiffAt 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ, F) ∞ f U) :
    ContMDiffAt 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ, F) ∞
      (specialUnitaryDeriv A f) U := by
  obtain ⟨g, hg, hfg⟩ := specialUnitary_exists_local_smooth_extension hf
  have hd : ContDiffAt ℝ ∞ (rightMulDeriv A.val g) U.val :=
    (hg.fderiv_right (by decide)).clm_apply (contDiffAt_id.mul contDiffAt_const)
  have h := hd.contMDiffAt.comp U specialUnitary_val_contMDiff.contMDiffAt
  apply h.congr_of_eventuallyEq
  exact (specialUnitaryDeriv_eventuallyEq A hfg).trans
    (specialUnitaryDeriv_of_ambient_eventually A U (hg.of_le (by decide)))

/-- Global smoothness is preserved by invariant differentiation. -/
theorem specialUnitaryDeriv_contMDiff (A : specialUnitaryLieAlgebra (n := n))
    {f : Matrix.specialUnitaryGroup n ℂ → F}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ, F) ∞ f) :
    ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ, F) ∞ (specialUnitaryDeriv A f) :=
  fun _ => specialUnitaryDeriv_contMDiffAt A hf.contMDiffAt

/-- Local ambient `C²` regularity suffices for the actual SU operator commutator. -/
theorem specialUnitaryDeriv_commutator_of_ambientAt (A B : specialUnitaryLieAlgebra (n := n))
    (U : Matrix.specialUnitaryGroup n ℂ) {f : Matrix n n ℂ → F}
    (hf : ContDiffAt ℝ 2 f U.val) :
    specialUnitaryDeriv A (specialUnitaryDeriv B (fun V => f V.val)) U -
      specialUnitaryDeriv B (specialUnitaryDeriv A (fun V => f V.val)) U =
      specialUnitaryDeriv ⁅A, B⁆ (fun V => f V.val) U := by
  have hfun (C : specialUnitaryLieAlgebra (n := n)) :
      specialUnitaryDeriv C (fun V => f V.val) =ᶠ[𝓝 U]
        (fun V => rightMulDeriv C.val f V.val) :=
    specialUnitaryDeriv_of_ambient_eventually C U (hf.of_le (by decide))
  have hD (C : specialUnitaryLieAlgebra (n := n)) :
      DifferentiableAt ℝ (rightMulDeriv C.val f) U.val := by
    have hd : ContDiffAt ℝ 1 (rightMulDeriv C.val f) U.val :=
      (hf.fderiv_right (by norm_num)).clm_apply (contDiffAt_id.mul contDiffAt_const)
    exact hd.differentiableAt (by norm_num)
  rw [specialUnitaryDeriv_congr A (hfun B), specialUnitaryDeriv_congr B (hfun A),
    specialUnitaryDeriv_of_ambient A U (hD B), specialUnitaryDeriv_of_ambient B U (hD A),
    specialUnitaryDeriv_of_ambient ⁅A, B⁆ U (hf.differentiableAt (by norm_num))]
  exact rightMulDeriv_commutator A.val B.val U.val hf

/-- The actual SU directional operators have the matrix-commutator relation for every smooth test.
A proved local extension supplies the ambient calculation; no extension hypothesis is assumed. -/
theorem specialUnitaryDeriv_commutator (A B : specialUnitaryLieAlgebra (n := n))
    {f : Matrix.specialUnitaryGroup n ℂ → F} {U : Matrix.specialUnitaryGroup n ℂ}
    (hf : ContMDiffAt 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ, F) ∞ f U) :
    specialUnitaryDeriv A (specialUnitaryDeriv B f) U -
      specialUnitaryDeriv B (specialUnitaryDeriv A f) U =
      specialUnitaryDeriv ⁅A, B⁆ f U := by
  obtain ⟨g, hg, hfg⟩ := specialUnitary_exists_local_smooth_extension hf
  rw [specialUnitaryDeriv_congr A (specialUnitaryDeriv_eventuallyEq B hfg),
    specialUnitaryDeriv_congr B (specialUnitaryDeriv_eventuallyEq A hfg),
    specialUnitaryDeriv_congr ⁅A, B⁆ hfg]
  exact specialUnitaryDeriv_commutator_of_ambientAt A B U (hg.of_le (by decide))

end LogSobolev
