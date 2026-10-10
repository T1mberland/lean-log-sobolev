module

public import LogSobolev.Unitary.SpecialUnitaryPolynomialSpace
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Global smooth ambient extensions of SU polynomial observables

Induction on powers of the affine-observable space constructs a globally smooth
real function on the ambient complex matrices extending each polynomial SU
observable. Restriction along the isometric inclusion then proves local Lipschitz
regularity for the actual unnormalized Hilbert–Schmidt metric.
-/

open Matrix
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every polynomial SU observable extends to a globally smooth ambient real function. -/
theorem specialUnitaryPolynomial_exists_contDiff_extension (d : ℕ)
    {f : specialUnitarySmoothFunctions n} (hf : f ∈ specialUnitaryPolynomialSpace d) :
    ∃ g : Matrix n n ℂ → ℝ, ContDiff ℝ ∞ g ∧
      ∀ U : Matrix.specialUnitaryGroup n ℂ, g U.val = f U := by
  induction d generalizing f with
  | zero =>
      change f ∈ specialUnitaryAffineSpace ^ 0 at hf
      rw [pow_zero (specialUnitaryAffineSpace (n := n))] at hf
      obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hf
      refine ⟨fun _ => r, contDiff_const, fun U => ?_⟩
      rw [Algebra.algebraMap_eq_smul_one]
      change r = r * 1
      exact (mul_one r).symm
  | succ d ih =>
      change f ∈ specialUnitaryAffineSpace ^ (d + 1) at hf
      rw [pow_succ (specialUnitaryAffineSpace (n := n)) d] at hf
      refine Submodule.mul_induction_on hf ?_ ?_
      · intro a ha b hb
        obtain ⟨g, hg, he⟩ := ih ha
        obtain ⟨⟨c, l⟩, rfl⟩ := hb
        refine ⟨fun M => g M * (c + l M), hg.mul (contDiff_const.add l.contDiff), ?_⟩
        intro U
        change g U.val * (c + l U.val) = a U * (c + l U.val)
        rw [he]
      · intro a b ha hb
        obtain ⟨ga, hga, hea⟩ := ha
        obtain ⟨gb, hgb, heb⟩ := hb
        refine ⟨fun M => ga M + gb M, hga.add hgb, ?_⟩
        intro U
        change ga U.val + gb U.val = a U + b U
        rw [hea, heb]

/-- Polynomial observables are locally Lipschitz for the actual HS subspace metric. -/
theorem specialUnitaryPolynomial_locallyLipschitz (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) : LocallyLipschitz (f.val : Matrix.specialUnitaryGroup n ℂ → ℝ) := by
  obtain ⟨g, hg, he⟩ := specialUnitaryPolynomial_exists_contDiff_extension d f.prop
  have h : (f.val : Matrix.specialUnitaryGroup n ℂ → ℝ) = fun U => g U.val :=
    funext fun U => (he U).symm
  rw [h]
  exact (hg.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)).locallyLipschitz.comp
    isometry_subtype_coe.lipschitz.locallyLipschitz

end LogSobolev
