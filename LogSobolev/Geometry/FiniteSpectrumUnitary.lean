module

public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected

@[expose] public section

/-! # Connectedness of unitaries with finite spectra

Mathlib constructs the selfadjoint argument by continuous functional calculus.
On a finite spectrum the scalar argument is continuous even when the spectrum
meets the branch cut. Thus every such unitary is an exponential. If every
unitary has finite spectrum, the unitary group is a continuous image of the
real vector space of selfadjoint elements, and is connected.
-/

open Complex NormedSpace selfAdjoint Unitary

namespace LogSobolev

variable {A : Type*} [CStarAlgebra A]

/-- The functional-calculus argument exponentiates to a unitary with finite spectrum. -/
theorem expUnitary_argSelfAdjoint_of_finite_spectrum (u : unitary A)
    (hu : (spectrum ℂ (u : A)).Finite) :
    expUnitary (argSelfAdjoint u) = u := by
  ext
  have : ContinuousOn arg (spectrum ℂ (u : A)) := hu.continuousOn _
  rw [expUnitary_coe, argSelfAdjoint_coe, ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ),
    ← cfc_comp_smul .., ← cfc_comp' ..]
  conv_rhs => rw [← cfc_id' ℂ (u : A)]
  refine cfc_congr fun y hy ↦ ?_
  have hy₁ : ‖y‖ = 1 := spectrum.norm_eq_one_of_unitary u.2 hy
  have he : I * y.arg = log y :=
    Complex.ext (by simp [log_re, hy₁]) (by simp [log_im])
  simpa [← exp_eq_exp_ℂ, he] using exp_log (by aesop)

/-- Finite spectra make the selfadjoint exponential surjective onto the unitary group. -/
theorem expUnitary_surjective_of_finite_spectrum
    (h : ∀ u : unitary A, (spectrum ℂ (u : A)).Finite) :
    Function.Surjective (expUnitary : selfAdjoint A → unitary A) := fun u =>
  ⟨argSelfAdjoint u, expUnitary_argSelfAdjoint_of_finite_spectrum u (h u)⟩

/-- The unitary group is connected if all its elements have finite spectrum. -/
theorem unitary_connectedSpace_of_finite_spectrum
    (h : ∀ u : unitary A, (spectrum ℂ (u : A)).Finite) : ConnectedSpace (unitary A) :=
  (expUnitary_surjective_of_finite_spectrum h).connectedSpace continuous_expUnitary

end LogSobolev
