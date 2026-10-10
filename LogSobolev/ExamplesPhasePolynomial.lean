module

public import LogSobolev

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Independent clients for the phase/SU regularization and joint derivative. -/
open Matrix MeasureTheory LogSobolev
open scoped Matrix.Norms.Frobenius NNReal

-- A nonsmooth distance observable admits the simultaneous derivative, in every degree.
example (d : ℕ) :
    ∃ (K : NNReal) (p : ℝ → specialUnitaryPolynomialSpace (n := Fin 2) d),
      (∀ t U, (p t).val U = ∫ V,
        dist (phaseMul (Real.sqrt (2 / (2 : ℝ))) t (specialUnitaryInclusion (U * V))) 1 *
          (specialUnitaryPowerKernel d).val V ∂specialUnitaryHaar (Fin 2)) ∧
      LipschitzWith K p ∧ (∀ᵐ t ∂volume, DifferentiableAt ℝ p t) :=
  unitary_exists_phase_polynomial_of_locallyLipschitz 2 (by decide) d
    (LipschitzWith.dist_left (1 : Matrix.unitaryGroup (Fin 2) ℂ)).locallyLipschitz

example (d : ℕ) {p : ℝ → specialUnitaryPolynomialSpace (n := Fin 2) d}
    {p' : specialUnitaryPolynomialSpace (n := Fin 2) d} {t : ℝ}
    (hp : HasDerivAt p p' t) (c : ℝ)
    (A : specialUnitaryLieAlgebra (n := Fin 2)) (U : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    HasDerivAt (fun s => (p (t + c * s)).val (U * specialUnitaryExpCurve A s))
      (c * p'.val U + specialUnitaryDeriv A (p t).val U) 0 :=
  specialUnitaryPolynomial_hasDerivAt_phase_flow d hp c A U

-- Exact dimension dependence of the central contribution, also in dimension one.
example (N : ℕ) (hN : 0 < N) (A : specialUnitaryLieAlgebra (n := Fin N)) (c : ℝ) :
    ‖A.val + (Complex.I * ((Real.sqrt (2 / (N : ℝ)) * c : ℝ) : ℂ)) •
      (1 : Matrix (Fin N) (Fin N) ℂ)‖ ^ 2 = ‖A.val‖ ^ 2 + 2 * c ^ 2 :=
  specialUnitary_phase_velocity_norm_sq N hN A c
