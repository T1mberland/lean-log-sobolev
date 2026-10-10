module

public import LogSobolev.Unitary.CentralOrthogonality
public import LogSobolev.Unitary.PhaseSlices
public import LogSobolev.Unitary.SpecialUnitaryCurves
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Exact speed of the combined phase and SU flow

The central phase direction is orthogonal to traceless SU directions for the
unnormalized HS metric. Consequently the combined curve has squared speed
`‖A‖² + 2 c²`, with no triangle-inequality loss.
-/

open Matrix
open scoped Matrix.Norms.Frobenius NNReal

namespace LogSobolev

/-- Scalar phase multiplication commutes with right matrix multiplication. -/
theorem phaseMul_mul {n : Type*} [Fintype n] [DecidableEq n] (a t : ℝ)
    (U V : Matrix.unitaryGroup n ℂ) :
    phaseMul a t (U * V) = phaseMul a t U * V := by
  apply Subtype.ext
  exact (Matrix.smul_mul (phase (a * t) : ℂ) U.val V.val).symm

/-- Simultaneous phase translation and right SU exponential flow. -/
noncomputable def unitaryPhaseFlow (N : ℕ) (t c : ℝ)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : specialUnitaryLieAlgebra (n := Fin N)) (s : ℝ) :
    Matrix.unitaryGroup (Fin N) ℂ :=
  phaseMul (Real.sqrt (2 / (N : ℝ))) (t + c * s)
    (specialUnitaryInclusion (U * specialUnitaryExpCurve A s))

@[simp] theorem unitaryPhaseFlow_zero (N : ℕ) (t c : ℝ)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : specialUnitaryLieAlgebra (n := Fin N)) :
    unitaryPhaseFlow N t c U A 0 =
      phaseMul (Real.sqrt (2 / (N : ℝ))) t (specialUnitaryInclusion U) := by
  simp [unitaryPhaseFlow]

/-- The derivative is left translation of the sum of the two generators. -/
theorem unitaryPhaseFlow_hasDerivAt (N : ℕ) (t c : ℝ)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : specialUnitaryLieAlgebra (n := Fin N)) (s : ℝ) :
    HasDerivAt (fun r => (unitaryPhaseFlow N t c U A r).val)
      ((unitaryPhaseFlow N t c U A s).val *
        (A.val + (Complex.I * ((Real.sqrt (2 / (N : ℝ)) * c : ℝ) : ℂ)) • 1)) s := by
  let a := Real.sqrt (2 / (N : ℝ))
  have hr : HasDerivAt (fun r : ℝ => a * (t + c * r)) (a * c) s := by
    simpa only [Pi.add_apply, zero_add, mul_one, id_eq] using
      ((hasDerivAt_const s t).add ((hasDerivAt_id s).const_mul c)).const_mul a
  have hz := (hr.ofReal_comp.const_mul Complex.I).cexp
  have hU := (specialUnitaryExpCurve_hasDerivAt A s).const_mul U.val
  have hd := hz.smul hU
  convert hd using 1 <;> try rfl
  change ((phase (a * (t + c * s)) : ℂ) • (U.val * (specialUnitaryExpCurve A s).val)) *
        (A.val + (Complex.I * ((a * c : ℝ) : ℂ)) • 1) = _
  simp only [Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, mul_one, smul_smul,
      phase, mul_assoc]
  congr 2
  ring

/-- The squared speed is exactly the sum of orthogonal squared speeds. -/
theorem unitaryPhaseFlow_speed_sq (N : ℕ) (hN : 0 < N) (t c : ℝ)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : specialUnitaryLieAlgebra (n := Fin N)) (s : ℝ) :
    ‖deriv (fun r => (unitaryPhaseFlow N t c U A r).val) s‖ ^ 2 = ‖A.val‖ ^ 2 + 2 * c ^ 2 := by
  rw [(unitaryPhaseFlow_hasDerivAt N t c U A s).deriv, norm_unitary_mul]
  exact specialUnitary_phase_velocity_norm_sq N hN A c

/-- A global Lipschitz bound with the exact quadratic speed. -/
theorem unitaryPhaseFlow_lipschitz (N : ℕ) (hN : 0 < N) (t c : ℝ)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : specialUnitaryLieAlgebra (n := Fin N)) :
    LipschitzWith (Real.toNNReal (Real.sqrt (‖A.val‖ ^ 2 + 2 * c ^ 2)))
      (unitaryPhaseFlow N t c U A) := by
  have h : LipschitzWith (Real.toNNReal (Real.sqrt (‖A.val‖ ^ 2 + 2 * c ^ 2)))
      (fun r => (unitaryPhaseFlow N t c U A r).val) := by
    apply lipschitzWith_of_nnnorm_deriv_le
      (fun s => (unitaryPhaseFlow_hasDerivAt N t c U A s).differentiableAt)
    intro s
    change ‖deriv (fun r => (unitaryPhaseFlow N t c U A r).val) s‖ ≤
      (Real.toNNReal (Real.sqrt (‖A.val‖ ^ 2 + 2 * c ^ 2)) : ℝ)
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    have he := unitaryPhaseFlow_speed_sq N hN t c U A s
    have hs := Real.sq_sqrt (show 0 ≤ ‖A.val‖ ^ 2 + 2 * c ^ 2 by positivity)
    nlinarith [Real.sqrt_nonneg (‖A.val‖ ^ 2 + 2 * c ^ 2),
      norm_nonneg (deriv (fun r => (unitaryPhaseFlow N t c U A r).val) s)]
  exact h

end LogSobolev
