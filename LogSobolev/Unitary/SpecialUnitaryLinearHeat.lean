module

public import LogSobolev.Unitary.SpecialUnitaryHeatBounds
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Constructed SU heat solutions for affine matrix observables

For `f(U) = c + l(U)`, with `l` a real continuous linear functional on matrices,
the actual sum-of-squares heat equation has the explicit solution
`c + l(U exp(t S))`, where `S = ∑ i, bᵢ²`. The derivative and initial value are
proved, and the maximum principle proves preservation of initial bounds.
This constructs heat solutions on this finite-dimensional class; it does not
supply heat evolution for all smooth or locally Lipschitz functions.
-/

open Matrix
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

/-- The matrix controlling the generator on linear matrix observables. -/
noncomputable def specialUnitaryLinearHeatMatrix (b : ι → specialUnitaryLieAlgebra (n := n)) :
    Matrix n n ℂ := ∑ i, (b i).val * (b i).val

/-- Invariant differentiation of an affine matrix observable. -/
theorem specialUnitaryDeriv_affine
    (A : specialUnitaryLieAlgebra (n := n)) (l : Matrix n n ℂ →L[ℝ] ℝ) (c : ℝ)
    (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryDeriv A (fun V => c + l V.val) U = l (U.val * A.val) := by
  rw [specialUnitaryDeriv_of_ambient A U (l.hasFDerivAt.const_add c).differentiableAt]
  unfold rightMulDeriv
  rw [(l.hasFDerivAt.const_add c).fderiv]

/-- The actual generator preserves the finite-dimensional affine matrix-observable class. -/
theorem specialUnitaryLaplacian_affine
    (b : ι → specialUnitaryLieAlgebra (n := n)) (l : Matrix n n ℂ →L[ℝ] ℝ) (c : ℝ)
    (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryLaplacian b (fun V => c + l V.val) U =
      l (U.val * specialUnitaryLinearHeatMatrix b) := by
  have he A : specialUnitaryDeriv A (fun V => c + l V.val) =
      fun V => l (V.val * A.val) := funext (specialUnitaryDeriv_affine A l c)
  have htwice (A : specialUnitaryLieAlgebra (n := n)) :
      specialUnitaryDeriv A (specialUnitaryDeriv A (fun V => c + l V.val)) U =
        l ((U.val * A.val) * A.val) := by
    rw [he]
    let lA : Matrix n n ℂ →L[ℝ] ℝ := l.comp ((ContinuousLinearMap.mul ℝ (Matrix n n ℂ)).flip A.val)
    change specialUnitaryDeriv A (fun V => lA V.val) U = _
    rw [specialUnitaryDeriv_of_ambient A U lA.differentiableAt]
    unfold rightMulDeriv
    rw [lA.hasFDerivAt.fderiv]
    rfl
  unfold specialUnitaryLaplacian
  simp_rw [htwice]
  simp [specialUnitaryLinearHeatMatrix, Matrix.mul_sum, map_sum, mul_assoc]

/-- An explicit heat evolution for affine matrix observables on the actual SU group. -/
noncomputable def specialUnitaryLinearHeat
    (b : ι → specialUnitaryLieAlgebra (n := n)) (l : Matrix n n ℂ →L[ℝ] ℝ) (c t : ℝ)
    (U : Matrix.specialUnitaryGroup n ℂ) : ℝ :=
  c + l (U.val * NormedSpace.exp (t • specialUnitaryLinearHeatMatrix b))

@[simp] theorem specialUnitaryLinearHeat_zero
    (b : ι → specialUnitaryLieAlgebra (n := n)) (l : Matrix n n ℂ →L[ℝ] ℝ) (c : ℝ)
    (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryLinearHeat b l c 0 U = c + l U.val := by
  simp [specialUnitaryLinearHeat]

/-- Every spatial slice of the constructed affine heat solution is smooth. -/
theorem specialUnitaryLinearHeat_contMDiff
    (b : ι → specialUnitaryLieAlgebra (n := n)) (l : Matrix n n ℂ →L[ℝ] ℝ) (c t : ℝ) :
    ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ (specialUnitaryLinearHeat b l c t) := by
  let E := NormedSpace.exp (t • specialUnitaryLinearHeatMatrix b)
  let lE := l.comp ((ContinuousLinearMap.mul ℝ (Matrix n n ℂ)).flip E)
  exact contMDiff_const.add (lE.contMDiff.comp specialUnitary_val_contMDiff)

/-- Joint continuity of the explicit affine heat evolution. -/
theorem specialUnitaryLinearHeat_continuous
    (b : ι → specialUnitaryLieAlgebra (n := n)) (l : Matrix n n ℂ →L[ℝ] ℝ) (c : ℝ) :
    Continuous (Function.uncurry (specialUnitaryLinearHeat b l c)) := by
  have hE : Continuous (fun t : ℝ => NormedSpace.exp (t • specialUnitaryLinearHeatMatrix b)) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_exp_smul_const (specialUnitaryLinearHeatMatrix b) t).continuousAt
  exact continuous_const.add (l.continuous.comp
    ((continuous_subtype_val.comp continuous_snd).mul (hE.comp continuous_fst)))

/-- The constructed evolution satisfies the actual SU heat equation, with no PDE hypothesis. -/
theorem specialUnitaryLinearHeat_hasDerivAt
    (b : ι → specialUnitaryLieAlgebra (n := n)) (l : Matrix n n ℂ →L[ℝ] ℝ) (c t : ℝ)
    (U : Matrix.specialUnitaryGroup n ℂ) :
    HasDerivAt (fun r => specialUnitaryLinearHeat b l c r U)
      (specialUnitaryLaplacian b (specialUnitaryLinearHeat b l c t) U) t := by
  let E := NormedSpace.exp (t • specialUnitaryLinearHeatMatrix b)
  let lE := l.comp ((ContinuousLinearMap.mul ℝ (Matrix n n ℂ)).flip E)
  have hL : specialUnitaryLaplacian b (specialUnitaryLinearHeat b l c t) U =
      l (U.val * (specialUnitaryLinearHeatMatrix b * E)) := by
    change specialUnitaryLaplacian b (fun V => c + lE V.val) U = _
    rw [specialUnitaryLaplacian_affine]
    change l ((U.val * specialUnitaryLinearHeatMatrix b) * E) = _
    rw [mul_assoc]
  rw [hL]
  exact (l.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_exp_smul_const' (specialUnitaryLinearHeatMatrix b) t).const_mul U.val)).const_add c

/-- The explicitly constructed heat evolution preserves every initial lower bound. -/
theorem specialUnitaryLinearHeat_lower_bound
    (b : ι → specialUnitaryLieAlgebra (n := n)) (l : Matrix n n ℂ →L[ℝ] ℝ)
    (c : ℝ) {a T : ℝ} (hT : 0 ≤ T)
    (hinit : ∀ U : Matrix.specialUnitaryGroup n ℂ, a ≤ c + l U.val) :
    ∀ U, a ≤ specialUnitaryLinearHeat b l c T U := by
  apply specialUnitary_heat_lower_bound b hT (specialUnitaryLinearHeat_continuous b l c)
    (fun t _ => specialUnitaryLinearHeat_contMDiff b l c t)
    (fun t _ U => specialUnitaryLinearHeat_hasDerivAt b l c t U)
    (fun _ _ => rfl)
  simpa only [specialUnitaryLinearHeat_zero] using hinit

/-- The explicitly constructed heat evolution preserves every initial upper bound. -/
theorem specialUnitaryLinearHeat_upper_bound
    (b : ι → specialUnitaryLieAlgebra (n := n)) (l : Matrix n n ℂ →L[ℝ] ℝ)
    (c : ℝ) {a T : ℝ} (hT : 0 ≤ T)
    (hinit : ∀ U : Matrix.specialUnitaryGroup n ℂ, c + l U.val ≤ a) :
    ∀ U, specialUnitaryLinearHeat b l c T U ≤ a := by
  apply specialUnitary_heat_upper_bound b hT (specialUnitaryLinearHeat_continuous b l c)
    (fun t _ => specialUnitaryLinearHeat_contMDiff b l c t)
    (fun t _ U => specialUnitaryLinearHeat_hasDerivAt b l c t U)
    (fun _ _ => rfl)
  simpa only [specialUnitaryLinearHeat_zero] using hinit

/-- Strictly positive affine initial data give strictly positive heat solutions for all forward times.
Compactness supplies a positive uniform lower bound; no positivity of the matrix exponential is assumed. -/
theorem specialUnitaryLinearHeat_pos
    (b : ι → specialUnitaryLieAlgebra (n := n)) (l : Matrix n n ℂ →L[ℝ] ℝ)
    (c : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hinit : ∀ U : Matrix.specialUnitaryGroup n ℂ, 0 < c + l U.val) :
    ∀ U, 0 < specialUnitaryLinearHeat b l c T U := by
  have hc : Continuous (fun U : Matrix.specialUnitaryGroup n ℂ => c + l U.val) :=
    continuous_const.add (l.continuous.comp continuous_subtype_val)
  obtain ⟨V, _, hm⟩ := isCompact_univ.exists_isMinOn
    ⟨(1 : Matrix.specialUnitaryGroup n ℂ), Set.mem_univ _⟩ hc.continuousOn
  have hb := specialUnitaryLinearHeat_lower_bound b l c hT
    (fun U => isMinOn_iff.mp hm U (Set.mem_univ U))
  exact fun U => lt_of_lt_of_le (hinit V) (hb U)

end LogSobolev
