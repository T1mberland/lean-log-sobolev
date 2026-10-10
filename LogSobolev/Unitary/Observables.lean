module

public import LogSobolev.Unitary.Haar
public import LogSobolev.Geometry.CompactRegularity

@[expose] public section

/-! # Nonconstant admissible observables

The real diagonal coordinate separates the identity from minus the identity.
It is 1-Lipschitz for the unnormalized Hilbert–Schmidt metric and satisfies
all regularity requirements in the intended theorem, in every positive dimension.
-/

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Each entry is bounded by the Frobenius norm (not by a normalized norm). -/
theorem norm_entry_le_frobenius (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  have h : ‖A i j‖ ^ 2 ≤ ∑ k, ∑ l, ‖A k l‖ ^ 2 :=
    (Finset.single_le_sum (fun k _ => sq_nonneg ‖A i k‖) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg ‖A k l‖))
        (Finset.mem_univ i))
  rw [← frobenius_norm_sq] at h
  nlinarith [norm_nonneg A, norm_nonneg (A i j)]

/-- A real matrix coordinate on the unitary group. -/
def entryReal (i j : n) (U : Matrix.unitaryGroup n ℂ) : ℝ := (U i j).re

theorem entryReal_lipschitz (i j : n) : LipschitzWith 1 (entryReal i j) := by
  apply LipschitzWith.of_dist_le_mul
  intro U V
  rw [Real.dist_eq, Subtype.dist_eq, dist_eq_norm]
  change |(U i j).re - (V i j).re| ≤ 1 * ‖(U : Matrix n n ℂ) - V‖
  rw [one_mul, ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans (norm_entry_le_frobenius ((U : Matrix n n ℂ) - (V : Matrix n n ℂ)) i j)

/-- Minus the identity, exhibited as an actual unitary matrix. -/
def negIdentity : Matrix.unitaryGroup n ℂ :=
  ⟨-1, by constructor <;> simp⟩

/-- The diagonal coordinate is nonconstant in every inhabited dimension. -/
theorem entryReal_nonconstant (i : n) :
    entryReal i i (1 : Matrix.unitaryGroup n ℂ) ≠ entryReal i i negIdentity := by
  norm_num [entryReal, negIdentity, Matrix.one_apply]

/-- It is not even Haar-almost-everywhere constant, since Haar has full support. -/
theorem entryReal_not_ae_constant (i : n) (c : ℝ) :
    ¬ entryReal i i =ᵐ[unitaryHaar n] (fun _ => c) := by
  intro h
  have he := (unitaryHaar n).eq_of_ae_eq h (entryReal_lipschitz i i).continuous continuous_const
  exact entryReal_nonconstant i ((congrFun he 1).trans (congrFun he negIdentity).symm)

/-- Every locally Lipschitz observable on U(N) has finite entropy and integrable
squared local slope; this includes nonsmooth locally Lipschitz observables. -/
theorem unitary_regular {f : Matrix.unitaryGroup n ℂ → ℝ} (hf : LocallyLipschitz f) :
    Integrable (fun U => f U ^ 2) (unitaryHaar n) ∧
    Integrable (fun U => f U ^ 2 * Real.log (f U ^ 2)) (unitaryHaar n) ∧
    Integrable (fun U => (localSlope f U).toReal ^ 2) (unitaryHaar n) :=
  ⟨integrable_sq_of_locallyLipschitz hf, integrable_sq_log_of_locallyLipschitz hf,
    integrable_localSlope_sq hf⟩

end LogSobolev
