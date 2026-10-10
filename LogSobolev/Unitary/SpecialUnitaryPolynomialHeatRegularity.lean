import LogSobolev.Unitary.SpecialUnitaryPolynomialHeat

/-! # Regularity of the constructed polynomial heat flow

Finite dimensionality makes actual invariant differentiation continuous on each
polynomial space. Consequently mixed time/spatial derivatives follow from the
constructed vector-valued evolution, without a mixed-regularity assumption.
For applying compact integral differentiation, the forward evolution is extended
constantly to negative times. Its heat equation is asserted only at positive times.
-/

open Matrix Filter Topology
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

/-- Any continuous linear observable of polynomial heat is jointly continuous. -/
theorem specialUnitaryPolynomialHeat_clm_continuous
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d)
    (A : specialUnitaryPolynomialSpace (n := n) d →L[ℝ]
      specialUnitaryPolynomialSpace (n := n) d) :
    Continuous (fun p : ℝ × Matrix.specialUnitaryGroup n ℂ =>
      (A (specialUnitaryPolynomialHeat b d f p.1)).val p.2) := by
  have ht : Continuous (specialUnitaryPolynomialHeat b d f) :=
    continuous_iff_continuousAt.mpr fun t => (specialUnitaryPolynomialHeat_hasDerivAt b d f t).continuousAt
  have hc := (specialUnitaryPolynomialToContinuousCLM d).continuous.comp (A.continuous.comp ht)
  exact continuous_eval.comp ((hc.comp continuous_fst).prodMk continuous_snd)

/-- Forward polynomial heat, constantly extended before time zero. -/
noncomputable def specialUnitaryPolynomialForwardHeat
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) (t : ℝ) :
    specialUnitaryPolynomialSpace (n := n) d :=
  specialUnitaryPolynomialHeat b d f (max t 0)

theorem specialUnitaryPolynomialForwardHeat_eq
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) {t : ℝ} (ht : 0 ≤ t) :
    specialUnitaryPolynomialForwardHeat b d f t = specialUnitaryPolynomialHeat b d f t := by
  simp only [specialUnitaryPolynomialForwardHeat, max_eq_left ht]

/-- Positive polynomial initial data give a globally positive extended family. -/
theorem specialUnitaryPolynomialForwardHeat_pos
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) (hpos : ∀ U, 0 < f.val U)
    (t : ℝ) (U : Matrix.specialUnitaryGroup n ℂ) :
    0 < (specialUnitaryPolynomialForwardHeat b d f t).val U :=
  specialUnitaryPolynomialHeat_pos b d f (le_max_right t 0) hpos U

/-- Joint continuity survives the constant extension to negative times. -/
theorem specialUnitaryPolynomialForwardHeat_clm_continuous
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d)
    (A : specialUnitaryPolynomialSpace (n := n) d →L[ℝ]
      specialUnitaryPolynomialSpace (n := n) d) :
    Continuous (fun p : ℝ × Matrix.specialUnitaryGroup n ℂ =>
      (A (specialUnitaryPolynomialForwardHeat b d f p.1)).val p.2) :=
  (specialUnitaryPolynomialHeat_clm_continuous b d f A).comp
    ((continuous_fst.max continuous_const).prodMk continuous_snd)

/-- At positive times the extended family solves the actual vector-valued heat equation. -/
theorem specialUnitaryPolynomialForwardHeat_hasDerivAt
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (specialUnitaryPolynomialForwardHeat b d f)
      (specialUnitaryPolynomialLaplacianCLM b d
        (specialUnitaryPolynomialForwardHeat b d f t)) t := by
  rw [specialUnitaryPolynomialForwardHeat_eq b d f ht.le]
  apply (specialUnitaryPolynomialHeat_hasDerivAt b d f t).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with r hr
  exact specialUnitaryPolynomialForwardHeat_eq b d f hr.le

/-- Mixed derivatives are obtained by composing the constructed heat ODE with a linear map. -/
theorem specialUnitaryPolynomialForwardHeat_clm_hasDerivAt
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d)
    (A : specialUnitaryPolynomialSpace (n := n) d →L[ℝ]
      specialUnitaryPolynomialSpace (n := n) d)
    {t : ℝ} (ht : 0 < t) (U : Matrix.specialUnitaryGroup n ℂ) :
    HasDerivAt (fun r => (A (specialUnitaryPolynomialForwardHeat b d f r)).val U)
      ((A (specialUnitaryPolynomialLaplacianCLM b d
        (specialUnitaryPolynomialForwardHeat b d f t))).val U) t :=
  ((specialUnitaryPolynomialEval d U).comp A).hasFDerivAt.comp_hasDerivAt t
    (specialUnitaryPolynomialForwardHeat_hasDerivAt b d f ht)

end LogSobolev
