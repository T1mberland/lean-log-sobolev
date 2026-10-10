import LogSobolev.Unitary.Haar

/-! # Special unitary Haar probability and its inclusion into U(N)

Only topological, metric and measure infrastructure is established here.
No curvature estimate or logarithmic Sobolev inequality is asserted.
-/

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The canonical inclusion of the existing Mathlib SU group into its U group. -/
def specialUnitaryInclusion : Matrix.specialUnitaryGroup n ℂ →* Matrix.unitaryGroup n ℂ where
  toFun U := ⟨U.val, U.prop.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem specialUnitaryInclusion_isometry :
    Isometry (specialUnitaryInclusion : Matrix.specialUnitaryGroup n ℂ → Matrix.unitaryGroup n ℂ) :=
  fun _ _ => rfl

theorem isClosed_specialUnitary :
    IsClosed (Matrix.specialUnitaryGroup n ℂ : Set (Matrix n n ℂ)) := by
  exact isClosed_unitary.inter (isClosed_eq continuous_id.matrix_det continuous_const)

instance specialUnitaryCompactSpace : CompactSpace (Matrix.specialUnitaryGroup n ℂ) := by
  apply isCompact_iff_compactSpace.mp
  exact (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace (Matrix.unitaryGroup n ℂ))).of_isClosed_subset
    isClosed_specialUnitary (fun _ h => h.1)

instance specialUnitaryContinuousInv : ContinuousInv (Matrix.specialUnitaryGroup n ℂ) where
  continuous_inv := by
    rw [continuous_induced_rng]
    exact continuous_star.comp continuous_subtype_val

instance specialUnitaryTopologicalGroup : IsTopologicalGroup (Matrix.specialUnitaryGroup n ℂ) where

instance specialUnitaryMeasurableSpace : MeasurableSpace (Matrix.specialUnitaryGroup n ℂ) := borel _
instance specialUnitaryBorelSpace : BorelSpace (Matrix.specialUnitaryGroup n ℂ) := ⟨rfl⟩

/-- Haar probability on SU, normalized on the entire compact group. -/
noncomputable def specialUnitaryHaar (n : Type*) [Fintype n] [DecidableEq n] :
    Measure (Matrix.specialUnitaryGroup n ℂ) := Measure.haarMeasure ⊤

instance : Measure.IsHaarMeasure (specialUnitaryHaar n) := by
  unfold specialUnitaryHaar
  infer_instance

instance : IsProbabilityMeasure (specialUnitaryHaar n) where
  measure_univ := Measure.haarMeasure_self

end LogSobolev
