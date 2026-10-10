module

public import LogSobolev.Unitary.HilbertSchmidt
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-! # Haar probability on the actual unitary group

This uses `Measure.haarMeasure ⊤`, normalized on the entire compact group.
The compactness proof uses the entrywise unit-ball bound, as in the inspected
`Weingarten/Haar.lean` local development and `QIT/Symmetry/UnitaryTwirl.lean`.
No external project is imported.
-/

open scoped Matrix.Norms.Frobenius
open Matrix MeasureTheory

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem unitary_entry_norm_le_one (U : Matrix.unitaryGroup n ℂ) (i j : n) :
    ‖U i j‖ ≤ 1 := by
  have h := congrArg (fun A : Matrix n n ℂ => (A i i).re) U.prop.2
  have hr : ∑ k, Complex.normSq (U i k) = 1 := by
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply,
      Complex.mul_conj, Complex.normSq_apply] using h
  have he : Complex.normSq (U i j) ≤ 1 := by
    rw [← hr]
    exact Finset.single_le_sum (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
  rw [Complex.normSq_eq_norm_sq] at he
  nlinarith [norm_nonneg (U i j)]

instance unitaryCompactSpace : CompactSpace (Matrix.unitaryGroup n ℂ) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : ℂ) 1).matrix.of_isClosed_subset isClosed_unitary
  intro U hU i j
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    unitary_entry_norm_le_one ⟨U, hU⟩ i j

noncomputable instance unitaryMeasurableSpace : MeasurableSpace (Matrix.unitaryGroup n ℂ) := borel _
instance unitaryBorelSpace : BorelSpace (Matrix.unitaryGroup n ℂ) := ⟨rfl⟩

/-- Compatibility with the topology inferred through the Frobenius metric.
The structures are definitionally equal; spelling out the metric projection
also makes the instance available at instance-synthesis transparency. -/
instance unitaryMetricBorelSpace :
    @BorelSpace (Matrix.unitaryGroup n ℂ)
      (inferInstance : MetricSpace (Matrix.unitaryGroup n ℂ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      inferInstance := unitaryBorelSpace

/-- Compactness for the same Frobenius metric topology. -/
instance unitaryMetricCompactSpace :
    @CompactSpace (Matrix.unitaryGroup n ℂ)
      (inferInstance : MetricSpace (Matrix.unitaryGroup n ℂ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace :=
  unitaryCompactSpace


/-- Normalized Haar measure, with the topology underlying the Frobenius metric. -/
noncomputable def unitaryHaar (n : Type*) [Fintype n] [DecidableEq n] :
    Measure (Matrix.unitaryGroup n ℂ) := Measure.haarMeasure ⊤

instance : Measure.IsHaarMeasure (unitaryHaar n) := by unfold unitaryHaar; infer_instance
instance : IsProbabilityMeasure (unitaryHaar n) where
  measure_univ := Measure.haarMeasure_self

/-- Left-invariant probability measures on this group equal the chosen Haar measure. -/
theorem eq_unitaryHaar (μ : Measure (Matrix.unitaryGroup n ℂ)) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] : μ = unitaryHaar n := by
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace μ (unitaryHaar n)
  have hc := congrArg (fun ν : Measure (Matrix.unitaryGroup n ℂ) => ν Set.univ) h
  have hc' : Measure.haarScalarFactor μ (unitaryHaar n) = 1 := by
    simpa only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one,
      ENNReal.coe_eq_one] using hc.symm
  simpa [hc'] using h

instance : (unitaryHaar n).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    exact eq_unitaryHaar _

/-- Continuous observables on the compact group are Haar integrable. -/
theorem unitary_integrable_of_continuous {f : Matrix.unitaryGroup n ℂ → ℝ}
    (hf : Continuous f) : Integrable f (unitaryHaar n) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

end LogSobolev
