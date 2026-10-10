module

public import LogSobolev.Unitary.SpecialUnitaryFlow
public import LogSobolev.Unitary.SpecialUnitaryGenerator
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Haar integration and invariant derivatives on SU

Compactness gives integrable domination for differentiation under the Haar
integral. Right invariance along the actual exponential curves then proves that
invariant derivatives have integral zero. All measures below are the existing
normalized Haar probability on the original matrix SU group.
-/

open Matrix MeasureTheory Filter Set Topology
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Uniqueness of normalized left-invariant measure on the actual compact SU group. -/
theorem eq_specialUnitaryHaar (μ : Measure (Matrix.specialUnitaryGroup n ℂ))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] : μ = specialUnitaryHaar n := by
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace μ (specialUnitaryHaar n)
  have hc := congrArg (fun ν : Measure (Matrix.specialUnitaryGroup n ℂ) => ν Set.univ) h
  have hc' : Measure.haarScalarFactor μ (specialUnitaryHaar n) = 1 := by
    simpa only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul,
      mul_one, ENNReal.coe_eq_one] using hc.symm
  simpa [hc'] using h

instance : (specialUnitaryHaar n).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    exact eq_specialUnitaryHaar _

/-- Continuous real functions on SU are integrable for the actual normalized Haar measure. -/
theorem specialUnitary_integrable_of_continuous
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ} (hf : Continuous f) :
    Integrable f (specialUnitaryHaar n) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Smooth invariant derivatives have zero Haar integral, proved by differentiating Haar invariance. -/
theorem specialUnitary_integral_deriv_eq_zero
    (A : specialUnitaryLieAlgebra (n := n))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f) :
    (∫ U, specialUnitaryDeriv A f U ∂specialUnitaryHaar n) = 0 := by
  have hD := (specialUnitaryDeriv_contMDiff A hf).continuous
  obtain ⟨M, hM⟩ := (isCompact_univ : IsCompact (univ : Set (Matrix.specialUnitaryGroup n ℂ))).exists_bound_of_continuousOn
    hD.continuousOn
  have hF (t : ℝ) : Continuous (fun U => f (U * specialUnitaryExpCurve A t)) :=
    hf.continuous.comp (continuous_id.mul continuous_const)
  have hF' (t : ℝ) : Continuous (fun U => specialUnitaryDeriv A f (U * specialUnitaryExpCurve A t)) :=
    hD.comp (continuous_id.mul continuous_const)
  have hI := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := specialUnitaryHaar n) (s := univ) (x₀ := (0 : ℝ))
    (F := fun t U => f (U * specialUnitaryExpCurve A t))
    (F' := fun t U => specialUnitaryDeriv A f (U * specialUnitaryExpCurve A t))
    (bound := fun _ => M) (by simp)
    (Eventually.of_forall fun t => (hF t).aestronglyMeasurable)
    (specialUnitary_integrable_of_continuous (hF 0))
    (hF' 0).aestronglyMeasurable
    (Eventually.of_forall fun U t _ => hM _ (mem_univ _)) (integrable_const M)
    (Eventually.of_forall fun U t _ => specialUnitary_hasDerivAt_mul_exp A U hf t)
  have he : (fun t : ℝ => ∫ U, f (U * specialUnitaryExpCurve A t) ∂specialUnitaryHaar n) =
      fun _ => ∫ U, f U ∂specialUnitaryHaar n := by
    funext t
    exact integral_mul_right_eq_self f (specialUnitaryExpCurve A t)
  have hd := hI.2
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const 0 (∫ U, f U ∂specialUnitaryHaar n))
  simpa only [specialUnitaryExpCurve_zero, mul_one] using hz

/-- Integration by parts for an actual invariant SU derivative. -/
theorem specialUnitary_integral_mul_deriv
    (A : specialUnitaryLieAlgebra (n := n))
    {f g : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ g) :
    (∫ U, f U * specialUnitaryDeriv A g U ∂specialUnitaryHaar n) =
      -(∫ U, g U * specialUnitaryDeriv A f U ∂specialUnitaryHaar n) := by
  have h := specialUnitary_integral_deriv_eq_zero A (hf.mul hg)
  rw [specialUnitaryDeriv_mul A hf hg] at h
  have hfg := specialUnitary_integrable_of_continuous
    (hf.continuous.mul (specialUnitaryDeriv_contMDiff A hg).continuous)
  have hgf := specialUnitary_integrable_of_continuous
    (hg.continuous.mul (specialUnitaryDeriv_contMDiff A hf).continuous)
  simp only [Pi.add_apply, Pi.mul_apply] at h
  have hi := integral_add hfg hgf
  simp only [Pi.mul_apply] at hi
  rw [hi] at h
  linarith

variable {ι : Type*} [Fintype ι]

/-- The actual generator has zero Haar integral on every smooth real test. -/
theorem specialUnitary_integral_laplacian_eq_zero
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f) :
    (∫ U, specialUnitaryLaplacian b f U ∂specialUnitaryHaar n) = 0 := by
  unfold specialUnitaryLaplacian
  rw [integral_finset_sum Finset.univ (fun i _ => specialUnitary_integrable_of_continuous
    (specialUnitaryDeriv_contMDiff (b i) (specialUnitaryDeriv_contMDiff (b i) hf)).continuous)]
  simp only [specialUnitary_integral_deriv_eq_zero _ (specialUnitaryDeriv_contMDiff _ hf),
    Finset.sum_const_zero]

/-- The generator-defined carré du champ of smooth tests is smooth. -/
theorem specialUnitaryGamma_contMDiff
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {f g : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ g) :
    ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ (specialUnitaryGamma b f g) := by
  have he : specialUnitaryGamma b f g =
      fun U => ∑ i, specialUnitaryDeriv (b i) f U * specialUnitaryDeriv (b i) g U :=
    funext (specialUnitaryGamma_eq b hf hg)
  rw [he]
  exact ContMDiff.sum fun i _ =>
    (specialUnitaryDeriv_contMDiff (b i) hf).mul (specialUnitaryDeriv_contMDiff (b i) hg)

/-- Haar integration by parts identifies the generator with its Dirichlet energy. -/
theorem specialUnitary_integral_mul_laplacian
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {f g : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ g) :
    (∫ U, f U * specialUnitaryLaplacian b g U ∂specialUnitaryHaar n) =
      -(∫ U, specialUnitaryGamma b f g U ∂specialUnitaryHaar n) := by
  have hD i := specialUnitaryDeriv_contMDiff (b i) hg
  have hDD i := specialUnitaryDeriv_contMDiff (b i) (hD i)
  simp_rw [specialUnitaryLaplacian, Finset.mul_sum, specialUnitaryGamma_eq b hf hg]
  rw [integral_finset_sum Finset.univ
    (f := fun i U => f U * specialUnitaryDeriv (b i) (specialUnitaryDeriv (b i) g) U)
    (fun i _ => specialUnitary_integrable_of_continuous
      (hf.continuous.mul (hDD i).continuous))]
  rw [integral_finset_sum Finset.univ
    (f := fun i U => specialUnitaryDeriv (b i) f U * specialUnitaryDeriv (b i) g U)
    (fun i _ => specialUnitary_integrable_of_continuous
      ((specialUnitaryDeriv_contMDiff (b i) hf).continuous.mul (hD i).continuous))]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [mul_comm] using specialUnitary_integral_mul_deriv (b i) hf (hD i)

/-- The actual generator is symmetric in the Haar integral on smooth real tests. -/
theorem specialUnitary_laplacian_symmetric
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {f g : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ g) :
    (∫ U, f U * specialUnitaryLaplacian b g U ∂specialUnitaryHaar n) =
      ∫ U, g U * specialUnitaryLaplacian b f U ∂specialUnitaryHaar n := by
  rw [specialUnitary_integral_mul_laplacian b hf hg,
    specialUnitary_integral_mul_laplacian b hg hf]
  simp_rw [specialUnitaryGamma_eq b hf hg, specialUnitaryGamma_eq b hg hf, mul_comm]

/-- The Haar quadratic form of the actual generator is nonpositive. -/
theorem specialUnitary_laplacian_nonpos
    (b : ι → specialUnitaryLieAlgebra (n := n))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f) :
    (∫ U, f U * specialUnitaryLaplacian b f U ∂specialUnitaryHaar n) ≤ 0 := by
  rw [specialUnitary_integral_mul_laplacian b hf hf]
  exact neg_nonpos.mpr (integral_nonneg (specialUnitaryGamma_nonneg b hf))

end LogSobolev
