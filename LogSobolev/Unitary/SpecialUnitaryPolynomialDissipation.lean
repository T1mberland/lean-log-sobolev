module

public import LogSobolev.Unitary.SpecialUnitaryPolynomialHeatRegularity
public import LogSobolev.Unitary.SpecialUnitaryFisherDifferentiation
public import LogSobolev.Analysis.ExponentialDecay

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Entropy and Fisher dissipation for constructed SU polynomial heat

These theorems supply their own heat evolution and all its regularity, starting
only from a strictly positive polynomial observable. For a real Hilbert–Schmidt
orthonormal basis, the Fisher differential inequality has coefficient `N`.
Equilibrium convergence and the resulting logarithmic Sobolev inequality are
not asserted here.
-/

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

/-- Entropy dissipation along the constructed forward polynomial heat flow. -/
theorem specialUnitaryPolynomialForwardHeat_hasDerivAt_entropy
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) (hpos : ∀ U, 0 < f.val U)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r => entropy (specialUnitaryHaar n)
      (specialUnitaryPolynomialForwardHeat b d f r).val)
      (-(∫ U, specialUnitaryGamma b (specialUnitaryPolynomialForwardHeat b d f t).val
        (specialUnitaryPolynomialForwardHeat b d f t).val U /
        (specialUnitaryPolynomialForwardHeat b d f t).val U ∂specialUnitaryHaar n)) t := by
  let P := specialUnitaryPolynomialForwardHeat b d f
  let L := specialUnitaryPolynomialLaplacianCLM b d
  apply specialUnitary_hasDerivAt_entropy b (F := fun r => (P r).val)
    (Q := fun r => (L (P r)).val) (s := Set.Ioi 0)
    (specialUnitaryPolynomialForwardHeat_clm_continuous b d f (ContinuousLinearMap.id ℝ _))
    (specialUnitaryPolynomialForwardHeat_clm_continuous b d f L)
    (specialUnitaryPolynomialForwardHeat_pos b d f hpos)
    (fun r hr U => specialUnitaryPolynomialForwardHeat_clm_hasDerivAt b d f
      (ContinuousLinearMap.id ℝ _) hr U) t (Ioi_mem_nhds ht) (P t).val.contMDiff
  funext U
  exact specialUnitaryPolynomialLaplacian_apply b d (P t) U

/-- Exact Fisher dissipation for constructed positive polynomial heat, without
any supplied trajectory, PDE, or mixed-derivative hypothesis. -/
theorem specialUnitaryPolynomialForwardHeat_hasDerivAt_fisher
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) (hpos : ∀ U, 0 < f.val U)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun r => ∫ U, specialUnitaryGamma b (specialUnitaryPolynomialForwardHeat b d f r).val
        (specialUnitaryPolynomialForwardHeat b d f r).val U /
        (specialUnitaryPolynomialForwardHeat b d f r).val U ∂specialUnitaryHaar n)
      (-2 * (∫ U, (specialUnitaryPolynomialForwardHeat b d f t).val U *
        specialUnitaryGammaTwo b (Real.log ∘ (specialUnitaryPolynomialForwardHeat b d f t).val) U
        ∂specialUnitaryHaar n)) t := by
  let P := specialUnitaryPolynomialForwardHeat b d f
  let L := specialUnitaryPolynomialLaplacianCLM b d
  apply specialUnitary_hasDerivAt_fisher_of_heat b (F := fun r => (P r).val)
    (Q := fun r => (L (P r)).val) (s := Set.Ioi 0)
    (specialUnitaryPolynomialForwardHeat_clm_continuous b d f (ContinuousLinearMap.id ℝ _))
    (specialUnitaryPolynomialForwardHeat_clm_continuous b d f L)
    (fun r U => ne_of_gt (specialUnitaryPolynomialForwardHeat_pos b d f hpos r U))
    (fun r => (P r).val.contMDiff) (fun r => (L (P r)).val.contMDiff)
    (fun i => specialUnitaryPolynomialForwardHeat_clm_continuous b d f
      (specialUnitaryPolynomialDerivCLM (b i) d))
    (fun i => specialUnitaryPolynomialForwardHeat_clm_continuous b d f
      ((specialUnitaryPolynomialDerivCLM (b i) d).comp L))
    (fun r hr U => specialUnitaryPolynomialForwardHeat_clm_hasDerivAt b d f
      (ContinuousLinearMap.id ℝ _) hr U)
    (fun i r hr U => specialUnitaryPolynomialForwardHeat_clm_hasDerivAt b d f
      (specialUnitaryPolynomialDerivCLM (b i) d) hr U)
    t (Ioi_mem_nhds ht)
  funext U
  exact specialUnitaryPolynomialLaplacian_apply b d (P t) U

/-- The constructed polynomial heat flow satisfies `I'(t) ≤ -N I(t)` for the
unnormalized real Hilbert–Schmidt orthonormal generator. -/
theorem specialUnitaryPolynomialForwardHeat_fisher_deriv_le
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n))) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) (hpos : ∀ U, 0 < f.val U)
    {t : ℝ} (ht : 0 < t) :
    deriv (fun r => ∫ U, specialUnitaryGamma b (specialUnitaryPolynomialForwardHeat b d f r).val
      (specialUnitaryPolynomialForwardHeat b d f r).val U /
      (specialUnitaryPolynomialForwardHeat b d f r).val U ∂specialUnitaryHaar n) t ≤
    -(Fintype.card n : ℝ) * (∫ U,
      specialUnitaryGamma b (specialUnitaryPolynomialForwardHeat b d f t).val
        (specialUnitaryPolynomialForwardHeat b d f t).val U /
      (specialUnitaryPolynomialForwardHeat b d f t).val U ∂specialUnitaryHaar n) := by
  rw [(specialUnitaryPolynomialForwardHeat_hasDerivAt_fisher b d f hpos ht).deriv]
  have h := specialUnitary_weighted_gammaTwo_log_lower_bound b
    (specialUnitaryPolynomialForwardHeat b d f t).val.contMDiff
    (specialUnitaryPolynomialForwardHeat_pos b d f hpos t)
  linarith

/-- Fisher information is continuous even at the initial-time endpoint. -/
theorem specialUnitaryPolynomialForwardHeat_fisher_continuous
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) (hpos : ∀ U, 0 < f.val U) :
    Continuous (fun r => ∫ U,
      specialUnitaryGamma b (specialUnitaryPolynomialForwardHeat b d f r).val
        (specialUnitaryPolynomialForwardHeat b d f r).val U /
      (specialUnitaryPolynomialForwardHeat b d f r).val U ∂specialUnitaryHaar n) := by
  let P := specialUnitaryPolynomialForwardHeat b d f
  have hF : Continuous (fun p : ℝ × Matrix.specialUnitaryGroup n ℂ => (P p.1).val p.2) :=
    specialUnitaryPolynomialForwardHeat_clm_continuous b d f (ContinuousLinearMap.id ℝ _)
  have hG : Continuous (fun p : ℝ × Matrix.specialUnitaryGroup n ℂ =>
      specialUnitaryGamma b (P p.1).val (P p.1).val p.2) := by
    simp_rw [specialUnitaryGamma_eq b (P _).val.contMDiff (P _).val.contMDiff]
    apply continuous_finset_sum
    intro i _
    have hD := specialUnitaryPolynomialForwardHeat_clm_continuous b d f
      (specialUnitaryPolynomialDerivCLM (b i) d)
    exact hD.mul hD
  have h := continuous_parametric_integral_of_continuous (μ := specialUnitaryHaar n)
    (f := fun r U => specialUnitaryGamma b (P r).val (P r).val U / (P r).val U)
    (hG.div hF (fun p => ne_of_gt (specialUnitaryPolynomialForwardHeat_pos b d f hpos p.1 p.2)))
    isCompact_univ
  simpa only [Measure.restrict_univ] using h

/-- Integrated Fisher decay with exact rate `N`, including time zero, for every
strictly positive finite-degree polynomial observable on SU(N). -/
theorem specialUnitaryPolynomialForwardHeat_fisher_le_exp
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n))) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) (hpos : ∀ U, 0 < f.val U)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ U, specialUnitaryGamma b (specialUnitaryPolynomialForwardHeat b d f t).val
      (specialUnitaryPolynomialForwardHeat b d f t).val U /
      (specialUnitaryPolynomialForwardHeat b d f t).val U ∂specialUnitaryHaar n) ≤
    Real.exp (-(Fintype.card n : ℝ) * t) *
      (∫ U, specialUnitaryGamma b f.val f.val U / f.val U ∂specialUnitaryHaar n) := by
  have h := le_exp_mul_of_deriv_le
    (specialUnitaryPolynomialForwardHeat_fisher_continuous b d f hpos).continuousOn
    (fun r hr => (specialUnitaryPolynomialForwardHeat_hasDerivAt_fisher b d f hpos hr).differentiableAt)
    (fun r hr => specialUnitaryPolynomialForwardHeat_fisher_deriv_le b d f hpos hr) ht
  simpa only [specialUnitaryPolynomialForwardHeat, max_self, specialUnitaryPolynomialHeat_zero] using h

end LogSobolev
