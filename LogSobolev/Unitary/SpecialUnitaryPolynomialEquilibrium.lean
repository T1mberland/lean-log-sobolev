module

public import LogSobolev.Unitary.SpecialUnitaryPolynomialFunctionals
public import LogSobolev.Unitary.SpecialUnitaryPolynomialEnergyDecay
public import LogSobolev.Unitary.SpecialUnitaryZeroEnergy

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Equilibrium of constructed polynomial SU heat

The orbit is bounded in a finite-dimensional space with its actual supremum
norm. Energy decay and continuity force every cluster point to have zero Haar
energy. The proved connectedness/kernel theorem identifies it as a constant,
and conservation of normalized Haar mass uniquely fixes that constant. Compactness
then gives convergence of the whole orbit and vanishing limiting entropy.
-/

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

/-- Constructed positive polynomial heat converges in the actual supremum norm to its Haar mean. -/
theorem specialUnitaryPolynomialForwardHeat_tendsto_mean
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n))) (d : ℕ)
    (hN : 0 < Fintype.card n)
    (f : specialUnitaryPolynomialSpace (n := n) d) (hpos : ∀ U, 0 < f.val U) :
    Tendsto (specialUnitaryPolynomialForwardHeat b d f) atTop
      (𝓝 (specialUnitaryPolynomialConst d (∫ U, f.val U ∂specialUnitaryHaar n))) := by
  let P := specialUnitaryPolynomialForwardHeat b d f
  have hE := specialUnitaryPolynomialForwardHeat_energy_tendsto_zero b d hN f hpos
  have hm (t : ℝ) : (∫ U, (P t).val U ∂specialUnitaryHaar n) =
      ∫ U, f.val U ∂specialUnitaryHaar n :=
    specialUnitaryPolynomialHeat_integral b d f (max t 0)
  have hmass : Tendsto (fun t => ∫ U, (P t).val U ∂specialUnitaryHaar n) atTop
      (𝓝 (∫ U, f.val U ∂specialUnitaryHaar n)) := by
    simp_rw [hm]
    exact tendsto_const_nhds
  apply (isCompact_closedBall (0 : specialUnitaryPolynomialSpace (n := n) d) ‖f‖).tendsto_nhds_of_unique_mapClusterPt
  · apply Eventually.of_forall
    intro t
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact specialUnitaryPolynomialHeat_norm_le b d f (le_max_right t 0)
  · intro g _ hg
    have hz : (∫ U, specialUnitaryGamma b g.val g.val U ∂specialUnitaryHaar n) = 0 :=
      eq_of_nhds_neBot (ClusterPt.mono
        (hg.continuousAt_comp
          (f := fun q : specialUnitaryPolynomialSpace (n := n) d =>
            ∫ U, specialUnitaryGamma b q.val q.val U ∂specialUnitaryHaar n)
          (specialUnitaryPolynomial_energy_continuous b d).continuousAt) hE)
    have hmg : (∫ U, g.val U ∂specialUnitaryHaar n) = ∫ U, f.val U ∂specialUnitaryHaar n :=
      eq_of_nhds_neBot (ClusterPt.mono
        (hg.continuousAt_comp
          (f := fun q : specialUnitaryPolynomialSpace (n := n) d => ∫ U, q.val U ∂specialUnitaryHaar n)
          (specialUnitaryPolynomial_integral_continuous d).continuousAt) hmass)
    have he := specialUnitary_eq_mean_of_integral_gamma_eq_zero b g.val.contMDiff hz
    apply Subtype.ext
    ext U
    rw [specialUnitaryPolynomialConst_apply]
    exact (congrFun he U).trans hmg

/-- Limiting entropy vanishes for the constructed positive polynomial heat flow. -/
theorem specialUnitaryPolynomialForwardHeat_entropy_tendsto_zero
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n))) (d : ℕ)
    (hN : 0 < Fintype.card n)
    (f : specialUnitaryPolynomialSpace (n := n) d) (hpos : ∀ U, 0 < f.val U) :
    Tendsto (fun t => entropy (specialUnitaryHaar n)
      (specialUnitaryPolynomialForwardHeat b d f t).val) atTop (𝓝 0) := by
  have h := (specialUnitaryPolynomial_entropy_continuous (n := n) d).continuousAt.tendsto.comp
    (specialUnitaryPolynomialForwardHeat_tendsto_mean b d hN f hpos)
  have he : (fun U => (specialUnitaryPolynomialConst (n := n) d
      (∫ U, f.val U ∂specialUnitaryHaar n)).val U) =
      (fun _ => ∫ U, f.val U ∂specialUnitaryHaar n) := by
    funext U
    exact specialUnitaryPolynomialConst_apply _ _ U
  simpa only [he, entropy_const, Function.comp_def] using h

end LogSobolev
