module

public import LogSobolev.Unitary.SpecialUnitaryPolynomialEquilibrium
public import LogSobolev.Analysis.DissipationBound
public import LogSobolev.Unitary.SpecialUnitarySquareEnergy

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Logarithmic Sobolev inequality for polynomial SU observables

The constructed heat flow, proved dissipation and exponential Fisher decay,
and proved zero limiting entropy give the positive-density bound `Ent(g) ≤ I(g)/N`.
Regularizing squares and taking ε to zero gives `Ent(f²) ≤ (4/N) ∫ Γ(f,f)`
for all real polynomial observables, including functions with zeros.
The underlying measure is actual normalized Haar measure and the generator uses
an orthonormal basis for the unnormalized real Hilbert–Schmidt inner product.
Extension to all locally Lipschitz functions and local-slope identification
remain separate obligations.
-/

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι]

/-- The positive-density logarithmic Sobolev inequality for every finite-degree
polynomial observable, proved from its constructed heat flow. -/
theorem specialUnitaryPolynomial_entropy_le_fisher
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n))) (d : ℕ)
    (hN : 0 < Fintype.card n)
    (f : specialUnitaryPolynomialSpace (n := n) d) (hpos : ∀ U, 0 < f.val U) :
    entropy (specialUnitaryHaar n) f.val ≤
      (1 / (Fintype.card n : ℝ)) *
        (∫ U, specialUnitaryGamma b f.val f.val U / f.val U ∂specialUnitaryHaar n) := by
  have hP : Continuous (specialUnitaryPolynomialForwardHeat b d f) := by
    have h : Continuous (specialUnitaryPolynomialHeat b d f) :=
      continuous_iff_continuousAt.mpr fun t => (specialUnitaryPolynomialHeat_hasDerivAt b d f t).continuousAt
    exact h.comp (continuous_id.max continuous_const)
  have h := initial_le_div_of_dissipation_decay
    (by exact_mod_cast hN : 0 < (Fintype.card n : ℝ))
    ((specialUnitaryPolynomial_entropy_continuous d).comp hP).continuousOn
    (fun t ht => specialUnitaryPolynomialForwardHeat_hasDerivAt_entropy b d f hpos ht)
    (fun t ht => specialUnitaryPolynomialForwardHeat_fisher_le_exp b d f hpos ht.le)
    (specialUnitaryPolynomialForwardHeat_entropy_tendsto_zero b d hN f hpos)
  simpa only [Function.comp_apply, specialUnitaryPolynomialForwardHeat, max_self,
    specialUnitaryPolynomialHeat_zero, one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using h

/-- The squared-function logarithmic Sobolev bound for every real polynomial
observable, with coefficient `4/N` (LSI constant `2/N`). No sign or nonvanishing
hypothesis is imposed on the observable. -/
theorem specialUnitaryPolynomial_entropy_sq_le
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n))) (d : ℕ)
    (hN : 0 < Fintype.card n)
    (f : specialUnitaryPolynomialSpace (n := n) d) :
    entropy (specialUnitaryHaar n) (fun U => f.val U ^ 2) ≤
      (4 / (Fintype.card n : ℝ)) *
        (∫ U, specialUnitaryGamma b f.val f.val U ∂specialUnitaryHaar n) := by
  let q : specialUnitaryPolynomialSpace (n := n) (d + d) :=
    ⟨f.val * f.val, specialUnitaryPolynomialSpace_mul_mem f.prop f.prop⟩
  let g : ℝ → specialUnitaryPolynomialSpace (n := n) (d + d) :=
    fun ε => q + specialUnitaryPolynomialConst (d + d) ε
  have hg (ε : ℝ) : ((g ε).val : Matrix.specialUnitaryGroup n ℂ → ℝ) =
      fun U => f.val U ^ 2 + ε := by
    funext U
    change f.val U * f.val U + ε * 1 = f.val U ^ 2 + ε
    ring
  have hc : Continuous (fun ε => entropy (specialUnitaryHaar n) (g ε).val) :=
    (specialUnitaryPolynomial_entropy_continuous (d + d)).comp
      (continuous_const.add (specialUnitaryPolynomialConst_continuous (d + d)))
  have ht : Tendsto (fun ε => entropy (specialUnitaryHaar n) (g ε).val)
      (𝓝[>] (0 : ℝ)) (𝓝 (entropy (specialUnitaryHaar n) (fun U => f.val U ^ 2))) := by
    have h := (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa only [hg 0, add_zero] using h
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hp : ∀ U, 0 < (g ε).val U := by
    rw [hg ε]
    exact fun U => add_pos_of_nonneg_of_pos (sq_nonneg _) hε
  have h := specialUnitaryPolynomial_entropy_le_fisher b (d + d) hN (g ε) hp
  have hi : (∫ U, specialUnitaryGamma b (g ε).val (g ε).val U / (g ε).val U
      ∂specialUnitaryHaar n) ≤
      4 * (∫ U, specialUnitaryGamma b f.val f.val U ∂specialUnitaryHaar n) := by
    rw [← integral_const_mul]
    apply integral_mono
      (specialUnitary_integrable_fisher b (g ε).val.contMDiff (fun U => ne_of_gt (hp U)))
      ((specialUnitary_integrable_of_continuous
        (specialUnitaryGamma_contMDiff b f.val.contMDiff f.val.contMDiff).continuous).const_mul 4)
    intro U
    rw [hg ε]
    exact specialUnitary_fisher_sq_add_const_le b f.val.contMDiff hε U
  have hcN : 0 ≤ 1 / (Fintype.card n : ℝ) := by positivity
  have h' := h.trans (mul_le_mul_of_nonneg_left hi hcN)
  convert h' using 1
  ring

end LogSobolev
