import LogSobolev.Unitary.SpecialUnitaryPolynomialSpace

/-! # Polynomial pullbacks by ambient linear maps

A real linear matrix map restricting to a self-map of SU preserves polynomial
degree. This includes translations and inversion (conjugate transpose), the
operations needed to express convolution with a polynomial kernel as a
polynomial observable. The proof uses actual function equality and does not
assume any approximation or logarithmic Sobolev inequality.
-/

open Matrix
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Pullback by an ambient real linear map preserving SU preserves degree. -/
theorem specialUnitaryPolynomial_exists_linear_pullback
    (T : Matrix.specialUnitaryGroup n ℂ → Matrix.specialUnitaryGroup n ℂ)
    (L : Matrix n n ℂ →L[ℝ] Matrix n n ℂ)
    (hT : ∀ U, (T U).val = L U.val) (d : ℕ)
    {f : specialUnitarySmoothFunctions n} (hf : f ∈ specialUnitaryPolynomialSpace d) :
    ∃ g : specialUnitaryPolynomialSpace (n := n) d, ∀ U, g.val U = f (T U) := by
  induction d generalizing f with
  | zero =>
      change f ∈ specialUnitaryAffineSpace ^ 0 at hf
      rw [pow_zero (specialUnitaryAffineSpace (n := n))] at hf
      obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hf
      refine ⟨⟨algebraMap ℝ _ r, ?_⟩, fun U => ?_⟩
      · change algebraMap ℝ _ r ∈ specialUnitaryAffineSpace ^ 0
        rw [pow_zero (specialUnitaryAffineSpace (n := n))]
        exact Submodule.mem_one.mpr ⟨r, rfl⟩
      · change (algebraMap ℝ (specialUnitarySmoothFunctions n) r) U =
          (algebraMap ℝ (specialUnitarySmoothFunctions n) r) (T U)
        rw [Algebra.algebraMap_eq_smul_one]
        rfl
  | succ d ih =>
      change f ∈ specialUnitaryAffineSpace ^ (d + 1) at hf
      rw [pow_succ (specialUnitaryAffineSpace (n := n)) d] at hf
      refine Submodule.mul_induction_on hf ?_ ?_
      · intro a ha b hb
        obtain ⟨g, hg⟩ := ih ha
        obtain ⟨⟨c, l⟩, rfl⟩ := hb
        let k := specialUnitaryAffineMap (c, l.comp L)
        have hk : k ∈ specialUnitaryAffineSpace := ⟨(c, l.comp L), rfl⟩
        refine ⟨⟨g.val * k, ?_⟩, fun U => ?_⟩
        · change g.val * k ∈ specialUnitaryAffineSpace ^ (d + 1)
          rw [pow_succ (specialUnitaryAffineSpace (n := n)) d]
          exact Submodule.mul_mem_mul g.prop hk
        · change g.val U * (c + l (L U.val)) = a (T U) * (c + l (T U).val)
          rw [hg, hT]
      · intro a b ha hb
        obtain ⟨ga, hga⟩ := ha
        obtain ⟨gb, hgb⟩ := hb
        refine ⟨ga + gb, fun U => ?_⟩
        change ga.val U + gb.val U = a (T U) + b (T U)
        rw [hga, hgb]

/-- Left translation preserves each polynomial degree bound. -/
theorem specialUnitaryPolynomial_exists_mul_left (V : Matrix.specialUnitaryGroup n ℂ)
    (d : ℕ) (f : specialUnitaryPolynomialSpace (n := n) d) :
    ∃ g : specialUnitaryPolynomialSpace (n := n) d, ∀ U, g.val U = f.val (V * U) :=
  specialUnitaryPolynomial_exists_linear_pullback (fun U => V * U)
    (ContinuousLinearMap.mul ℝ (Matrix n n ℂ) V.val) (fun _ => rfl) d f.prop

/-- Right translation preserves each polynomial degree bound. -/
theorem specialUnitaryPolynomial_exists_mul_right (V : Matrix.specialUnitaryGroup n ℂ)
    (d : ℕ) (f : specialUnitaryPolynomialSpace (n := n) d) :
    ∃ g : specialUnitaryPolynomialSpace (n := n) d, ∀ U, g.val U = f.val (U * V) :=
  specialUnitaryPolynomial_exists_linear_pullback (fun U => U * V)
    ((ContinuousLinearMap.mul ℝ (Matrix n n ℂ)).flip V.val) (fun _ => rfl) d f.prop

/-- Inversion is real linear in the ambient entries on SU, and preserves degree. -/
theorem specialUnitaryPolynomial_exists_inv (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) :
    ∃ g : specialUnitaryPolynomialSpace (n := n) d, ∀ U, g.val U = f.val U⁻¹ :=
  specialUnitaryPolynomial_exists_linear_pullback Inv.inv
    (starL' ℝ : Matrix n n ℂ ≃L[ℝ] Matrix n n ℂ).toContinuousLinearMap
    (fun _ => rfl) d f.prop

/-- For a polynomial convolution kernel, its translate as a function of the
output variable has the same degree bound. -/
theorem specialUnitaryPolynomial_exists_inv_mul (V : Matrix.specialUnitaryGroup n ℂ)
    (d : ℕ) (f : specialUnitaryPolynomialSpace (n := n) d) :
    ∃ g : specialUnitaryPolynomialSpace (n := n) d, ∀ U, g.val U = f.val (U⁻¹ * V) := by
  obtain ⟨g, hg⟩ := specialUnitaryPolynomial_exists_mul_right V d f
  obtain ⟨k, hk⟩ := specialUnitaryPolynomial_exists_inv d g
  exact ⟨k, fun U => (hk U).trans (hg U⁻¹)⟩

end LogSobolev
