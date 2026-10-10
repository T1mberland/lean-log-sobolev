import LogSobolev.Geometry.DerivationSubmodulePowers
import LogSobolev.Unitary.SpecialUnitaryLinearHeat
import LogSobolev.Unitary.SpecialUnitaryOperatorAlgebra

/-! # Finite-dimensional polynomial spaces on the actual SU group

The affine matrix observables form a finite-dimensional submodule of actual
smooth SU functions. Its `d`th submodule power consists of finite sums of
products of `d` affine observables, so constants allow lower degrees as well.
The invariant derivatives preserve these spaces by the verified Leibniz rule;
therefore the actual sum-of-squares generator preserves them too.
-/

open Matrix
open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual invariant derivative, bundled as a derivation of smooth functions. -/
noncomputable def specialUnitarySmoothDerivation (A : specialUnitaryLieAlgebra (n := n)) :
    Derivation ℝ (specialUnitarySmoothFunctions n) (specialUnitarySmoothFunctions n) where
  toLinearMap := specialUnitaryDerivEnd A
  map_one_eq_zero' := by
    ext U
    change specialUnitaryDeriv A (fun _ => (1 : ℝ)) U = 0
    simp [specialUnitaryDeriv]
  leibniz' f g := by
    ext U
    exact congrFun (specialUnitaryDeriv_mul A f.contMDiff g.contMDiff) U

/-- Affine real matrix observables, as actual smooth functions on SU. -/
noncomputable def specialUnitaryAffineMap :
    (ℝ × (Matrix n n ℂ →L[ℝ] ℝ)) →ₗ[ℝ] specialUnitarySmoothFunctions n where
  toFun p := ⟨fun U => p.1 + p.2 U.val,
    contMDiff_const.add (p.2.contMDiff.comp specialUnitary_val_contMDiff)⟩
  map_add' p q := by
    ext U
    change p.1 + q.1 + (p.2 U.val + q.2 U.val) = (p.1 + p.2 U.val) + (q.1 + q.2 U.val)
    ring
  map_smul' r p := by
    ext U
    change r * p.1 + r * p.2 U.val = r * (p.1 + p.2 U.val)
    ring

/-- The finite-dimensional space of affine matrix observables on SU. -/
noncomputable def specialUnitaryAffineSpace : Submodule ℝ (specialUnitarySmoothFunctions n) :=
  (specialUnitaryAffineMap (n := n)).range

/-- Polynomial observables of degree at most `d`, represented directly as smooth functions.
Mathlib's submodule product takes the linear span of products, so no formal
polynomial quotient or chosen coordinate system is introduced. -/
noncomputable def specialUnitaryPolynomialSpace (d : ℕ) :
    Submodule ℝ (specialUnitarySmoothFunctions n) := specialUnitaryAffineSpace ^ d

/-- Affine matrix observables are finitely generated as a real vector space. -/
theorem specialUnitaryAffineSpace_fg : (specialUnitaryAffineSpace (n := n)).FG :=
  Submodule.fg_range specialUnitaryAffineMap

instance specialUnitaryPolynomialSpace_finite (d : ℕ) :
    Module.Finite ℝ (specialUnitaryPolynomialSpace (n := n) d) :=
  Module.Finite.of_fg (specialUnitaryAffineSpace_fg.pow d)

/-- Constants lie in the affine-observable space. -/
theorem one_mem_specialUnitaryAffineSpace :
    (1 : specialUnitarySmoothFunctions n) ∈ specialUnitaryAffineSpace := by
  refine ⟨(1, 0), ?_⟩
  ext U
  simp [specialUnitaryAffineMap]

/-- An actual invariant derivative preserves affine matrix observables. -/
theorem specialUnitaryDerivEnd_mem_affine
    (A : specialUnitaryLieAlgebra (n := n)) {f : specialUnitarySmoothFunctions n}
    (hf : f ∈ specialUnitaryAffineSpace) : specialUnitaryDerivEnd A f ∈ specialUnitaryAffineSpace := by
  obtain ⟨⟨c, l⟩, rfl⟩ := hf
  let lA := l.comp ((ContinuousLinearMap.mul ℝ (Matrix n n ℂ)).flip A.val)
  refine ⟨(0, lA), ?_⟩
  ext U
  change 0 + lA U.val = specialUnitaryDeriv A (fun V => c + l V.val) U
  rw [specialUnitaryDeriv_affine, zero_add]
  rfl

/-- Invariant differentiation preserves every finite-degree polynomial space. -/
theorem specialUnitaryDerivEnd_mem_polynomial
    (A : specialUnitaryLieAlgebra (n := n)) (d : ℕ) {f : specialUnitarySmoothFunctions n}
    (hf : f ∈ specialUnitaryPolynomialSpace d) :
    specialUnitaryDerivEnd A f ∈ specialUnitaryPolynomialSpace d :=
  derivation_mem_submodule_pow (specialUnitarySmoothDerivation A)
    (fun _ h => specialUnitaryDerivEnd_mem_affine A h) d hf

/-- The bundled actual sum-of-squares generator. -/
noncomputable def specialUnitaryLaplacianEnd {ι : Type*} [Fintype ι]
    (b : ι → specialUnitaryLieAlgebra (n := n)) : Module.End ℝ (specialUnitarySmoothFunctions n) :=
  ∑ i, specialUnitaryDerivEnd (b i) * specialUnitaryDerivEnd (b i)

/-- The bundled endomorphism agrees with the already-constructed differential operator. -/
theorem specialUnitaryLaplacianEnd_apply {ι : Type*} [Fintype ι]
    (b : ι → specialUnitaryLieAlgebra (n := n)) (f : specialUnitarySmoothFunctions n)
    (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryLaplacianEnd b f U = specialUnitaryLaplacian b f U := by
  simp only [specialUnitaryLaplacianEnd, LinearMap.sum_apply]
  change (∑ i, specialUnitaryDerivEnd (b i) (specialUnitaryDerivEnd (b i) f)) U = _
  exact map_sum (ContMDiffMap.evalRingHom U) _ Finset.univ

/-- The actual generator preserves every finite-dimensional polynomial space. -/
theorem specialUnitaryLaplacianEnd_mem_polynomial {ι : Type*} [Fintype ι]
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ) {f : specialUnitarySmoothFunctions n}
    (hf : f ∈ specialUnitaryPolynomialSpace d) :
    specialUnitaryLaplacianEnd b f ∈ specialUnitaryPolynomialSpace d := by
  simp only [specialUnitaryLaplacianEnd, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i _ => specialUnitaryDerivEnd_mem_polynomial (b i) d
    (specialUnitaryDerivEnd_mem_polynomial (b i) d hf)

/-- Increasing the degree enlarges the polynomial-observable space. -/
theorem specialUnitaryPolynomialSpace_mono : Monotone (specialUnitaryPolynomialSpace (n := n)) := by
  apply monotone_nat_of_le_succ
  intro d f hf
  change f ∈ specialUnitaryAffineSpace ^ (d + 1)
  rw [pow_succ (specialUnitaryAffineSpace (n := n)) d]
  simpa only [mul_one] using Submodule.mul_mem_mul hf one_mem_specialUnitaryAffineSpace

/-- Products add degree bounds, using Mathlib's actual submodule multiplication. -/
theorem specialUnitaryPolynomialSpace_mul_mem {d e : ℕ}
    {f g : specialUnitarySmoothFunctions n}
    (hf : f ∈ specialUnitaryPolynomialSpace d) (hg : g ∈ specialUnitaryPolynomialSpace e) :
    f * g ∈ specialUnitaryPolynomialSpace (d + e) := by
  change f * g ∈ specialUnitaryAffineSpace ^ (d + e)
  rw [pow_add (specialUnitaryAffineSpace (n := n)) d e]
  exact Submodule.mul_mem_mul hf hg

/-- Restrict the actual generator to a finite-dimensional polynomial-observable space. -/
noncomputable def specialUnitaryPolynomialLaplacian {ι : Type*} [Fintype ι]
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ) :
    Module.End ℝ (specialUnitaryPolynomialSpace (n := n) d) :=
  (specialUnitaryLaplacianEnd b).restrict (fun _ h => specialUnitaryLaplacianEnd_mem_polynomial b d h)

/-- The restricted generator still acts by the original SU Laplacian, pointwise. -/
theorem specialUnitaryPolynomialLaplacian_apply {ι : Type*} [Fintype ι]
    (b : ι → specialUnitaryLieAlgebra (n := n)) (d : ℕ)
    (f : specialUnitaryPolynomialSpace (n := n) d) (U : Matrix.specialUnitaryGroup n ℂ) :
    (specialUnitaryPolynomialLaplacian b d f).val U = specialUnitaryLaplacian b f.val U :=
  specialUnitaryLaplacianEnd_apply b f.val U

end LogSobolev
