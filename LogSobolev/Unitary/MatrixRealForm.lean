import LogSobolev.Unitary.MatrixAdjointTrace

/-! # The skew-adjoint real form of complex matrices

A complex-linear operator commuting with adjoint acts in the same way on the
self-adjoint and skew-adjoint real summands. Its full real trace is therefore
twice its trace on the skew-adjoint real form.
-/

open Matrix

namespace LogSobolev

variable {n : Type*} [Fintype n]

instance matrixSkewFiniteDimensional :
    FiniteDimensional ℝ (skewAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (skewAdjoint.submodule ℝ (Matrix n n ℂ)))

/-- Multiplication by i identifies the two real adjoint eigenspaces. -/
noncomputable def matrixSelfToSkew :
    selfAdjoint (Matrix n n ℂ) ≃ₗ[ℝ] skewAdjoint (Matrix n n ℂ) where
  toFun A := ⟨Complex.I • A.val, A.prop.smul_mem_skewAdjoint (by
    change star Complex.I = -Complex.I
    simp)⟩
  invFun A := ⟨(-Complex.I) • A.val, isSelfAdjoint_smul_of_mem_skewAdjoint (by
    change star (-Complex.I) = -(-Complex.I)
    simp) A.prop⟩
  left_inv A := by
    apply Subtype.ext
    change (-Complex.I) • (Complex.I • A.val) = A.val
    simp [smul_smul]
  right_inv A := by
    apply Subtype.ext
    change Complex.I • ((-Complex.I) • A.val) = A.val
    simp [smul_smul]
  map_add' A B := by apply Subtype.ext; exact smul_add _ _ _
  map_smul' r A := by apply Subtype.ext; exact smul_comm _ _ _

/-- The full matrix space as two copies of its real skew-adjoint part. -/
noncomputable def matrixSkewDecompose :
    Matrix n n ℂ ≃ₗ[ℝ] skewAdjoint (Matrix n n ℂ) × skewAdjoint (Matrix n n ℂ) :=
  (StarModule.decomposeProdAdjoint ℝ (Matrix n n ℂ)).trans
    (matrixSelfToSkew.prodCongr (LinearEquiv.refl ℝ _))

/-- Restrict a complex-linear, adjoint-commuting operator to skew-adjoint matrices. -/
noncomputable def matrixSkewMap (f : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hf : ∀ X, f (star X) = star (f X)) :
    skewAdjoint (Matrix n n ℂ) →ₗ[ℝ] skewAdjoint (Matrix n n ℂ) :=
  (f.restrictScalars ℝ).restrict (p := skewAdjoint.submodule ℝ (Matrix n n ℂ))
    (q := skewAdjoint.submodule ℝ (Matrix n n ℂ)) (by
    intro X hX
    change star (f X) = -(f X)
    change star X = -X at hX
    rw [← hf, hX, map_neg])

/-- Complex linearity makes both real summands carry the same operator. -/
theorem matrixSkewDecompose_intertwines (f : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hf : ∀ X, f (star X) = star (f X)) (X : Matrix n n ℂ) :
    matrixSkewDecompose (f X) =
      (matrixSkewMap f hf (matrixSkewDecompose X).1,
       matrixSkewMap f hf (matrixSkewDecompose X).2) := by
  apply Prod.ext <;> apply Subtype.ext
  · change Complex.I • ((⅟(2 : ℝ)) • (f X + star (f X))) =
      f (Complex.I • ((⅟(2 : ℝ)) • (X + star X)))
    simp [← hf]
  · change (⅟(2 : ℝ)) • (f X - star (f X)) =
      f ((⅟(2 : ℝ)) • (X - star X))
    simp [← hf]

/-- The full real trace is twice the trace on the real skew-adjoint summand. -/
theorem matrix_real_trace_eq_twice_skew (f : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hf : ∀ X, f (star X) = star (f X)) :
    LinearMap.trace ℝ (Matrix n n ℂ) (f.restrictScalars ℝ) =
      2 * LinearMap.trace ℝ (skewAdjoint (Matrix n n ℂ)) (matrixSkewMap f hf) := by
  let e := matrixSkewDecompose (n := n)
  have he : e.conj (f.restrictScalars ℝ) =
      (matrixSkewMap f hf).prodMap (matrixSkewMap f hf) := by
    apply LinearMap.ext
    intro X
    have h := matrixSkewDecompose_intertwines f hf (e.symm X)
    change e (f (e.symm X)) =
      (matrixSkewMap f hf (e (e.symm X)).1, matrixSkewMap f hf (e (e.symm X)).2) at h
    rw [e.apply_symm_apply] at h
    exact h
  rw [← LinearMap.trace_conj' (f.restrictScalars ℝ) e, he, LinearMap.trace_prodMap', two_mul]

end LogSobolev
