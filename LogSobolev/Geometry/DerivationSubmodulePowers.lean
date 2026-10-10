import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Finiteness.Subalgebra

/-! # Derivations preserving polynomial submodule filtrations

If a derivation preserves a submodule of a commutative algebra, it preserves
every power of that submodule. With affine observables as generators, these
powers are finite-degree polynomial spaces. Finite generation of the powers
is supplied by Mathlib's existing `Submodule.FG.pow` theorem.
-/

namespace LogSobolev

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A derivation preserves products of invariant submodules. -/
theorem derivation_mem_submodule_mul (D : Derivation R A A) {M N : Submodule R A}
    (hM : ∀ x ∈ M, D x ∈ M) (hN : ∀ x ∈ N, D x ∈ N)
    {x : A} (hx : x ∈ M * N) : D x ∈ M * N := by
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro a ha b hb
    rw [D.leibniz, smul_eq_mul, smul_eq_mul]
    apply Submodule.add_mem
    · exact Submodule.mul_mem_mul ha (hN b hb)
    · rw [mul_comm b (D a)]
      exact Submodule.mul_mem_mul (hM a ha) hb
  · intro a b ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb

/-- Every power of an invariant submodule is invariant under the derivation. -/
theorem derivation_mem_submodule_pow (D : Derivation R A A) {M : Submodule R A}
    (hM : ∀ x ∈ M, D x ∈ M) (d : ℕ) {x : A} (hx : x ∈ M ^ d) : D x ∈ M ^ d := by
  induction d generalizing x with
  | zero =>
      rw [pow_zero] at hx ⊢
      obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
      rw [D.map_algebraMap]
      exact Submodule.zero_mem _
  | succ d ih =>
      rw [pow_succ] at hx ⊢
      exact derivation_mem_submodule_mul D (fun _ h => ih h) hM hx

end LogSobolev
