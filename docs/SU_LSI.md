# SU(N) LSI: current proof boundary

**The SU(N) LSI is not yet proved, even for smooth functions.**
The exact remaining target, with the existing definitions, is:

```lean
open LogSobolev MeasureTheory
open scoped NNReal Matrix.Norms.Frobenius

-- An unproved goal, not a declaration in the library:
∀ N : ℕ, 2 ≤ N →
  MetricLSI (specialUnitaryHaar (Fin N)) (2 / (N : ℝ≥0))
```

This asks for entropy coefficient `4/N`, the existing normalized Haar measure
on `Matrix.specialUnitaryGroup (Fin N) ℂ`, and the local metric slope of every
locally Lipschitz real function. No alternative energy or measure is substituted.

## Algebraic steps now proved

* `Unitary/SpecialUnitaryAlgebra.lean` defines `specialUnitaryLieAlgebra` as
  a real `LieSubalgebra` of complex matrices with `star A = -A` and `trace A = 0`.
  Closure under real scalar multiplication and the associative commutator is
  proved. This has **not** been identified with a manifold tangent space.
* `negTracePair_lie` proves invariance of `negTracePair A B = -Re Tr(A B)`.
  `negTracePair_self` proves that its diagonal equals the unnormalized
  Frobenius norm squared on skew-Hermitian matrices. Positive definiteness on
  the traceless skew-Hermitian subalgebra is proved.
* `Unitary/MatrixCasimir.lean:sum_matrixUnits_double_lie` proves, over any
  commutative ring and finite matrix index type, with `Eij` the matrix units:

  `Σᵢⱼ [Eij, [Eji, A]] = 2N A − 2 Tr(A) I`.

* `Unitary/SpecialUnitaryCasimir.lean:specialUnitary_commutator_energy`
  combines that identity with the trace pairing and proves:

  `Σᵢⱼ ‖[Eij, A]‖²_HS = 2N ‖A‖²_HS`

  for every traceless skew-Hermitian matrix A. The statement uses the
  Frobenius scoped metric instances, not the default matrix norm.

Independent examples check the coefficient in dimension three and the
nonzero element `diag(i, -i)` in dimension two, including its norm squared `2`.

## Curve geometry now proved

`Unitary/DeterminantDerivative.lean:hasDerivAt_det_at_one` proves that the
matrix determinant derivative at identity is the trace of the velocity.
`Unitary/SpecialUnitaryCurves.lean:det_exp_smul_eq_one_of_trace_zero` then proves
`det(exp(t A)) = 1` for every traceless complex matrix and real t, by the
exponential group law and vanishing derivative.

`mem_specialUnitaryLieAlgebra_iff_curve_velocity` characterizes the algebra
exactly as derivatives at identity of curves in the actual matrix SU group.
Its reverse construction is `specialUnitaryExpCurve`.
`specialUnitaryExpCurve_speed` gives constant speed `‖A‖_HS`, and
`specialUnitaryExpCurve_lipschitz` gives the corresponding global Lipschitz bound.
`specialUnitary_curve_velocity_leftTranslate` and
`specialUnitary_velocity_leftTranslate_norm` prove that translating arbitrary
curve velocities to identity puts them in this algebra and preserves their norm.

These statements use the unnormalized Frobenius norm throughout. They identify
curve velocities without claiming a manifold atlas or Levi-Civita connection.
Independent examples test arbitrary algebra elements and the determinant-one
exponential of the non-skew trace-zero matrix `diag(1, -1)`.

## Inner product, adjoint action, and real contraction

`Unitary/SpecialUnitaryInner.lean` installs the real inner product
`inner A B = -Re Tr(A B)` on the special unitary Lie algebra, with a proved
compatibility equation for the existing Frobenius norm. Its finite-dimensional
instance is inherited from the actual matrix submodule.
`specialUnitary_ad_skew` proves skew-symmetry of the infinitesimal adjoint action.

`Unitary/SpecialUnitaryAdjoint.lean` constructs `specialUnitaryAdjointIsometry`:
conjugation by any actual unitary matrix is a real linear isometric equivalence
of this algebra. It preserves the bracket and inner product.
`specialUnitaryAdjoint_exp_derivative` identifies the derivative of conjugation
along an actual SU exponential curve with the matrix commutator.

`Unitary/SpecialUnitaryKilling.lean:specialUnitary_killing_self` proves, for
**any real orthonormal basis** b of this algebra:

`Killing(A,A) = − Σᵢ ‖[A,bᵢ]‖²_HS`.

This uses Mathlib's Killing form (the trace of the composed adjoint maps).
Basis independence and nonpositivity are proved, including for the standard
orthonormal basis supplied by the finite-dimensional inner-product structure.

## Exact Killing coefficient now proved

`Unitary/SpecialUnitaryKillingConstant.lean` closes the real contraction calculation:

* `specialUnitary_killing_self_eq` proves `Killing(A,A) = −2N ‖A‖²_HS`.
* `specialUnitary_killing_eq_inner` proves the full bilinear identity
  `Killing(A,B) = −2N inner(A,B)`.
* `specialUnitary_orthonormal_commutator_energy` proves
  `Σᵢ ‖[A,bᵢ]‖²_HS = 2N ‖A‖²_HS` for every real orthonormal basis b.

These are unconditional results for the actual traceless skew-Hermitian
matrix Lie algebra, for every finite index type, including empty and singleton
indices. No basis or curvature formula is assumed in their proofs.

`Unitary/MatrixAdjointTrace.lean:matrix_real_trace_ad_sq` computes the trace
on the full real vector space of complex matrices as `−4N ‖A‖²_HS`.
`Unitary/MatrixRealForm.lean:matrix_real_trace_eq_twice_skew` uses Mathlib's
`StarModule.decomposeProdAdjoint` and multiplication by i to show that a
complex-linear star-commuting operator has full real trace twice its trace on
the skew-adjoint subspace. Finally, commutators have traceless range, so
`LinearMap.trace_restrict_eq_of_forall_mem` identifies that restricted trace
with the actual Killing form of su. Thus the complex matrix-unit calculation
is now connected to the real orthonormal contraction by proved trace identities.

An independent example constructs `diag(i,−i)` in su(2) and proves its Killing
square is `−8`; another checks the real-basis coefficient `6` in dimension three.

For mathematical comparison, [Alexandrino–Bettiol, Chapter 2, Exercise 2.50 and
Remark 2.34](https://www.lehman.edu/faculty/rbettiol/old_teaching/661files/Chap2.pdf)
give the SU Killing normalization and the bi-invariant Ricci relation. The
latter is still a geometric obligation here; the reference is not a Lean axiom.

## What these identities do not prove

The real orthonormal contraction and its exact dimension factor are now proved.
Interpreting one quarter of this contraction as Ricci curvature still requires
the manifold tangent identification and the Levi-Civita/curvature calculation
for the actual bi-invariant metric. No algebraic expression has been defined
as the Ricci tensor to bypass that obligation.

The inspected Mathlib checkout supplies general Lie-group and Riemannian
interfaces, but no SU Lie-group instance or curvature-to-LSI theorem applicable
here was found. No such result has been added as a hypothesis disguised as an
instance. The audited `markov-semigroups` class still assumes the entropy decay
needed for its abstract LSI implication and cannot supply this missing proof.

## Remaining route to the theorem

1. Upgrade the proved curve-velocity characterization to a manifold tangent
   identification for the actual matrix SU group, and construct the Hilbert–Schmidt bi-invariant
   Riemannian metric. Prove the geometric Ricci formula `Ric = −¼ Killing`;
   the now-proved Killing coefficient then yields the normalization `N/2`.
2. Prove an applicable curvature-to-LSI criterion. A diffusion route needs a
   constructed heat semigroup, invariant probability identified with Haar,
   entropy dissipation, the gradient/Fisher-information estimate, and convergence
   to equilibrium. None of those analytic estimates is supplied by the Casimir
   computation.
3. Obtain the locally Lipschitz formulation, including any approximation and
   identification of the gradient energy with local metric slopes required by
   the analytic proof.
4. Transfer from the intrinsic metric to the Hilbert–Schmidt metric by proving
   the distance comparison and applying the existing Lipschitz transport API.

The geodesic-LSI-to-Hilbert–Schmidt route is the one cited in the
[Meckes–Meckes appendix, proof of Theorem 15](https://arxiv.org/pdf/1210.2681).
Its citation of Bakry–Émery is a mathematical reference, not an imported Lean
proof. The final bottleneck remains geometric and analytic, not an assembly
or constant-arithmetic problem.

## Verification

Proof commits: `0f05569` (algebra), `339112a` (curves), and `5bf0ed6`
(inner product, adjoint isometry, and real Killing contraction), followed by
`5c6ebdb` (exact Killing coefficient and real orthonormal energy).
`lake build` and the independent `Examples.lean`
compilation pass. The recursive `Audit.lean` check passes for all 306 project
declarations, accepting only `propext`, `Classical.choice`, and `Quot.sound`.
It prints the fully elaborated commutator-energy, curve-velocity, and
exponential-speed, conjugation-derivative, and Killing-contraction, exact-coefficient, and real-orthonormal-energy theorems, exposes the Frobenius instances, and inspects the
Lie-algebra, trace-pairing, exponential-curve, and inner-product definitions.
The full output is in [axiom-audit.txt](axiom-audit.txt). These checks certify
the algebraic and curve results above, not an SU(N) LSI theorem.
