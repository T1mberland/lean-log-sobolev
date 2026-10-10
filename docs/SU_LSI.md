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
  proved. For the constructed atlas, manifold tangent coordinates now map to
  ambient velocities by the proved inclusion derivative `A ↦ U A`.
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

## Actual local exponential coordinates now proved

`Unitary/MatrixExpDeterminant.lean:det_matrix_exp` proves
`det(exp A) = Complex.exp(trace A)` for **every** complex matrix, by the
determinant derivative and an integrating factor. The earlier trace-zero
exponential theorem is now a specialization of this result.

`Unitary/MatrixLocalExponential.lean` applies Mathlib's inverse function theorem
to matrix exponential, whose strict derivative at zero is the identity.
`matrixExpLocalHomeomorph` is a genuine ambient local homeomorphism, with zero
in its source and identity in its target. Its inverse has identity strict
derivative and every order of smoothness at identity.

`exists_specialUnitary_exp_neighborhood` proves that on a sufficiently small
open Frobenius neighborhood of zero, exponential is injective and
`exp A ∈ SU` is equivalent to `A ∈ su`. For the unitary condition it uses
adjoint compatibility, exponential inverses, and local injectivity; for the
determinant condition it uses the proved determinant identity and scalar
exponential injectivity in a strip around zero.

`Unitary/SpecialUnitaryLocalCoordinates.lean:exists_specialUnitary_exp_homeomorph`
then constructs a homeomorphism between an **open neighborhood of zero in su**
and an **open neighborhood of identity in the actual matrix SU group**, whose
forward map is matrix exponential. An independent example extracts generators
for every SU(2) element in this open neighborhood. This establishes genuine
local coordinates, without assuming an SU manifold instance.

The later smooth-atlas construction below uses these coordinates. This local
homeomorphism result alone does not identify the tangent metric or connection.

## Smooth atlas now proved

`Unitary/SpecialUnitaryAnalyticNeighborhood.lean` shrinks the ambient chart to
an open neighborhood where its inverse is analytic at every target point.
The SU/su correspondence is preserved under this restriction.

`Unitary/SpecialUnitaryChart.lean:specialUnitaryExpChart` packages the actual
exponential/logarithm pair as an `OpenPartialHomeomorph` from su to SU.
Its source contains zero and its target contains identity. Translating its
inverse by group multiplication defines `specialUnitaryChartAt U` with U in
its source, for every actual SU element U. `specialUnitaryChartedSpace` installs
this covering atlas on the **existing** matrix-group topology.

`Unitary/SpecialUnitaryManifold.lean:specialUnitaryIsManifold` proves

```lean
IsManifold 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) ∞
  (Matrix.specialUnitaryGroup n ℂ)
```

The proof verifies every atlas transition on its actual source. A transition
is the restriction of `A ↦ projection(log(V⁻¹ U exp A))`, where `projection`
is a proved continuous linear left inverse of the su inclusion. This projection
is only a device for extending the coordinate expression into the model space;
it is not asserted to be an orthogonal or Riemannian projection. On overlaps,
the logarithm already lies in su and the projection fixes it.

The smooth group operations are now proved in
`Unitary/SpecialUnitaryLieGroup.lean`. The instance `specialUnitaryLieGroup`
uses the original matrix type and the previously verified atlas. The ambient
criterion `contMDiff_specialUnitary_iff` proves smoothness into SU exactly when
the ambient matrix map is smooth. Matrix multiplication, real linear adjoint,
and the matrix exponential then give smooth multiplication, inversion, and
exponential without additional assumptions.

`Unitary/SpecialUnitaryTangent.lean:specialUnitary_val_hasMFDerivAt` identifies
the actual manifold derivative of inclusion at `U` with `A ↦ U A`.
`specialUnitary_mfderiv_val_norm` proves equality of its ambient Frobenius norm
and the su model-coordinate norm. Norms are specified explicitly; no arbitrary
tangent-space norm or Riemannian structure is assumed. The smooth Riemannian
metric, connection/curvature formula, and analytic LSI argument remain open.

## Invariant fields and actual differential operators

`Unitary/SpecialUnitaryInvariantFields.lean` proves the derivative of left
multiplication is the identity in the translated tangent coordinates. In
particular, Mathlib's `mulInvariantVectorField A` has ambient velocity `U A`,
proved in `specialUnitary_mulInvariantVectorField_val`. These are preferred
coordinates depending on the base point; their constancy does not mean the
vector fields commute.

`Unitary/SpecialUnitarySmoothExtension.lean` constructs a local ambient retraction
using the analytic logarithm and the proved linear retraction onto su.
`specialUnitary_exists_local_smooth_extension` shows that every smooth SU test
admits a smooth ambient extension near each point. It assumes no extension
hypothesis and does not assert a globally smooth logarithm or retraction.

`Unitary/SpecialUnitaryDifferentialOperators.lean` defines `specialUnitaryDeriv`
using the actual `mfderiv`, not an arbitrary operator supplied by a class.
`specialUnitaryDeriv_contMDiff` proves it preserves smoothness, and
`specialUnitaryDeriv_commutator` proves, for every smooth SU test,

`D_A(D_B f)(U) − D_B(D_A f)(U) = D_[A,B] f(U)`.

The proof uses the verified local extension and the generic normed-algebra
`Geometry/AlgebraVectorFields.lean:rightMulDeriv_commutator`. The latter uses
Mathlib's Lie bracket and symmetry of second derivatives. The result is not
restricted to ambient polynomial or globally extendible tests. An independent
SU(2) example uses `A = diag(i,−i)` and `B = [[0,1],[-1,0]]`; their operator
commutator on the matrix inclusion has `(0,1)` entry `2i` at identity.

This proves the differential-operator commutator relation. Equality between
Mathlib's `GroupLieAlgebra` bracket and the algebraic matrix bracket has not
itself been packaged as a theorem. No Γ₂ bound, heat semigroup, or LSI
is asserted by these modules; the subsequent generator module is described below.

## Second-order energy and the constructed generator

`Unitary/SpecialUnitarySecondOrder.lean:specialUnitary_dual_commutator_energy`
uses the Riesz representation theorem and the exact Killing contraction to prove
`Σᵢⱼ (ℓ([bᵢ,bⱼ]))² = 2N Σᵢ (ℓ(bᵢ))²` for every continuous real linear functional
on su and every real HS orthonormal basis. Applied to the actual manifold
differential, it gives `specialUnitaryDeriv_commutator_energy`.

`specialUnitary_second_derivative_energy_lower_bound` then proves

`(N/2) Σᵢ (Dᵢ f(U))² ≤ Σᵢⱼ (Dᵢ Dⱼ f(U))²`

for every real function smooth at `U`. The proof uses the already-proved operator
commutator and `Geometry/SecondOrderArray.lean:sum_sq_sub_transpose_le`, which
bounds the squared antisymmetric part of an array by four times its squared norm.
The `N/2` coefficient is thus a proved estimate on actual derivatives.

`Unitary/SpecialUnitaryGenerator.lean` defines `specialUnitaryLaplacian` as
`L = Σᵢ Dᵢ²`, for a supplied finite family of directions, and proves it preserves
smoothness. `specialUnitaryGamma` is defined by the actual generator expression
`(L(fg) − f Lg − g Lf)/2`, not by declaring an energy formula.
`specialUnitaryGamma_eq` proves this equals `Σᵢ (Dᵢ f)(Dᵢ g)` via two applications
of the verified product rule. Nonnegativity on equal smooth tests follows.
An orthonormal family is supplied when using the HS metric normalization.

Independent examples instantiate an existing real orthonormal basis of su(2)
for the second-order estimate, and verify that the generator-defined energy is
`1` at identity for `f(U) = Im(U₀₀)` and the single direction `diag(i,−i)`.
The latter is a nonzero one-direction test, not a claim that one direction is a
full orthonormal frame.

These results supply the second-order estimate. The subsequent operator modules
below now identify it with Γ₂. No heat semigroup has been introduced by assumption.

## Verified generator commutation and Γ₂ bound

`Unitary/SpecialUnitaryOperatorAlgebra.lean` packages the actual invariant
derivatives as real linear endomorphisms of Mathlib's space of smooth SU
functions. Linearity in the direction and the commutator relation are proved
from the manifold derivative; no abstract representation is assumed.

`Geometry/CasimirCommutation.lean:sum_squares_commute_of_skew_coefficients`
is a general algebraic theorem: if commutation with an element acts on a finite
family through skew coefficients, its sum of squares commutes with that element.
`Unitary/SpecialUnitaryGeneratorCommutation.lean` verifies these coefficients
using the actual orthonormal su basis and the proved ad-invariant HS pairing.
`specialUnitaryLaplacian_deriv` therefore proves `L(D_A f) = D_A(L f)` for every
smooth SU test.

`Unitary/SpecialUnitaryGammaTwo.lean` defines the iterated carré du champ by

`Γ₂(f) = (L Γ(f,f) − 2 Γ(f,Lf))/2`.

It then proves `specialUnitaryGammaTwo_eq`:

`Γ₂(f)(U) = Σᵢⱼ (Dᵢ Dⱼ f(U))²`,

and `specialUnitaryGammaTwo_lower_bound`:

`(N/2) Γ(f,f)(U) ≤ Γ₂(f)(U)`.

These theorems hold for every smooth real test on the actual SU manifold and
every real HS orthonormal basis. The coefficient uses the matrix size, not the
Lie algebra dimension. Γ₂ is not defined as the second-derivative sum; their
equality is proved using generator commutation and product rules. An independent
SU(3) example expands the bound into `3 Γ ≤ L Γ − 2 Γ(f,Lf)`, checking both factors.

This closes the differential Γ₂ estimate. It does **not** prove entropy decay,
a heat-semigroup existence theorem, or an LSI, even on smooth tests.

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
identifying the geometric Lie bracket with the matrix commutator and proving
the Levi-Civita/curvature calculation
for the actual bi-invariant metric. No algebraic expression has been defined
as the Ricci tensor to bypass that obligation.

The inspected Mathlib checkout supplies general Lie-group and Riemannian
interfaces, but no SU Lie-group instance or curvature-to-LSI theorem applicable
here was found. No such result has been added as a hypothesis disguised as an
instance. The audited `markov-semigroups` class still assumes the entropy decay
needed for its abstract LSI implication and cannot supply this missing proof.

## Haar integration now proved

`Unitary/SpecialUnitaryFlow.lean:specialUnitary_hasDerivAt_mul_exp` identifies
ordinary differentiation of `f(U exp(tA))` with the actual invariant derivative
at `U exp(tA)`. It uses the proved local smooth ambient extension and the matrix
exponential derivative; no flow derivative is assumed.

`Unitary/SpecialUnitaryHaarCalculus.lean` proves uniqueness and right invariance
of the existing normalized SU Haar measure. Differentiation under the integral,
with compactness bounding the derivative, gives
`specialUnitary_integral_deriv_eq_zero`: `∫ D_A f = 0`.
The product rule gives `specialUnitary_integral_mul_deriv` and
`specialUnitary_integral_mul_laplacian`: `∫ f Lg = −∫ Γ(f,g)`.
Smoothness and compactness establish all integrability requirements. The
actual generator therefore has zero integral, is symmetric, and has nonpositive
quadratic form on smooth real tests.

`Unitary/SpecialUnitaryIntegratedGammaTwo.lean` then proves
`specialUnitary_integral_gammaTwo`: `∫ Γ₂(f) = ∫ (Lf)²`, and
`specialUnitary_integrated_gammaTwo_lower_bound`:

`(N/2) ∫ Γ(f,f) ≤ ∫ (Lf)²`.

These statements use the existing normalized Haar measure and, for the last
estimate, a real Hilbert–Schmidt orthonormal basis. This is a generator
coercivity estimate, not yet a Poincaré or entropy inequality. No spectral or
heat-semigroup existence assumption is introduced.

## Remaining route to the theorem

The sum-of-squares route now has its exact differential estimate
`Γ₂ ≥ (N/2) Γ`. The remaining central task is analytic: construct the diffusion
for this operator and prove the entropy argument, with invariant measure equal
to the already-defined normalized Haar probability. Haar integration by parts
is now proved. Required steps include semigroup existence and regularity, entropy dissipation,
the Fisher-information estimate derived from the proved Γ₂ bound, and convergence
to constants. Connectedness/ergodicity needed for this convergence must be proved;
it is not supplied by an abstract class or inferred from Γ₂ alone.

A precise **unproved smooth intermediate goal**, for `N ≥ 2`, a real orthonormal
basis `b` of su(N), and `f` smooth on SU(N), is

```lean
entropy (specialUnitaryHaar (Fin N)) (fun U => f U ^ 2) ≤
  (4 / (N : ℝ)) * ∫ U, specialUnitaryGamma b f f U ∂specialUnitaryHaar (Fin N)
```

After that, identify the energy with the local Hilbert–Schmidt metric slope and
prove the extension to all locally Lipschitz functions. These remain proof
obligations, not assumed data. The operator route follows the approach described
in [Rothaus, *Hypercontractivity and the Bakry–Emery criterion for compact Lie
groups*, pp. 361–363](https://www.researchgate.net/publication/243022735_Hypercontractivity_and_the_Bakry-Emery_criterion_for_compact_Lie_groups).
The source is a mathematical reference, not an imported Lean foundation.

The alternative geometric route remains:

1. Use the proved smooth group operations and inclusion derivative to construct
   the Hilbert–Schmidt bi-invariant
   Riemannian metric. For the geometric bracket, reuse Mathlib’s
   `GroupLieAlgebra` and `mulInvariantVectorField` and identify their bracket
   with the matrix commutator; the algebraic subalgebra alone is not that proof.
   Prove the geometric Ricci formula `Ric = −¼ Killing`;
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

The alternative geodesic-LSI-to-Hilbert–Schmidt route is the one cited in the
[Meckes–Meckes appendix, proof of Theorem 15](https://arxiv.org/pdf/1210.2681).
Its citation of Bakry–Émery is a mathematical reference, not an imported Lean
proof. The final bottleneck remains geometric and analytic, not an assembly
or constant-arithmetic problem.

## Verification

Proof commits: `0f05569` (algebra), `339112a` (curves), and `5bf0ed6`
(inner product, adjoint isometry, and real Killing contraction), followed by
`5c6ebdb` (exact Killing coefficient and real orthonormal energy), and
`2387b3e` (determinant identity and actual local exponential coordinates), and
`78fea3b` (smooth translated exponential atlas), and `fc7c4c0` (smooth group
operations, ambient criterion, and exact manifold tangent normalization), and
`e5cfa1d` (invariant fields, local smooth extensions, and smooth directional
operator commutators), and `6cb53ac` (the `N/2` second-derivative estimate and
generator-defined carré du champ), and `eb986ff` (actual operator Casimir
commutation and the exact generator-defined Γ₂ identity and bound), and
`3c059da` (actual Haar integration by parts and integrated Γ₂ coercivity).
`lake build` and the independent `Examples.lean`
compilation pass. The recursive `Audit.lean` check passes for all 482 project
declarations, accepting only `propext`, `Classical.choice`, and `Quot.sound`.
It prints the fully elaborated commutator-energy, curve-velocity, and
exponential-speed, conjugation-derivative, and Killing-contraction, exact-coefficient, and real-orthonormal-energy theorems, exposes the Frobenius instances, and inspects the
Lie-algebra, trace-pairing, exponential-curve, and inner-product definitions.
The full output is in [axiom-audit.txt](axiom-audit.txt). These checks certify
the algebraic, curve, local-coordinate, smooth Lie-group, tangent-derivative,
smooth differential-operator, second-order energy, generator, Γ₂, and Haar
integration results
above, not an SU(N) LSI theorem.
