# SU(N) logarithmic Sobolev inequality

**The full SU(N) metric LSI is proved for every locally Lipschitz real function
and every positive dimension, including SU(1).**

The public theorem is in `LogSobolev/Unitary/SpecialUnitaryLSI.lean`:

```lean
LogSobolev.specialUnitary_metricLSI
  (hN : 0 < Fintype.card n) :
  MetricLSI (specialUnitaryHaar n) (2 / (Fintype.card n : ℝ≥0))
```

`specialUnitary_entropy_sq_le_of_locallyLipschitz` gives the real form directly:
`Ent(f²) ≤ (4/N) ∫ (localSlope f).toReal²`. Its only function hypothesis is
`LocallyLipschitz f`. The group is Mathlib's actual
`Matrix.specialUnitaryGroup n ℂ`, the measure is normalized Haar probability,
and the metric is the **unnormalized Hilbert–Schmidt metric**. Compact regularity
proves square, log-moment, and slope-energy integrability.

This closes the SU ingredient of the Meckes–Meckes appendix proof. The interval
LSI, L²-product tensorization, and U(1) analytic case are still needed for the
larger U(N) Theorem 15 goal; they are not claimed here.

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
metric and connection/curvature formula are not constructed. The completed LSI
proof below uses the actual sum-of-squares operator instead.

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

## Logarithmic calculus and entropy differentiation now proved

`Unitary/SpecialUnitaryChainRules.lean` proves the actual scalar chain rule
`L(φ ∘ f) = φ′(f) Lf + φ″(f) Γ(f,f)`, with scalar smoothness required only
along the range of `f`. Its logarithmic specializations give
`L log f = Lf/f − Γ(f,f)/f²` and `Γ(log f,log f) = Γ(f,f)/f²`.
The logarithmic Haar identity is
`specialUnitary_integral_log_mul_laplacian`:

`∫ log(f) Lf = −∫ Γ(f,f)/f`.

`Measure/CompactDifferentiation.lean` derives domination on a compact time
interval times a compact space from joint continuity.
`Measure/EntropyDifferentiation.lean:hasDerivAt_entropy_of_compact` proves
entropy differentiation, including the correction for varying total mass.
The family and proposed time derivative are jointly continuous, the family is
positive, and the time-derivative hypothesis is required only on a neighborhood
of the specified time.

`Unitary/SpecialUnitaryEntropyDissipation.lean:specialUnitary_hasDerivAt_entropy`
then proves `d Ent(F_t)/dt = −∫ Γ(F_t,F_t)/F_t` **for a supplied family whose
time derivative at that time is the actual Laplacian**. Integrability and
nonpositivity of this entropy derivative are proved. This is a conditional
statement about a differentiable family, not a construction of a heat solution
and not an assumed entropy-decay axiom. In particular, no backwards heat
solution is required by its local time-derivative hypothesis.

For every positive smooth `f` and real HS orthonormal basis, the same module
proves `specialUnitary_weighted_gammaTwo_log_lower_bound`:

`(N/2) ∫ Γ(f,f)/f ≤ ∫ f Γ₂(log f)`.

This supplies the curvature part of the Fisher-information argument. The
spatial dissipation identity and a conditional time-derivative theorem are now
proved below. Polynomial heat existence, its required regularity, and exponential
Fisher decay, equilibrium, and polynomial LSI are established later in this
report. The final convolution argument below extends to every locally Lipschitz function.

## Fisher dissipation now proved under explicit regularity

`Unitary/SpecialUnitaryFisherIdentity.lean` proves the mixed logarithmic chain
rule and the weighted Haar identity, then
`specialUnitary_fisher_variation_identity`:

`∫ [2 Γ(f,Lf)/f − Γ(f,f) Lf/f²] = −2 ∫ f Γ₂(log f)`.

This spatial identity is unconditional for a smooth nowhere-zero test and any
finite family of directions. It uses the actual constructed operators and
normalized Haar measure. For positive tests and an HS orthonormal basis,
`specialUnitary_fisher_variation_le` bounds this expression by `−N ∫ Γ(f,f)/f`.

`Unitary/SpecialUnitaryFisherDifferentiation.lean` proves
`specialUnitary_hasDerivAt_fisher` by differentiating the integral. Its explicit
hypotheses are joint continuity of `F`, `Q`, `D_i F`, and `D_i Q`; spatial
smoothness; nonvanishing of `F`; and local identities `∂ₜF = Q` and
`∂ₜ(D_i F) = D_i Q`. It does not assume the desired Fisher derivative.
With the additional heat-direction equality `Q_t = L F_t`,
`specialUnitary_hasDerivAt_fisher_of_heat` proves

`I′(t) = −2 ∫ F_t Γ₂(log F_t)`, where `I(t) = ∫ Γ(F_t,F_t)/F_t`.

For positive families, `specialUnitary_fisher_deriv_le` proves `I′(t) ≤ −N I(t)`.
These are **conditional theorems about supplied regular families**. Their
regularity hypotheses are now discharged for the constructed polynomial heat
flow described below. A heat flow on arbitrary smooth functions has not yet
been constructed.
An independent exponential-rescaling example discharges every differentiation
hypothesis for a time-dependent family, without asserting it solves the heat
equation.

## Maximum principle and an actual affine heat construction

`Geometry/SecondDerivativeExtrema.lean` proves the necessary second-derivative
sign at local extrema from Mathlib's derivative test.
`Unitary/SpecialUnitaryMaximumPrinciple.lean` applies it along the actual curves
`U exp(tA)`. It proves vanishing of invariant first derivatives at minima,
nonnegativity of each second invariant derivative there, and
`specialUnitary_laplacian_nonneg_at_min` / `specialUnitary_laplacian_nonpos_at_max`.
These are the actual constructed differential operators, for any finite family
of directions; no abstract positive-generator axiom is used.

`Geometry/CompactEvolutionMaximum.lean:nonneg_of_compact_minimum_principle`
proves positivity preservation on a compact space from the derivative sign at
spatial minima. It minimizes on a compact space-time rectangle and uses a
positive linear time perturbation. No measure structure is needed.
`Unitary/SpecialUnitaryHeatBounds.lean` specializes this to the actual SU heat
equation: `specialUnitary_heat_lower_bound`, `specialUnitary_heat_upper_bound`,
and `specialUnitary_heat_nonneg`. These theorems assume a classical solution
but **derive**, rather than assume, preservation of bounds.

`Unitary/SpecialUnitaryLinearHeat.lean` now constructs actual solutions for
affine matrix observables. For a real continuous linear functional `l` on
matrices, a scalar `c`, and `S = ∑ i, (b i)²`, define

`specialUnitaryLinearHeat b l c t U = c + l(U exp(t S))`.

`specialUnitaryLaplacian_affine` proves `L(c+l(U)) = l(U S)`.
`specialUnitaryLinearHeat_zero` proves the exact initial value, and
`specialUnitaryLinearHeat_hasDerivAt` proves `∂ₜ F_t = L F_t` **without a heat
solution or PDE hypothesis**. Joint continuity and smoothness of every spatial
slice are proved. Initial lower and upper bounds are preserved, and
`specialUnitaryLinearHeat_pos` proves strict positivity at all forward times
from strictly positive affine initial data. An independent SU(2) example uses
the nonconstant positive density `2 + Im(U₀₀)`; an SU(3) example checks the
actual PDE with the canonical real HS orthonormal basis.

## Polynomial heat and integrated Fisher decay

`Geometry/DerivationSubmodulePowers.lean` proves that a derivation preserving a
submodule preserves every power of that submodule. This reuses Mathlib's
submodule products and `Submodule.FG.pow` rather than introducing a formal
polynomial quotient.

`Unitary/SpecialUnitaryPolynomialSpace.lean` defines the affine-observable space
`W` as the range of `(c,l) ↦ (U ↦ c + l(U))` in actual smooth SU functions.
`specialUnitaryPolynomialSpace d = W^d` consists of linear combinations of
products of `d` affine observables; constants allow all lower degrees.
Finite dimensionality, monotonicity in degree, multiplication of degree bounds,
and invariance under every actual `D_A` and the actual generator `L` are proved.

`Unitary/SpecialUnitaryPolynomialNorm.lean` gives these spaces their actual
supremum norm by an injective map into continuous functions on SU. Completeness
and continuity of the restricted generator and invariant derivatives follow
from finite dimensionality. This function-space norm does not change the
Hilbert–Schmidt metric on the group.

`Unitary/SpecialUnitaryPolynomialHeat.lean` constructs `P_t = exp(t L)` on each
space. It proves the initial value, semigroup law, actual heat equation, joint
continuity, preservation of lower and upper bounds, forward strict positivity,
supremum-norm contraction, and conservation of normalized Haar mass.
No supplied solution, positivity, or invariance hypothesis is used.

`Unitary/SpecialUnitaryPolynomialHeatRegularity.lean` derives mixed time/spatial
regularity by composing the vector-valued heat ODE with the continuous actual
invariant derivatives. The forward heat flow is extended constantly before
time zero solely to apply global continuity/positivity integral lemmas; its
heat equation is asserted only at positive times.

`Unitary/SpecialUnitaryPolynomialDissipation.lean` now proves, for **every
strictly positive polynomial observable** and the real unnormalized HS
orthonormal generator:

* `specialUnitaryPolynomialForwardHeat_hasDerivAt_entropy`: `Ent′ = −I`.
* `specialUnitaryPolynomialForwardHeat_hasDerivAt_fisher`:
  `I′ = −2 ∫ (P_t f) Γ₂(log P_t f)`.
* `specialUnitaryPolynomialForwardHeat_fisher_deriv_le`: `I′ ≤ −N I`.
* `specialUnitaryPolynomialForwardHeat_fisher_le_exp`:
  `I(P_t f) ≤ exp(−Nt) I(f)` for every `t ≥ 0`, including zero.

Here `I(g) = ∫ Γ(g,g)/g dHaar`. All heat and mixed-regularity hypotheses of
the earlier conditional theorems are discharged. A reusable integrating-factor
lemma in `Analysis/ExponentialDecay.lean` uses Mathlib's derivative monotonicity
criterion and needs only continuity at the initial endpoint.
Independent examples construct `(2 + Im(U₀₀))²` in degree two on SU(2), prove
strict positivity and an actual invariant derivative equal to four, and check
Haar-mass conservation and Fisher decay at exact rate two.

## Connectedness and the zero-energy kernel

`Geometry/FiniteSpectrumUnitary.lean` reuses Mathlib's selfadjoint argument and
continuous functional calculus. A scalar argument restricted to a finite
spectrum is continuous, even at a branch cut. The theorem
`expUnitary_argSelfAdjoint_of_finite_spectrum` therefore proves that its
selfadjoint exponential is the original unitary. Surjectivity of the continuous
exponential gives `unitary_connectedSpace_of_finite_spectrum`.

`Unitary/UnitaryConnected.lean` applies this to actual complex matrices, reusing
`Matrix.finite_spectrum`. The C⋆ operator norm is used locally to invoke the
functional-calculus API. Mathlib's matrix operator-norm topology is the original
finite matrix topology, so the exported `unitaryConnectedSpace` asserts
connectedness for that topology. It does not install an operator norm on the
LSI development or change its Frobenius metric.

`Unitary/SpecialUnitaryConnected.lean` constructs a continuous retraction
`unitaryToSpecialUnitary i`: multiply row `i` by the conjugate of the determinant.
Unitarity, determinant one, continuity, and the right-inverse identity on SU
are proved. Its surjectivity proves `specialUnitaryConnectedSpace` for every
finite index type; the empty-index singleton case is treated separately.

`Unitary/SpecialUnitaryZeroEnergy.lean` uses full support of actual normalized
Haar measure to turn zero integrated carré du champ into pointwise zero energy.
A real HS orthonormal basis then detects every invariant derivative.
`specialUnitary_eq_mul_exp_of_deriv_eq_zero` proves constancy along actual
exponential curves. The existing local exponential atlas gives local constancy,
and the newly proved connectedness gives global constancy:

* `specialUnitary_eq_mean_of_integral_gamma_eq_zero`: every smooth zero-energy
  function equals its normalized Haar mean.
* `specialUnitary_eq_const_of_laplacian_eq_zero`: a smooth function annihilated
  by the actual Laplacian is constant, by Haar integration by parts.

Independent examples check connectedness under the Frobenius scope at dimensions
zero, one, and three. The nonconstant quadratic SU(2) example now has **strictly
positive integrated Haar energy**, and an SU(3) example checks the harmonic
function conclusion. No connectedness or ergodicity class is assumed.

## Polynomial equilibrium and logarithmic Sobolev inequality

`Unitary/SpecialUnitaryPolynomialFunctionals.lean` proves joint evaluation,
continuity of normalized Haar mass, integrated carré du champ, and entropy on
each polynomial space with its actual supremum norm. Entropy continuity includes
zeros, using Mathlib's global continuity of `x log x`. Constants are constructed
inside every degree bound.

`Unitary/SpecialUnitaryPolynomialEnergyDecay.lean` proves that a positive smooth
density bounded by `M` satisfies `∫ Γ(g,g) ≤ M I(g)`. The proved polynomial heat
bounds and exponential Fisher estimate then give decay of integrated energy
to zero for every positive matrix dimension.

`Unitary/SpecialUnitaryPolynomialEquilibrium.lean` closes the equilibrium step:

* `specialUnitaryPolynomialForwardHeat_tendsto_mean`: every strictly positive
  polynomial heat orbit converges in the supremum norm to its normalized Haar mean.
* `specialUnitaryPolynomialForwardHeat_entropy_tendsto_zero`: its entropy tends
  to zero.

The proof puts the bounded orbit in a compact finite-dimensional ball. Continuity
of energy makes every cluster point zero-energy; the connectedness/kernel theorem
makes it a constant. Continuity and conservation of Haar mass uniquely determine
that constant. Mathlib's compact unique-cluster-point criterion yields convergence
of the entire orbit. No convergence or ergodicity assumption is introduced.

`Analysis/DissipationBound.lean:initial_le_div_of_dissipation_decay` proves the
scalar comparison `E(0) ≤ K/a` from `E′ = −I`, `I(t) ≤ exp(−at) K`, and a zero
limit of `E`. The hypotheses are all discharged by the constructed polynomial flow.

`Unitary/SpecialUnitaryPolynomialLSI.lean` now proves:

* `specialUnitaryPolynomial_entropy_le_fisher`:
  `entropy Haar g ≤ (1/N) * ∫ Γ(g,g)/g dHaar` for strictly positive polynomial `g`.
* `specialUnitaryPolynomial_entropy_sq_le`:
  `entropy Haar (f²) ≤ (4/N) * ∫ Γ(f,f) dHaar` for **every real polynomial `f`**.

Both apply in every positive matrix dimension. Here `Γ` is the actual generator's
carré du champ for a real orthonormal basis of the **unnormalized HS** Lie-algebra
inner product, and Haar is the actual normalized measure on SU(N).
`Unitary/SpecialUnitarySquareEnergy.lean` proves the exact factor four in
`Γ(f²+ε) = 4 f² Γ(f,f)` and the Fisher bound by `4 Γ(f,f)`. The squared theorem
uses the degree-`2d` polynomial `f²+ε` and entropy continuity as `ε ↓ 0`, so it has
no sign or nonvanishing hypothesis. Independent examples check a nonconstant
quadratic density, a centered quadratic vanishing at the identity, and the exact
coefficient `4/N` for arbitrary positive `N`.

## Actual local-slope comparison and polynomial metric LSI

`Geometry/LocalSlopeDerivative.lean:localSlope_eq_of_hasDerivAt` proves that the
paper's local slope on the real line equals the absolute derivative. It uses the
proved punctured-limsup characterization, so the zero quotient at the base point
does not invalidate the limit argument.

`Unitary/SpecialUnitarySlope.lean` proves left multiplication is an isometry for
the unnormalized Hilbert–Schmidt metric. Combining translated exponential curves,
their verified speed, and slope composition gives `specialUnitaryDeriv_le_localSlope`.
The actual gradient coordinates in a real HS orthonormal basis have squared norm
`Γ(f,f)`, and differentiation in that direction gives `Γ(f,f)`.
`specialUnitaryGamma_le_localSlope_sq` then proves, for every smooth real test:

```lean
ENNReal.ofReal (specialUnitaryGamma b f f U) ≤ localSlope f U ^ 2
```

The proof treats infinite slope separately before taking real values, and treats
a zero gradient separately before canceling its norm. No dimension factor or
normalization is lost. Equality of the two energies is not needed for this bound.

`Unitary/SpecialUnitaryPolynomialExtension.lean` constructs a **global smooth
ambient extension** of every polynomial observable by induction on submodule
powers. Restriction along the actual isometric matrix inclusion proves
`specialUnitaryPolynomial_locallyLipschitz`. Thus the compact regularity API
establishes measurability, square/log-moment integrability, and finite slope energy.

`Unitary/SpecialUnitaryPolynomialMetricLSI.lean` proves:

* `specialUnitaryPolynomial_metric_entropy_sq_le`: the exact extended local-slope
  inequality with constant `2/N` for every real polynomial observable.
* `specialUnitaryPolynomial_slopeEnergy_ne_top`: the right-hand side is finite.
* `specialUnitaryPolynomial_entropy_sq_le_slope`: the real form
  `Ent(f²) ≤ (4/N) ∫ (localSlope f).toReal² dHaar`, with no regularity or
  integrability premises beyond polynomial membership.

Independent examples check finite **strictly positive** slope energy on a concrete
nonconstant SU(2) polynomial, the real inequality for a centered quadratic with
a zero at the identity, and the exact constant `2/N` for arbitrary positive `N`.

## Completed extension to locally Lipschitz functions

`Geometry/LocalSlopeAverage.lean` proves
`ofReal_deriv_integral_sq_le_lintegral_localSlope_sq`. If summands are continuous
in the compact probability-space variable and uniformly Lipschitz in a real
time variable, and their average is differentiable, its squared derivative is
bounded by the average of their squared local slopes. The summands need not be
differentiable. The proof applies Jensen to difference quotients at
`t_j = 1/(j+1)`, then reverse Fatou with a finite constant dominator. The
sequential limsup is bounded by the actual metric local slope.

`Unitary/SpecialUnitaryConvolutionEnergy.lean` applies this result to
`f(U exp(tA) V)` under the probability measure with density `k(V)` against Haar.
Compact local Lipschitz regularity supplies a global bound, and verified left
and right HS isometries give speed `‖A‖`. Taking `A` to be the already constructed
smooth gradient gives the pointwise carré-du-champ bound. Tonelli and actual
right Haar invariance then prove:

```lean
specialUnitary_convolution_energy_le_slopeEnergy
-- For any nonnegative continuous kernel of Haar mass one, any locally
-- Lipschitz f, and any smooth p with p(U) = ∫ f(UV) k(V) dHaar(V):
-- ofReal (∫ Γ(p,p) dHaar) ≤ slopeEnergy Haar f.
```

The approximation uses the degree-one peak
`q(U) = (N + Re Tr U)/(2N)`, uniquely maximized at identity, and normalized
powers `k_j = q^j / ∫ q^j`. `SpecialUnitaryPeak.lean` proves the exact HS
trace identities and peak bounds. `SpecialUnitaryPowerKernel.lean` constructs
actual polynomial probability densities and proves concentration. The reusable
`Measure/PowerKernel.lean` gives a geometric tail bound; the Banach-valued
result in `Measure/PowerKernelApproximation.lean` yields **uniform** convergence
of the polynomial convolution approximants. `EntropyContinuity.lean` gives
squared entropy convergence, including functions with zeros.

`Unitary/SpecialUnitaryLSI.lean` applies the proved polynomial energy LSI to each
approximant, bounds every approximant's energy by the original slope energy,
and passes to the entropy limit. The resulting full theorem has no polynomial,
smoothness, supplied heat flow, curvature criterion, approximation, or energy
estimate among its hypotheses. It is valid for every positive dimension.

A general heat semigroup on all smooth functions, a Ricci theorem, and an
imported Bakry–Émery axiom are unnecessary for this proof. The finite-degree
heat construction and the verified approximation close the argument.

Independent examples include arbitrary positive dimensions, SU(1), and the
nonconstant distance-to-identity observable on SU(2), with its integrability
and finite slope energy proved. Earlier examples also prove strictly positive
finite slope energy for a concrete nonconstant quadratic observable.

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
`3c059da` (actual Haar integration by parts and integrated Γ₂ coercivity), and
`0c520e8` (scalar/logarithmic diffusion calculus, compact entropy
differentiation, conditional entropy dissipation, and weighted logarithmic Γ₂),
and `d6c3cc6` (spatial Fisher identity and conditional time-dependent Fisher
dissipation with explicit mixed-derivative hypotheses), and `60361a5` (actual
generator maximum principle, preservation of heat bounds, and constructed
positive affine heat solutions), and `50aba17` (finite-degree polynomial heat,
Haar-mass conservation, mixed regularity, constructed entropy/Fisher
dissipation, and exponential Fisher decay at rate `N`), and `c70774f`
(connectedness of actual U(N)/SU(N), zero-energy constancy, and the smooth
generator kernel), and `35e2978` (polynomial heat equilibrium, zero limiting
entropy, positive-density entropy bound, and the squared-polynomial LSI with
coefficient `4/N`), and `1e2e435` (pointwise local-slope comparison, polynomial
ambient extension and local Lipschitz regularity, and finite-energy polynomial
metric LSI), and `e41ed2b` (uniform entropy continuity, degree-preserving
pullbacks, polynomial convolution, and normalized averaging identities), and
`b391128` (concentrating polynomial probability kernels, Banach-valued
approximation, and uniform/entropy approximation of continuous SU observables),
and `1e46e9a` (averaged local-slope energy control and the full SU(N) LSI
for every locally Lipschitz real observable).
`lake build` and the independent `Examples.lean`
compilation pass. The recursive `Audit.lean` check passes for all 792 project
declarations, accepting only `propext`, `Classical.choice`, and `Quot.sound`.
It prints the fully elaborated commutator-energy, curve-velocity, and
exponential-speed, conjugation-derivative, and Killing-contraction, exact-coefficient, and real-orthonormal-energy theorems, exposes the Frobenius instances, and inspects the
Lie-algebra, trace-pairing, exponential-curve, and inner-product definitions.
The full output is in [axiom-audit.txt](axiom-audit.txt). These checks certify
the algebraic, curve, local-coordinate, smooth Lie-group, tangent-derivative,
smooth differential-operator, second-order energy, generator, Γ₂, and Haar
integration, logarithmic chain-rule, entropy-differentiation, and spatial and
conditional time-dependent Fisher results, the maximum principle, constructed
affine and polynomial heat solutions, their regularity and Fisher decay, and
actual U(N)/SU(N) connectedness, kernel constancy, polynomial equilibrium, and
polynomial entropy inequalities, the actual local-slope comparison, ambient
extension/regularity, polynomial convolution approximation, and the averaged
energy bound. They also certify the full locally Lipschitz SU(N) metric LSI
and its real-valued form, whose fully elaborated statements are printed.
The larger U(N) theorem remains open.
