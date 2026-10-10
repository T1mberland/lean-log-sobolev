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

## What these identities do not prove

The complex matrix units Eij are **not** a real orthonormal basis of su(N).
Thus the last displayed sum has not been declared to be Ricci curvature.
Connecting it to curvature requires the real tangent-space and basis
identifications and the Levi-Civita/curvature calculation for the bi-invariant
metric. The algebraic dimension factor alone is insufficient.

The inspected Mathlib checkout supplies general Lie-group and Riemannian
interfaces, but no SU Lie-group instance or curvature-to-LSI theorem applicable
here was found. No such result has been added as a hypothesis disguised as an
instance. The audited `markov-semigroups` class still assumes the entropy decay
needed for its abstract LSI implication and cannot supply this missing proof.

## Remaining route to the theorem

1. Upgrade the proved curve-velocity characterization to a manifold tangent
   identification for the actual matrix SU group, and construct the Hilbert–Schmidt bi-invariant
   Riemannian metric. Relate the matrix-unit identity to the real orthonormal
   tangent contraction and prove the Ricci bound with normalization `N/2`.
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

Proof commits: `0f05569` (algebra) and `339112a` (curves). `lake build` and the independent `Examples.lean`
compilation pass. The recursive `Audit.lean` check passes for all 222 project
declarations, accepting only `propext`, `Classical.choice`, and `Quot.sound`.
It prints the fully elaborated commutator-energy, curve-velocity, and
exponential-speed theorems, exposes the Frobenius instances, and inspects the
Lie-algebra, trace-pairing, and exponential-curve definitions.
The full output is in [axiom-audit.txt](axiom-audit.txt). These checks certify
the algebraic and curve results above, not an SU(N) LSI theorem.
