# Mathematical report

## Result and limits

This is a **partial formalization**, not a proof of Meckes–Meckes Theorem 15.
There is no theorem claiming the `6/N` LSI on U(N), even for smooth functions or
for N=1. No interval or SU(N) LSI has been assumed as an axiom or installed in a
typeclass. The development proves the metric/measure foundations, the exact Haar
decomposition in Lemma 16, and the transport and regularity results below.

The principal unfinished step is analytic/geometric: obtaining SU(N)'s LSI
from a proved curvature calculation and a proved diffusion criterion. The
interval/circle LSI and the appropriate tensorization argument are also
substantial analytic obligations. The exact short-interval Haar decomposition is now proved, including N=1.
The remaining analytic/geometric obligations are mathematical missing proofs,
not merely unresolved Lean syntax or typeclass errors.

## Proved declarations

All names below are in namespace `LogSobolev`.

| Source | Main declarations | Precise scope |
|---|---|---|
| `LogSobolev/Measure/Entropy.lean` | `entropy_nonneg`, `entropy_map` | Jensen with integrability; entropy commutes with measurable pushforward. |
| `LogSobolev/Measure/ProductEntropy.lean` | `integrable_marginal_mul_log`, `integrable_slice_entropy`, `entropy_prod_chain`, `entropy_marginal_le` | Exact binary product chain rule and entropy contraction under marginalization. For nonnegative integrable densities with integrable log moment, marginal log-integrability is proved. This is not metric-LSI tensorization. |
| `LogSobolev/Measure/LSI.lean` | `HasEnergyLSI.map`, `.mono`, `.scale_energy` | Abstract implications with explicitly supplied source LSI, test class and energy comparison; not LSI existence. |
| `LogSobolev/Geometry/LocalSlope.lean` | `localSlope_eq_limsup_nhdsNE`, `localSlope_lt_top`, `localSlope_comp_le`, `localSlope_comp_isometryEquiv` | Actual upper local metric slope, including collapsed points under a map and isolated points. |
| `LogSobolev/Geometry/SlopeMeasurable.lean` | `localSlope_eq_iInf_iSup_probe`, `measurable_localSlope` | Borel measurability for every continuous real function on a metric space; no separability assumption. |
| `LogSobolev/Geometry/MetricLSI.lean` | `slopeEnergy_comp_le`, `MetricLSI.map`, `.map_isometryEquiv` | The squared-slope integral and LSI pushforward with factor `K²`. Locally Lipschitz tests have explicit entropy integrability; infinite energy is allowed. |
| `LogSobolev/Geometry/CompactRegularity.lean` | `integrable_sq_of_locallyLipschitz`, `integrable_sq_log_of_locallyLipschitz`, `integrable_localSlope_sq`, `slopeEnergy_eq_ofReal_integral`, `MetricLSI.real_form` | All requisite integrability for locally Lipschitz functions under a finite Borel measure on a compact metric space. The last theorem is conditional on LSI. |
| `LogSobolev/Unitary/HilbertSchmidt.lean` | `frobenius_norm_sq_eq_trace`, `unitary_norm`, `norm_unitary_mul`, `norm_mul_unitary` | `‖A‖² = Tr(A* A)`, `‖U‖ = sqrt(card n)`, and invariance under unitary multiplication. |
| `LogSobolev/Unitary/Haar.lean` | `unitaryCompactSpace`, `unitaryHaar`, `eq_unitaryHaar` | Haar probability on Mathlib's actual matrix unitary group, with uniqueness among left-invariant probability measures and right invariance. |
| `LogSobolev/Unitary/SpecialUnitary.lean` | `specialUnitaryInclusion_isometry`, `specialUnitaryCompactSpace`, `specialUnitaryHaar` | Actual SU group, closed/compact, isometrically included in U, with normalized Haar measure. No curvature result. |
| `LogSobolev/Unitary/SpecialUnitaryAlgebra.lean` | `specialUnitaryLieAlgebra`, `negTracePair_lie`, `negTracePair_self`, `specialUnitary_negTracePair_pos` | Real traceless skew-Hermitian Lie subalgebra and positive, invariant trace pairing with the exact Frobenius diagonal. No manifold tangent identification. |
| `LogSobolev/Unitary/MatrixCasimir.lean` | `sum_matrixUnits_double_lie`, `sum_matrixUnits_double_lie_of_trace_zero` | Algebraic identity `Σ[Eij,[Eji,A]] = 2N A − 2 Tr(A) I` over any commutative ring. |
| `LogSobolev/Unitary/SpecialUnitaryCasimir.lean` | `sum_matrixUnits_lie_norm_sq`, `specialUnitary_commutator_energy` | The matrix-unit commutator-energy sum is `2N ‖A‖²` on the traceless skew-Hermitian subalgebra. Matrix units are not a real tangent basis; this does not yet prove Ricci or LSI. |
| `LogSobolev/Unitary/DeterminantDerivative.lean` | `hasDerivAt_det_at_one` | Entrywise differentiable matrix curves at identity have determinant derivative equal to trace. |
| `LogSobolev/Unitary/UnitaryCurves.lean` | `skewAdjoint_iff_unitary_curve_velocity` | Skew-Hermitian matrices are exactly velocities at identity of actual unitary curves. |
| `LogSobolev/Unitary/SpecialUnitaryCurves.lean` | `det_exp_smul_eq_one_of_trace_zero`, `mem_specialUnitaryLieAlgebra_iff_curve_velocity`, `specialUnitaryExpCurve_speed`, `specialUnitaryExpCurve_lipschitz` | Trace-zero exponentials have determinant one; actual SU curve velocities characterize the algebra, with exact Frobenius speeds and norm-preserving left translation. No manifold atlas or curvature theorem. |
| `LogSobolev/Unitary/SpecialUnitaryInner.lean` | `specialUnitaryAlgebraInnerProductSpace`, `specialUnitary_ad_skew` | Real trace inner product compatible with the existing Frobenius norm, finite dimensionality, and skew-symmetry of the adjoint action. |
| `LogSobolev/Unitary/SpecialUnitaryAdjoint.lean` | `specialUnitaryAdjointIsometry`, `specialUnitaryAdjoint_lie`, `specialUnitaryAdjoint_exp_derivative` | Actual unitary conjugation acts isometrically and preserves brackets; its derivative along an SU exponential curve is the matrix commutator. |
| `LogSobolev/Unitary/SpecialUnitaryKilling.lean` | `specialUnitary_killing_self`, `specialUnitary_commutator_energy_basis_independent`, `specialUnitary_killing_self_nonpos` | Negative Killing form equals commutator energy over any real HS orthonormal basis. The Ricci interpretation remains unproved. |
| `LogSobolev/Unitary/MatrixAdjointTrace.lean` | `matrix_real_trace`, `matrix_real_trace_ad_sq` | Full real trace of double adjoint is `−4N ‖A‖²` for traceless skew-Hermitian A. |
| `LogSobolev/Unitary/MatrixRealForm.lean` | `matrixSkewDecompose`, `matrix_real_trace_eq_twice_skew` | A complex-linear star-commuting matrix operator has twice the real trace of its skew-adjoint restriction. |
| `LogSobolev/Unitary/SpecialUnitaryKillingConstant.lean` | `specialUnitary_killing_self_eq`, `specialUnitary_killing_eq_inner`, `specialUnitary_orthonormal_commutator_energy` | Exact real Killing coefficient `−2N` and commutator energy coefficient `2N` for every real HS orthonormal basis. The Ricci formula and LSI are not asserted. |
| `LogSobolev/Unitary/MatrixExpDeterminant.lean` | `hasDerivAt_det_exp_smul`, `det_matrix_exp` | Determinant-exponential identity for all complex matrices, proved by scalar ODE and integrating factor. |
| `LogSobolev/Unitary/MatrixLocalExponential.lean` | `matrixExpLocalHomeomorph`, `matrixLog_hasStrictFDerivAt_one`, `matrixLog_contDiffAt_one`, `exists_specialUnitary_exp_neighborhood` | Actual ambient local inverse and its smoothness at identity; near zero the SU constraint is equivalent to membership in su. |
| `LogSobolev/Unitary/SpecialUnitaryLocalCoordinates.lean` | `exists_specialUnitary_exp_homeomorph` | Exponential is a homeomorphism between genuine open identity neighborhoods in the real algebra and the actual matrix SU group. Smooth compatibility is supplied by the later manifold module; curvature is still unproved. |
| `LogSobolev/Unitary/SpecialUnitaryAnalyticNeighborhood.lean` | `exists_specialUnitary_analytic_exp` | SU-compatible ambient exponential chart with analytic inverse at every target point. |
| `LogSobolev/Unitary/SpecialUnitaryChart.lean` | `specialUnitaryExpChart`, `specialUnitaryChartedSpace` | Actual SU/su partial homeomorphism and a translated covering atlas on the existing group topology. |
| `LogSobolev/Unitary/SpecialUnitaryManifold.lean` | `specialUnitary_chart_transition_contDiffOn`, `specialUnitaryIsManifold` | Every atlas transition is smooth; the actual matrix group is a smooth real manifold modeled on su with its Frobenius norm. The tangent metric, curvature, and LSI are not asserted by this module. |
| `LogSobolev/Unitary/SpecialUnitarySmoothMaps.lean` | `specialUnitary_val_contMDiff`, `contMDiff_specialUnitary_iff` | Inclusion is smooth; an SU-valued map is smooth iff its ambient matrix map is smooth, for arbitrary source charted spaces. |
| `LogSobolev/Unitary/SpecialUnitaryLieGroup.lean` | `specialUnitary_mul_contMDiff`, `specialUnitary_inv_contMDiff`, `specialUnitaryLieGroup`, `specialUnitary_exp_contMDiff` | Proved smooth operations install a genuine Lie group on the original matrix SU group and atlas. |
| `LogSobolev/Unitary/SpecialUnitaryTangent.lean` | `specialUnitary_val_hasMFDerivAt`, `specialUnitary_mfderiv_val_norm` | Actual manifold inclusion derivative is `A ↦ U A` with exact Frobenius norm preservation in model coordinates. No Riemannian bundle or curvature theorem is assumed. |
| `LogSobolev/Unitary/PhaseMap.lean` | `phaseMul_dist_le`, `phaseMap_lipschitz` | The full-line phase map has Lipschitz constant `sqrt(3)` for every positive N; no probability argument is needed. |
| `LogSobolev/Measure/Interval.lean` | `intervalUniform_univ`, `map_intervalUniform` | Normalized Lebesgue measure on the Euclidean subtype `[0,L]` for `L>0`. |
| `LogSobolev/Unitary/ProductDomain.lean` | `phaseDomainMeasure_probability`, `intervalPhaseMap_lipschitz` | The exact interval × SU domain and probability measure, and the restricted map's Lipschitz bound. |
| `LogSobolev/Unitary/CircleDecomposition.lean` | `circleSpecialUnitaryMap_surjective`, `map_circleSpecialUnitaryMap`, `map_circleSpecialUnitaryMap_mul_root` | Continuous surjective scalar homomorphism from Circle × SU to U, full-circle Haar decomposition, and invariance of the SU mixture under central Nth roots. |
| `LogSobolev/Unitary/PhasePeriodicity.lean` | `phaseInterval_root`, `phaseSliceMeasure_periodic`, `phaseAverage_intervalIntegral_translate` | The SU-averaged phase distribution has exactly the paper's short period, and its integral is unchanged by translating the integration window. |
| `LogSobolev/Unitary/PhaseHaar.lean` | `integral_map_intervalPhaseMap`, `map_intervalPhaseMap` | **Unconditional Lemma 16:** the exact normalized interval × SU measure maps to normalized U Haar, for every positive N including N=1. |
| `LogSobolev/Unitary/LSITransfer.lean` | `unitary_metricLSI_of_phaseDomain` | **Conditional:** explicitly assumes source MetricLSI(2/N), then proves target MetricLSI(6/N) using the verified Haar identity and Lipschitz bound. No source LSI is proved. |
| `LogSobolev/Unitary/Observables.lean` | `entryReal_lipschitz`, `entryReal_not_ae_constant`, `unitary_regular` | A meaningful nonconstant test in each positive dimension, and all integrability requirements for every locally Lipschitz U(N) observable. |

## Convention and semantic checks

* The group is `Matrix.unitaryGroup (Fin N) ℂ`, not an abstract type satisfying
  an assumed LSI. SU is `Matrix.specialUnitaryGroup (Fin N) ℂ`.
* `unitaryHaar` and `specialUnitaryHaar` are `Measure.haarMeasure ⊤`, after
  proving compactness. Their total masses are proved to be one.
* `Matrix.Norms.Frobenius` is open at elaboration of every matrix-metric result.
  The trace identity and the identity-matrix norm example exclude division by N
  and exclude the operator norm. `WithLp 2` explicitly supplies the L² product
  metric; the ordinary maximum product metric is not substituted.
* `localSlope` has values in `ℝ≥0∞`. Its definition is the limsup of the absolute
  difference quotient, with denominator the actual metric distance. Its
  equality to the punctured-neighborhood definition is proved. It is finite
  on all locally Lipschitz tests. `toReal` is used for the real energy only
  after that finiteness is established.
* `MetricLSI` uses `2C`. `MetricLSI.real_form` recovers the ordinary finite
  integral inequality on compact spaces, with all integrability established.
  A future constant `6/N` therefore has coefficient `12/N`.
* `phaseMap_apply` gives the actual exponential matrix formula. The interval
  length is `π * sqrt(2/N)`. Its positivity and probability normalization need
  `N>0`. The metric proof works for N=1 too, but is **not** a proof of its LSI.
* The real diagonal coordinate separates `I` from `-I`, is 1-Lipschitz, and is
  not a.e. constant under Haar. This checks that the admissible class contains
  nonconstant functions. It does not by itself prove their entropy inequality.

## Exact remaining statements

The following are **unproved goals**, not library declarations. They use the
definitions already implemented. Open `MeasureTheory`, `LogSobolev`, and the
scopes `NNReal` and `Matrix.Norms.Frobenius`.

The main target is:

```lean
∀ (N : ℕ), 0 < N →
  MetricLSI (unitaryHaar (Fin N)) (6 / (N : ℝ≥0))
```

Equivalently for the intended applications, the desired real inequality is:

```lean
∀ (N : ℕ), 0 < N →
  ∀ f : Matrix.unitaryGroup (Fin N) ℂ → ℝ, LocallyLipschitz f →
    entropy (unitaryHaar (Fin N)) (fun U => f U ^ 2) ≤
      (12 / (N : ℝ)) *
        ∫ U, (localSlope f U).toReal ^ 2 ∂unitaryHaar (Fin N)
```

The reference route still needs these statements:

```lean
-- SU(N), with exactly the unnormalized metric and Haar probability:
∀ (N : ℕ), 2 ≤ N →
  MetricLSI (specialUnitaryHaar (Fin N)) (2 / (N : ℝ≥0))

-- The Euclidean interval, all locally Lipschitz finite-entropy tests:
∀ (N : ℕ), 0 < N →
  MetricLSI (intervalUniform (phaseIntervalLength N)) (2 / (N : ℝ≥0))

-- Tensorization for this L² metric and the actual product probability:
∀ (N : ℕ), 2 ≤ N →
  MetricLSI (intervalUniform (phaseIntervalLength N)) (2 / (N : ℝ≥0)) →
  MetricLSI (specialUnitaryHaar (Fin N)) (2 / (N : ℝ≥0)) →
  MetricLSI (phaseDomainMeasure N) (2 / (N : ℝ≥0))

-- The remaining separate N=1 analytic case:
MetricLSI (unitaryHaar (Fin 1)) 6
```

None of these is a hypothesis hidden in the proved geometric or regularity
results. `map_intervalPhaseMap` now proves the required Haar image identity
without any analytic assumptions. `unitary_metricLSI_of_phaseDomain` separately
exposes the remaining product LSI as its hypothesis.

## Shortest sound continuation

The measure-theoretic step is complete. Its proof takes an Nth root of the
determinant to factor every unitary as a circle scalar times an SU matrix.
Central Nth roots preserve SU Haar, so averaging over SU makes the phase
distribution periodic with period `π * sqrt(2/N)`. Fubini and periodic interval
integration show invariance under every left translation in U. The existing
`eq_unitaryHaar` then identifies the normalized pushforward. Closed interval
endpoints are handled by the verified equality of Lebesgue integrals on Icc
and Ioc. This argument applies for every positive N.

The binary entropy chain rule and its marginal log-integrability are now
proved in `ProductEntropy.lean`, adapted from the inspected conditional-entropy
library to heterogeneous products. This is an analytic ingredient, not the
metric-LSI tensorization theorem. The next tensorization obligation is to control
the local slope of the square root of a marginal of `f²`, and relate the two
coordinate energies to the full L²-product energy. The manifold/interval
setting needs the appropriate gradient-to-local-slope identification; the
inspected Gaussian tensorization is not immediately that theorem. Prove a one-dimensional
circle/interval LSI and scaling, including the circle case for N=1.

The [SU-specific proof boundary](SU_LSI.md) describes the algebraic
normalization, smooth Lie group, and tangent-inclusion proofs. The geometric
Lie-bracket identification, Riemannian metric, and curvature computation remain
to be established.
The SU step still needs a concrete diffusion or Riemannian development: the
Hilbert–Schmidt bi-invariant geometry, Ricci normalization, entropy dissipation,
curvature-to-Fisher-information decay, equilibrium convergence, and any smooth
approximation needed to obtain locally Lipschitz functions. The abstract
`markov-semigroups` class does not eliminate these obligations. Its assumed
entropy decay must not be passed off as a proved curvature criterion.

Once the analytic ingredients exist, `unitary_metricLSI_of_phaseDomain`
already assembles the result with constant `6/N`; `MetricLSI.real_form` removes
the compact regularity side conditions. A verified Herbst argument is a later task.

## Verification and commits

Verification performed on 2026-10-10 with Lean 4.28.0 and the pinned Mathlib
commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`:

* `lake build`: passed for the complete library (2903 dependency/build jobs,
  primarily cached Mathlib artifacts).
* `lake env lean LogSobolev/Examples.lean`: passed; the examples compile as an
  independent client importing the public root module.
* `lake env lean LogSobolev/Audit.lean`: passed. The automated traversal checked
  **402 declarations** in the `LogSobolev` namespace, including definitions,
  instances, and generated auxiliaries. Every transitive axiom was one of
  `propext`, `Classical.choice`, or `Quot.sound`. No `sorryAx` or custom axiom
  was present in those dependency closures.
* The audit also executes 78 `#print axioms` commands, prints the core
  definitions, and prints fully elaborated types for the trace normalization,
  phase-map Lipschitz theorem, U(N) regularity theorem, exact Haar identity,
  conditional final LSI transfer, product entropy chain rule, and SU algebra
  commutator energy, SU curve-velocity characterization, and exponential speed, the real Killing contraction, and the derivative of
  conjugation, the exact Killing coefficient, the real orthonormal energy, the actual SU local
  coordinates, smoothness of the ambient inverse, the actual smooth atlas, the ambient smooth-map criterion, Lie group instance,
  and inclusion derivative with exact coordinate-norm preservation. The elaborated
  metric instances are explicitly Frobenius and `WithLp 2`.
* Source scan found no proof omissions or custom axiom declarations;
  `git diff --check` passed.

The complete output is preserved in [axiom-audit.txt](axiom-audit.txt).
See `scripts/check.sh` for the repeatable commands. This audit certifies the
proved partial results; there is no final U(N) LSI theorem to audit yet.

Completed milestones:

* `d774e93`: ecosystem audit, pinned project, entropy transport and
  Hilbert–Schmidt normalization.
* `a8ce6ef`: metric-slope measurability and transport, compact regularity,
  normalized Haar/interval/product measures, the phase-map estimate,
  nonconstant observables, independent examples and the recursive axiom audit.
* `cc0eae8`: unconditional short-interval Haar decomposition for every positive
  N, full-circle decomposition, central-root invariance and phase periodicity;
  conditional `2/N` to `6/N` LSI transfer; independent examples at N=1 and N=3,
  and the expanded 163-declaration recursive audit.
* `0e9ac0d`: product entropy chain rule, proved marginal log-integrability,
  integrability of slice entropy, and entropy contraction under marginalization;
  a compact locally Lipschitz usage example and the 167-declaration audit.
  This milestone does not close metric-LSI tensorization or the main theorem.
* `0f05569`: the real matrix special unitary Lie subalgebra, invariant positive
  trace pairing, general matrix-unit double-commutator identity, and exact
  `2N` Frobenius commutator energy; normalization examples and the expanded
  194-declaration audit. The SU LSI and Ricci interpretation remain unproved.

* `339112a`: determinant derivative at identity, trace-zero exponential determinant,
  actual U/SU curve-velocity characterizations, SU exponential curves with exact
  Frobenius speed and Lipschitz bound, and norm-preserving velocity translation.
  Independent examples and the expanded 222-declaration recursive audit pass.
  These results do not establish Ricci curvature or SU LSI.

* `5bf0ed6`: the Frobenius-compatible real inner-product structure on su,
  isometric unitary conjugation preserving the bracket, its derivative along
  SU exponential curves, and the Killing-form contraction over a real
  orthonormal basis. Independent examples and all 255 declarations pass the
  recursive audit. The exact Killing coefficient, Ricci formula, and LSI are open.

* `5c6ebdb`: exact real Killing coefficient `−2N` and real orthonormal
  commutator energy `2N`, proved via full matrix trace, the two real adjoint
  summands, and traceless-range restriction. The independent nonzero su(2)
  example, complete build, and recursive 306-declaration audit pass.
  The manifold Ricci formula and the analytic LSI remain open.

* `2387b3e`: full determinant-exponential identity; ambient exponential local
  homeomorphism and smooth inverse at identity; exact local SU/su constraint
  correspondence; and an exponential homeomorphism between actual open
  neighborhoods in su and SU. The old trace-zero determinant proof now uses
  the general identity. Build, independent examples, and all 327 declarations
  pass the recursive audit. A smooth atlas, curvature, and LSI remain open.

* `78fea3b`: SU-compatible ambient neighborhoods with analytic inverse throughout,
  a totalized exponential/logarithm partial homeomorphism, a translated atlas
  on the original SU topology, and the proved `IsManifold` instance. Every
  transition is smooth on its source. Build, independent examples, and the
  380-declaration recursive audit pass. Smooth group operations, tangent metric,
  curvature, and the analytic LSI remain open.

* `fc7c4c0`: ambient smooth-map criterion, smooth multiplication/inversion and
  exponential, the actual SU `LieGroup` instance, and the inclusion derivative
  `A ↦ U A` with exact Frobenius norm preservation in model coordinates.
  Full build (2903 jobs), independent examples, and the 402-declaration recursive
  axiom audit pass. The geometric bracket identification, smooth Riemannian
  metric, curvature, and analytic LSI remain open.

The report and README are committed separately after these verified proof
milestones; use `git log --oneline` to see the documentation commit as well.
