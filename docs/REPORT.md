# Mathematical report

## Result and limits

This is a **partial formalization**, not a proof of Meckes–Meckes Theorem 15.
There is no theorem claiming the `6/N` LSI on U(N), even for smooth functions or
for N=1. No interval or SU(N) LSI has been assumed as an axiom or installed in a
typeclass. The development proves the metric/measure foundations, the exact Haar
decomposition in Lemma 16, and the transport and regularity results below.

The SU(N) entropy inequality is now proved on **all polynomial matrix observables**
in carré-du-champ energy form, with coefficient `4/N` on `Ent(f²)`. The constructed
heat proof includes positivity, Haar-mass conservation, Fisher decay, convergence,
and vanishing limiting entropy. The principal remaining SU obligation is extension
to the full locally Lipschitz class by an energy-controlled approximation.
The comparison with the actual local Hilbert–Schmidt slope and the polynomial
metric LSI, including finite slope energy, are now proved. The interval/circle LSI and the appropriate tensorization argument are also
substantial analytic obligations. The exact short-interval Haar decomposition is now proved, including N=1.
Entropy continuity under uniform convergence, degree preservation under translations
and inversion, and polynomial convolution of arbitrary continuous observables are
also proved. Normalized convolution preserves Haar mass; nonnegative normalized
kernels preserve upper bounds. Explicit normalized powers of the polynomial
peak now give concentrating polynomial probability densities and uniform
polynomial approximation of every continuous observable, with convergence of
squared entropy. What remains on the SU approximation route is control of the
averaged differential energy by the original function's local-slope energy.
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
| `LogSobolev/Geometry/AlgebraVectorFields.lean` | `rightMul_lieBracket`, `rightMulDeriv_commutator` | The actual Euclidean bracket of `x ↦ x A` and `x ↦ x B` is `x ↦ x(AB−BA)`; differentiation operators satisfy the corresponding commutator for `C²` tests. |
| `LogSobolev/Unitary/SpecialUnitaryInvariantFields.lean` | `specialUnitary_mfderiv_mul_left_apply`, `specialUnitary_mulInvariantVectorField_val` | Mathlib's geometric invariant tangent field has ambient velocity `U A`; no geometric bracket or curvature formula is presumed. |
| `LogSobolev/Unitary/SpecialUnitarySmoothExtension.lean` | `specialUnitary_exists_local_smooth_extension` | Every smooth SU function has a proved smooth ambient extension locally at each point, with no extension assumption. |
| `LogSobolev/Unitary/SpecialUnitaryDifferentialOperators.lean` | `specialUnitaryDeriv_contMDiff`, `specialUnitaryDeriv_commutator` | Actual invariant manifold differentiation preserves smoothness and satisfies `D_A D_B − D_B D_A = D_[A,B]` for every smooth SU test. First-order operator identities; the higher-order conclusions are proved in later modules. |
| `LogSobolev/Geometry/SecondOrderArray.lean` | `sum_sq_sub_transpose_le` | Antisymmetrization has squared norm at most four on a finite real array. |
| `LogSobolev/Unitary/SpecialUnitarySecondOrder.lean` | `specialUnitary_dual_commutator_energy`, `specialUnitary_second_derivative_energy_lower_bound` | Exact dual Killing contraction `2N`; for every smooth real SU test and real HS orthonormal basis, second-derivative energy is at least `N/2` times first-derivative energy. No Γ₂ identity is assumed. |
| `LogSobolev/Unitary/SpecialUnitaryGenerator.lean` | `specialUnitaryLaplacian`, `specialUnitaryLaplacian_contMDiff`, `specialUnitaryGamma_eq`, `specialUnitaryGamma_nonneg` | Actual sum of squares preserves smoothness. Its generator-defined carré du champ equals the sum of products of first derivatives. No semigroup or invariant-measure identity yet. |
| `LogSobolev/Geometry/CasimirCommutation.lean` | `sum_squares_commute_of_skew_coefficients` | A finite sum of squares commutes with any element whose commutator acts by skew coefficients. Pure algebra, applied below to actual operators. |
| `LogSobolev/Unitary/SpecialUnitaryOperatorAlgebra.lean` | `specialUnitaryDerivEnd`, `specialUnitaryDerivRepresentation`, `specialUnitaryDerivEnd_commutator` | Actual invariant derivatives as linear endomorphisms of genuine smooth functions, with proved linearity and commutator relation. |
| `LogSobolev/Unitary/SpecialUnitaryGeneratorCommutation.lean` | `specialUnitaryCasimir_commute`, `specialUnitaryLaplacian_deriv` | The constructed generator commutes with every invariant derivative for a real HS orthonormal basis; no diffusion or curvature hypothesis. |
| `LogSobolev/Unitary/SpecialUnitaryGammaTwo.lean` | `specialUnitaryGammaTwo_eq`, `specialUnitaryGammaTwo_lower_bound` | Γ₂ is defined by `(LΓ−2Γ(f,Lf))/2`; its equality with second-derivative energy and the exact lower bound `Γ₂ ≥ (N/2)Γ` are proved for every smooth real test. This is not LSI or entropy decay. |
| `LogSobolev/Unitary/SpecialUnitaryFlow.lean` | `specialUnitary_hasDerivAt_mul_exp` | Derivative along the actual curve `U exp(tA)` equals invariant differentiation for smooth tests. |
| `LogSobolev/Unitary/SpecialUnitaryHaarCalculus.lean` | `eq_specialUnitaryHaar`, `specialUnitary_integral_deriv_eq_zero`, `specialUnitary_integral_mul_laplacian` | Right invariance, zero integral of invariant derivatives, and the actual Haar Dirichlet identity. The generator is symmetric and nonpositive on smooth tests; all integrability is proved. |
| `LogSobolev/Unitary/SpecialUnitaryIntegratedGammaTwo.lean` | `specialUnitary_integral_gammaTwo`, `specialUnitary_integrated_gammaTwo_lower_bound` | `∫ Γ₂(f) = ∫ (Lf)²` and `(N/2) ∫ Γ(f,f) ≤ ∫ (Lf)²` for normalized Haar and smooth tests. This is not an entropy or Poincaré inequality. |
| `LogSobolev/Measure/CompactDifferentiation.lean` | `hasDerivAt_integral_of_compact` | Joint continuity and a local time derivative give differentiation under a finite measure on a compact space; domination is proved. |
| `LogSobolev/Measure/EntropyDifferentiation.lean` | `hasDerivAt_entropy_of_compact`, `hasDerivAt_entropy_of_compact_of_integral_eq_zero` | Entropy derivative of a positive family, including the changing-mass correction and its zero-mass-derivative specialization. |
| `LogSobolev/Unitary/SpecialUnitaryChainRules.lean` | `specialUnitaryLaplacian_comp`, `specialUnitaryLaplacian_log`, `specialUnitaryGamma_log`, `specialUnitary_integral_log_mul_laplacian` | Actual diffusion chain rule, logarithmic generator/energy formulas, and logarithmic Haar integration by parts. |
| `LogSobolev/Unitary/SpecialUnitaryEntropyDissipation.lean` | `specialUnitary_hasDerivAt_entropy`, `specialUnitary_entropy_deriv_nonpos`, `specialUnitary_weighted_gammaTwo_log_lower_bound` | Entropy dissipation for an explicitly supplied positive differentiable family in the actual heat direction; weighted logarithmic Γ₂ estimate. No heat existence or Fisher time-decay theorem is asserted. |
| `LogSobolev/Unitary/SpecialUnitaryFisherIdentity.lean` | `specialUnitary_fisher_variation_identity`, `specialUnitary_fisher_variation_le` | Spatial Fisher variation equals `−2 ∫ f Γ₂(log f)` and is at most `−N I(f)` for positive smooth tests and an HS orthonormal basis. No time family is needed. |
| `LogSobolev/Unitary/SpecialUnitaryFisherDifferentiation.lean` | `specialUnitary_hasDerivAt_fisher`, `specialUnitary_hasDerivAt_fisher_of_heat`, `specialUnitary_fisher_deriv_le` | Conditional Fisher derivative and dissipation for supplied families with explicit joint-continuity and mixed-derivative hypotheses. Proves `I′ ≤ −N I` in the heat direction; no heat construction or exponential decay is claimed. |
| `LogSobolev/Geometry/SecondDerivativeExtrema.lean` | `secondDerivative_nonneg_of_isLocalMin`, `secondDerivative_nonpos_of_isLocalMax` | Necessary second-derivative signs at extrema, proved from Mathlib's derivative test. |
| `LogSobolev/Geometry/CompactEvolutionMaximum.lean` | `nonneg_of_compact_minimum_principle` | Positivity preservation for a supplied evolution on a compact space whose time derivative is nonnegative at spatial minima. |
| `LogSobolev/Unitary/SpecialUnitaryMaximumPrinciple.lean` | `specialUnitary_laplacian_nonneg_at_min`, `specialUnitary_laplacian_nonpos_at_max` | The actual SU generator has the required signs at local extrema, via verified exponential curves. |
| `LogSobolev/Unitary/SpecialUnitaryHeatBounds.lean` | `specialUnitary_heat_lower_bound`, `specialUnitary_heat_upper_bound`, `specialUnitary_heat_nonneg` | Supplied classical solutions of the actual SU heat equation preserve initial bounds; positivity is a conclusion. |
| `LogSobolev/Unitary/SpecialUnitaryLinearHeat.lean` | `specialUnitaryLinearHeat`, `specialUnitaryLaplacian_affine`, `specialUnitaryLinearHeat_hasDerivAt`, `specialUnitaryLinearHeat_pos` | Actual constructed heat solution `c+l(U exp(t ∑ bᵢ²))` for affine matrix observables. Initial value, PDE, continuity, smooth spatial slices, bounds and forward strict positivity are proved. No general heat construction or LSI is asserted. |
| `LogSobolev/Geometry/DerivationSubmodulePowers.lean` | `derivation_mem_submodule_mul`, `derivation_mem_submodule_pow` | A derivation preserving submodules preserves their products and powers. |
| `LogSobolev/Unitary/SpecialUnitaryPolynomialSpace.lean` | `specialUnitaryPolynomialSpace_finite`, `specialUnitaryDerivEnd_mem_polynomial`, `specialUnitaryLaplacianEnd_mem_polynomial` | Finite-dimensional powers of actual affine SU observables are preserved by invariant differentiation and the actual generator. |
| `LogSobolev/Unitary/SpecialUnitaryPolynomialNorm.lean` | `specialUnitaryPolynomialToContinuous_injective`, `specialUnitaryPolynomialLaplacianCLM`, `specialUnitaryPolynomialDerivCLM` | Actual supremum norm, completeness by finite dimensionality, continuous restricted operators. |
| `LogSobolev/Unitary/SpecialUnitaryPolynomialHeat.lean` | `specialUnitaryPolynomialHeat_hasDerivAt_apply`, `specialUnitaryPolynomialHeat_add`, `specialUnitaryPolynomialHeat_norm_le`, `specialUnitaryPolynomialHeat_integral` | Constructed exponential evolution solves the actual heat equation on each polynomial space, preserves bounds and normalized Haar mass, and contracts the supremum norm. |
| `LogSobolev/Unitary/SpecialUnitaryPolynomialHeatRegularity.lean` | `specialUnitaryPolynomialForwardHeat_clm_continuous`, `specialUnitaryPolynomialForwardHeat_clm_hasDerivAt` | Joint and mixed derivative regularity for the constructed heat flow, constantly extended before time zero. |
| `LogSobolev/Analysis/ExponentialDecay.lean` | `le_exp_mul_of_deriv_le` | Integrating-factor decay from `f′ ≤ −a f`, with only continuity required at zero. |
| `LogSobolev/Unitary/SpecialUnitaryPolynomialDissipation.lean` | `specialUnitaryPolynomialForwardHeat_hasDerivAt_entropy`, `specialUnitaryPolynomialForwardHeat_hasDerivAt_fisher`, `specialUnitaryPolynomialForwardHeat_fisher_le_exp` | Actual entropy/Fisher dissipation and `I(Pₜ f) ≤ exp(−Nt) I(f)` for strictly positive polynomial data. No supplied trajectory, PDE, or mixed-regularity hypothesis remains. Equilibrium and polynomial LSI are proved in subsequent modules. |
| `LogSobolev/Geometry/FiniteSpectrumUnitary.lean` | `expUnitary_argSelfAdjoint_of_finite_spectrum`, `unitary_connectedSpace_of_finite_spectrum` | Finite-spectrum unitaries are exponentials by Mathlib's continuous functional calculus; the unitary group is connected when all unitary spectra are finite. |
| `LogSobolev/Unitary/UnitaryConnected.lean` | `unitaryConnectedSpace` | Connectedness of actual complex U(N) in the standard finite matrix topology; operator norm used only locally for C⋆ functional calculus. |
| `LogSobolev/Unitary/SpecialUnitaryConnected.lean` | `unitaryToSpecialUnitary_continuous`, `unitaryToSpecialUnitary_inclusion`, `specialUnitaryConnectedSpace` | A verified continuous determinant-correcting retraction U(N) → SU(N) proves connectedness, including the empty-index case. |
| `LogSobolev/Unitary/SpecialUnitaryZeroEnergy.lean` | `specialUnitary_eq_mean_of_integral_gamma_eq_zero`, `specialUnitary_eq_const_of_laplacian_eq_zero` | Smooth zero-Haar-energy functions equal their Haar mean. The actual SU Laplacian's smooth kernel contains only constants. Full support, basis detection, exponential orbits, and connectedness are proved or reused, not assumed. |
| `LogSobolev/Unitary/SpecialUnitaryPolynomialFunctionals.lean` | `specialUnitaryPolynomial_integral_continuous`, `specialUnitaryPolynomial_energy_continuous`, `specialUnitaryPolynomial_entropy_continuous` | Continuous Haar mass, energy, and entropy on each polynomial space with its actual supremum norm. |
| `LogSobolev/Unitary/SpecialUnitaryPolynomialEnergyDecay.lean` | `specialUnitaryPolynomialForwardHeat_energy_tendsto_zero` | Positive polynomial heat has integrated carré-du-champ energy tending to zero. |
| `LogSobolev/Unitary/SpecialUnitaryPolynomialEquilibrium.lean` | `specialUnitaryPolynomialForwardHeat_tendsto_mean`, `specialUnitaryPolynomialForwardHeat_entropy_tendsto_zero` | Supremum-norm convergence to the normalized Haar mean and zero limiting entropy; no assumed convergence/ergodicity. |
| `LogSobolev/Analysis/DissipationBound.lean` | `initial_le_div_of_dissipation_decay` | Scalar comparison bound from explicit dissipation, information decay, continuity at zero, and a zero entropy limit. |
| `LogSobolev/Unitary/SpecialUnitarySquareEnergy.lean` | `specialUnitaryGamma_sq_add_const`, `specialUnitary_fisher_sq_add_const_le` | Exact factor four for regularized squares and the corresponding Fisher-density bound. |
| `LogSobolev/Unitary/SpecialUnitaryPolynomialLSI.lean` | `specialUnitaryPolynomial_entropy_le_fisher`, `specialUnitaryPolynomial_entropy_sq_le` | Proved positive-density `Ent(g) ≤ I(g)/N`, then `Ent(f²) ≤ (4/N) ∫ Γ(f,f)` for every real polynomial observable, without a positivity hypothesis on `f`. Actual normalized Haar and unnormalized HS orthonormal generator. The local-slope form is proved in the subsequent metric module; the full smooth/locally Lipschitz extension remains open. |
| `LogSobolev/Geometry/LocalSlopeDerivative.lean` | `localSlope_eq_of_hasDerivAt` | The paper's upper local slope on the real line is the absolute derivative. |
| `LogSobolev/Unitary/SpecialUnitarySlope.lean` | `specialUnitaryDeriv_le_localSlope`, `specialUnitaryGradient_norm_sq`, `specialUnitaryGamma_le_localSlope_sq` | Verified exponential curves and exact HS gradient coordinates give pointwise actual energy ≤ local metric slope squared, including infinite slopes. |
| `LogSobolev/Unitary/SpecialUnitaryPolynomialExtension.lean` | `specialUnitaryPolynomial_exists_contDiff_extension`, `specialUnitaryPolynomial_locallyLipschitz` | Every polynomial observable has a globally smooth ambient matrix extension and is locally Lipschitz in the actual HS metric. |
| `LogSobolev/Unitary/SpecialUnitaryPolynomialMetricLSI.lean` | `specialUnitaryPolynomial_metric_entropy_sq_le`, `specialUnitaryPolynomial_slopeEnergy_ne_top`, `specialUnitaryPolynomial_entropy_sq_le_slope` | Actual local-slope LSI for all polynomial observables, with finite energy, extended constant `2/N`, and real coefficient `4/N`. The full locally Lipschitz `MetricLSI` is not asserted. |
| `LogSobolev/Unitary/PhaseMap.lean` | `phaseMul_dist_le`, `phaseMap_lipschitz` | The full-line phase map has Lipschitz constant `sqrt(3)` for every positive N; no probability argument is needed. |
| `LogSobolev/Measure/Interval.lean` | `intervalUniform_univ`, `map_intervalUniform` | Normalized Lebesgue measure on the Euclidean subtype `[0,L]` for `L>0`. |
| `LogSobolev/Unitary/ProductDomain.lean` | `phaseDomainMeasure_probability`, `intervalPhaseMap_lipschitz` | The exact interval × SU domain and probability measure, and the restricted map's Lipschitz bound. |
| `LogSobolev/Unitary/CircleDecomposition.lean` | `circleSpecialUnitaryMap_surjective`, `map_circleSpecialUnitaryMap`, `map_circleSpecialUnitaryMap_mul_root` | Continuous surjective scalar homomorphism from Circle × SU to U, full-circle Haar decomposition, and invariance of the SU mixture under central Nth roots. |
| `LogSobolev/Unitary/PhasePeriodicity.lean` | `phaseInterval_root`, `phaseSliceMeasure_periodic`, `phaseAverage_intervalIntegral_translate` | The SU-averaged phase distribution has exactly the paper's short period, and its integral is unchanged by translating the integration window. |
| `LogSobolev/Unitary/PhaseHaar.lean` | `integral_map_intervalPhaseMap`, `map_intervalPhaseMap` | **Unconditional Lemma 16:** the exact normalized interval × SU measure maps to normalized U Haar, for every positive N including N=1. |
| `LogSobolev/Unitary/LSITransfer.lean` | `unitary_metricLSI_of_phaseDomain` | **Conditional:** explicitly assumes source MetricLSI(2/N), then proves target MetricLSI(6/N) using the verified Haar identity and Lipschitz bound. No source LSI is proved. |
| `LogSobolev/Unitary/Observables.lean` | `entryReal_lipschitz`, `entryReal_not_ae_constant`, `unitary_regular` | A meaningful nonconstant test in each positive dimension, and all integrability requirements for every locally Lipschitz U(N) observable. |

The latest approximation infrastructure is unconditional:

* `Measure/EntropyContinuity.lean`: `continuous_entropy_continuousMap`,
  `continuous_entropy_sq_continuousMap`, and
  `tendsto_entropy_sq_of_tendsto_continuousMap` prove entropy convergence for
  uniform limits on compact finite-measure spaces, including zeros.
* `Unitary/SpecialUnitaryPolynomialPullback.lean`:
  `specialUnitaryPolynomial_exists_linear_pullback` proves degree preservation
  for ambient real linear maps preserving SU. Its translation and inversion
  specializations give the polynomial kernel identity needed for convolution.
* `Unitary/SpecialUnitaryPolynomialConvolution.lean`:
  `specialUnitaryPolynomial_exists_convolution` and
  `specialUnitaryPolynomial_exists_averaging` construct an actual degree-`d`
  polynomial from any continuous observable and degree-`d` kernel.
  `specialUnitary_averaging_integral` proves preservation of Haar mean for
  normalized kernels, and `specialUnitary_averaging_le` proves preservation of
  upper bounds for nonnegative normalized kernels. These theorems do not claim
  that such kernels form an approximate identity or control differential energy.

The normalized-power construction is also proved:

* `Measure/PowerKernel.lean`: positive normalization, mass one, a geometric
  tail estimate, and concentration at a unique peak on a compact space with a
  finite full-support measure.
* `Measure/PowerKernelApproximation.lean`:
  `tendsto_integral_powerKernel_smul` gives norm convergence of averages for
  continuous functions with values in any real Banach space.
* `Unitary/SpecialUnitaryPeak.lean`: exact HS distance/trace identities and a
  degree-one nonnegative polynomial uniquely peaked at identity.
* `Unitary/SpecialUnitaryPowerKernel.lean`: actual polynomial normalized-power
  densities of mass one, with concentration for the normalized SU Haar measure.
* `Unitary/SpecialUnitaryPolynomialApproximation.lean`:
  `specialUnitaryPolynomial_exists_uniform_entropy_approximation` proves the
  explicit convolution formula, uniform approximation, and squared entropy
  convergence for every continuous real SU observable. No energy bound for
  the approximants is assumed or claimed.

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
The sum-of-squares Γ₂ argument is now closed: the generator commutes with
invariant derivatives, its actual iterated carré du champ equals the
second-derivative sum, and `Γ₂ ≥ (N/2)Γ` is proved for every smooth real test.
This avoids needing a geometric Ricci theorem for the current operator route.
Haar integration by parts and the integrated Γ₂ identity are now proved.
The entropy-dissipation formula for a supplied positive differentiable family
in the heat direction is also proved. Heat solutions are now constructed on every finite-degree
polynomial-observable space, with the actual PDE, preservation of bounds,
supremum-norm contraction, normalized Haar-mass conservation, and all regularity
needed for entropy and Fisher differentiation. Exponential Fisher decay at rate
`N` is proved, including time zero. Connectedness and zero-energy/kernel constancy are proved.
The polynomial heat orbit now converges in its actual supremum norm to the Haar
mean; limiting entropy is proved zero. This yields the polynomial LSI
`Ent(f²) ≤ (4/N) ∫ Γ(f,f)` with no sign restriction on `f`, after regularizing
squares and taking the limit. The remaining SU step is extension to arbitrary
smooth and locally Lipschitz functions, with verified energy approximation and
control of the approximants' energies by the original local-slope energy. The
pointwise energy-to-slope bound, local Lipschitz regularity of all polynomial
observables, and the finite-energy polynomial metric LSI are now proved. Uniform polynomial
density alone would not establish the energy bound. Consistency across degrees
and general heat extension remain unproved but can be bypassed by extending the
proved polynomial inequality directly. The abstract
`markov-semigroups` class does not eliminate these obligations. Its assumed
entropy decay must not be passed off as a proved curvature criterion.

Once the analytic ingredients exist, `unitary_metricLSI_of_phaseDomain`
already assembles the result with constant `6/N`; `MetricLSI.real_form` removes
the compact regularity side conditions. A verified Herbst argument is a later task.

## Verification and commits

Verification performed on 2026-10-10 with Lean 4.28.0 and the pinned Mathlib
commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`:

* `lake build`: passed for the complete library (3112 dependency/build jobs,
  primarily cached Mathlib artifacts).
* `lake env lean LogSobolev/Examples.lean`: passed; the examples compile as an
  independent client importing the public root module.
* `lake env lean LogSobolev/Audit.lean`: passed. The automated traversal checked
  **783 declarations** in the `LogSobolev` namespace, including definitions,
  instances, and generated auxiliaries. Every transitive axiom was one of
  `propext`, `Classical.choice`, or `Quot.sound`. No `sorryAx` or custom axiom
  was present in those dependency closures.
* The audit also executes 233 `#print axioms` commands, prints the core
  definitions, and prints fully elaborated types for the trace normalization,
  phase-map Lipschitz theorem, U(N) regularity theorem, exact Haar identity,
  conditional final LSI transfer, product entropy chain rule, and SU algebra
  commutator energy, SU curve-velocity characterization, and exponential speed, the real Killing contraction, and the derivative of
  conjugation, the exact Killing coefficient, the real orthonormal energy, the actual SU local
  coordinates, smoothness of the ambient inverse, the actual smooth atlas, the ambient smooth-map criterion, Lie group instance,
  inclusion derivative with exact coordinate-norm preservation, local smooth
  extension, the actual differential-operator commutator, the `N/2` second-order
  bound, the generator-defined carré du champ identity, generator commutation,
  the exact Γ₂ bound, Haar integration by parts, and the integrated Γ₂
  estimate, scalar diffusion chain rule, entropy differentiation with changing
  mass, conditional entropy dissipation, weighted logarithmic Γ₂, the spatial
  Fisher identity, and the conditional Fisher differential inequality with all
  mixed-derivative hypotheses exposed, the actual generator maximum principle,
  bound preservation, the constructed affine and polynomial heat equations,
  polynomial Haar conservation, polynomial Fisher dissipation/decay, actual
  U(N)/SU(N) connectedness, zero-energy/kernel constancy, polynomial equilibrium,
  zero limiting entropy, both polynomial entropy bounds, actual local-slope
  comparison, polynomial ambient extension, and polynomial metric LSI. The elaborated
  metric instances are explicitly Frobenius and `WithLp 2`.
* The recursive audit now shares Lean's core collector visited set across all
  project roots. At milestone `6cb53ac`, an independent-root baseline run and
  the shared-traversal run both passed for 439 declarations and produced
  byte-for-byte identical complete output, including all 92 explicit axiom
  prints at that milestone. That shared run took 1m47s.
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

* `e5cfa1d`: identifies geometric invariant fields with matrix velocities, proves
  local smooth ambient extensions, and proves the actual SU directional
  operators preserve smoothness and obey the commutator identity for every
  smooth test. Full build (2932 jobs), independent examples including a nonzero
  SU(2) operator commutator, and the 425-declaration recursive audit pass.
  The Γ₂ estimate, Haar diffusion/entropy argument, and locally Lipschitz LSI
  remain open; no LSI premise or curvature axiom was introduced.

* `6cb53ac`: dual Killing contraction, the exact `N/2` second-derivative energy
  bound on actual smooth SU tests, and a sum-of-squares operator with its
  generator-defined carré du champ formula and nonnegativity. Build (2935 jobs),
  independent examples with an actual su(2) orthonormal basis and positive
  concrete energy, and both versions of the 439-declaration audit pass.
  The shared audit traversal has identical output to the independent-root
  baseline. Generator commutation, the Γ₂ identity, and LSI remain open.

* `eb986ff`: actual invariant operators on the smooth function space, a reusable
  finite Casimir calculation, proved generator commutation, and the exact
  generator-defined Γ₂ identity and bound `Γ₂ ≥ (N/2)Γ`. Build (2939 jobs),
  independent SU(3) normalization and iterated-generator examples, and the
  465-declaration recursive axiom audit pass. Haar integration by parts,
  diffusion construction, entropy dissipation/convergence, and locally Lipschitz
  LSI remain open; the Γ₂ differential estimate itself is now proved.

* `3c059da`: derivative along actual exponential curves, SU Haar right
  invariance and uniqueness, zero integral of invariant derivatives, and the
  generator Dirichlet identity with symmetry and nonpositivity. Integrated Γ₂
  equals `∫ (Lf)²`, giving the exact `N/2` coercivity estimate. Full build
  (2943 jobs), independent examples including a nonconstant coordinate test,
  and the 482-declaration recursive audit pass; 109 explicit `#print axioms`
  commands use only the three standard foundational axioms. Diffusion
  construction, entropy dissipation/convergence, energy identification, and
  locally Lipschitz LSI remain open.

* `0c520e8`: scalar and logarithmic chain rules for the actual SU generator,
  logarithmic Haar energy identity, and entropy differentiation on compact
  probability spaces with changing-mass correction. For a supplied regular
  positive family in the heat direction, entropy dissipation and nonpositivity
  are proved; the weighted logarithmic Γ₂ estimate is also proved. Build
  (2947 jobs), independent positive nonconstant SU-density and time-dependent
  exponential-family examples, and the 507-declaration recursive audit pass.
  All 121 explicit axiom checks use only standard foundational axioms. Heat
  construction, Fisher time derivative/decay, equilibrium convergence, and the
  locally Lipschitz LSI remain open.

* `d6c3cc6`: mixed logarithmic carré du champ, weighted Γ₂ integration by
  parts, and the unconditional spatial Fisher-variation identity and `−N`
  bound. Differentiation under the integral yields Fisher dissipation and
  `I′ ≤ −N I` for supplied families with explicit time/spatial regularity.
  Full build (2949 jobs), independent SU(3) normalization and time-dependent
  exponential-rescaling examples, and the 523-declaration recursive audit
  pass; 130 explicit axiom checks use only the standard foundational axioms.
  The mixed derivative hypotheses still need to be established for a
  constructed heat family. Heat existence, integrated decay, convergence,
  energy identification, and the locally Lipschitz LSI remain open.

* `60361a5`: necessary second-derivative sign at extrema, a reusable compact
  evolution minimum principle, the actual SU generator maximum principle,
  and preservation of initial heat bounds. Constructs actual heat solutions
  for every affine matrix observable as `c+l(U exp(t ∑ bᵢ²))`, with proved
  initial value, PDE, joint continuity, smooth spatial slices, and forward
  positivity. Build (2956 jobs), independent nonconstant positive SU(2) and
  direct SU(3) PDE examples, and the 552-declaration recursive audit pass.
  All 145 explicit axiom checks use only standard foundational axioms.
  Heat construction beyond affine observables, required general regularity,
  convergence, and the locally Lipschitz LSI remain open.

* `50aba17`: finite-degree polynomial spaces of actual SU matrix observables,
  invariant under the actual derivatives and generator. Constructs their heat
  evolution, with initial value, semigroup law, PDE, positivity, supremum-norm
  contraction, and normalized Haar-mass conservation. Proves mixed regularity,
  entropy and Fisher dissipation for constructed positive polynomial data,
  and integrated Fisher decay `I(Pₜ f) ≤ exp(−Nt) I(f)` for every `t ≥ 0`.
  Full build (2964 jobs), independent nonconstant positive quadratic SU(2)
  examples, and the 657-declaration recursive audit pass. All 160 explicit
  axiom checks use only standard foundational axioms. Polynomial LSI still
  needs vanishing limiting entropy; equilibrium/connectedness and the
  locally Lipschitz approximation and slope identification remain open.

* `c70774f`: connectedness of actual U(N) from finite-spectrum continuous
  functional calculus; a continuous determinant-correcting retraction proves
  connectedness of actual SU(N), including dimension zero. Zero Haar energy
  forces all actual invariant derivatives to vanish; exponential coordinates
  and connectedness then prove that the function equals its Haar mean. The
  smooth Laplacian kernel therefore has only constants. Full build (3094 jobs),
  independent Frobenius-topology connectedness, strictly positive quadratic
  Haar-energy, and SU(3) harmonic-function examples pass. The recursive audit
  covers 682 declarations and all 172 explicit axiom prints use only standard
  foundational axioms. Equilibrium convergence and the polynomial/locally
  Lipschitz LSI remain open; connectedness and kernel constancy no longer do.

* `35e2978`: continuity of polynomial mass, energy and entropy; decay of
  integrated energy; compactness and the zero-energy theorem prove uniform
  heat convergence to the Haar mean and zero limiting entropy. A proved scalar
  dissipation comparison gives `Ent(g) ≤ I(g)/N` on strictly positive polynomial
  densities. Exact regularized-square calculus and the `ε ↓ 0` limit then prove
  `Ent(f²) ≤ (4/N) ∫ Γ(f,f)` for all real polynomial observables with no positivity
  restriction. Full build (3100 jobs), independent concrete density, centered
  quadratic with zeros, equilibrium, and arbitrary-positive-dimension examples
  pass. All 706 declarations pass recursive auditing, and all 183 explicit
  axiom checks use only standard foundational axioms. The full locally Lipschitz
  metric LSI still requires local-slope comparison and energy-controlled
  approximation; it is not claimed by this polynomial result.

* `1e2e435`: scalar derivative–local-slope identity; actual HS isometric
  translation and exponential-curve derivative bounds; explicit gradient
  coordinates with squared norm `Γ`; and the pointwise bound `Γ ≤ localSlope²`.
  Every polynomial has a proved global smooth ambient extension, hence local
  Lipschitz regularity and finite slope energy. The polynomial LSI now uses the
  actual paper local slope, with extended constant `2/N` and real coefficient
  `4/N`. Build (3104 jobs), independent nonconstant finite positive slope-energy,
  centered quadratic, and arbitrary-positive-dimension examples pass. All 723
  declarations pass recursive auditing; all 195 explicit axiom prints use only
  standard foundational axioms. The remaining full-SU obligation is verified
  energy-controlled approximation and entropy convergence for arbitrary locally
  Lipschitz functions; no full `MetricLSI` instance is asserted.

* `e41ed2b`: uniform-norm continuity of entropy and squared entropy on compact
  finite-measure spaces; degree preservation of actual SU polynomials under
  ambient real linear pullback, translations, and inversion; polynomial
  convolution of arbitrary continuous observables, with the averaging formula
  proved by Haar invariance; preservation of Haar mean and upper bounds by
  normalized averaging. Full build (3107 jobs), independent varying-degree
  entropy-limit and continuous-observable convolution examples, and the complete
  recursive audit pass. All 736 project declarations and 208 explicit axiom
  checks use only standard foundational axioms. Kernel concentration and the
  averaged energy bound remain unproved; full SU(N) `MetricLSI` is not asserted.

* `b391128`: normalized powers of the explicit SU peak give nonnegative,
  normalized polynomial kernels concentrating at identity. A reusable Banach-valued
  approximation theorem yields uniform polynomial convolution approximation and
  squared entropy convergence for every continuous SU observable. Build (3112
  jobs), independent normalization and distance-to-identity examples, and the
  full audit pass: 783 declarations, 233 explicit axiom prints, only the three
  standard foundational axioms. The averaged differential-energy bound for
  locally Lipschitz input remains unproved.

The report and README are committed separately after these verified proof
milestones; use `git log --oneline` to see the documentation commit as well.
