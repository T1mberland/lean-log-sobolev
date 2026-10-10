# Formalization report: logarithmic Sobolev inequality on U(N)

## Main result

`LogSobolev.unitary_metricLSI` in
[`UnitaryLSI.lean`](../LogSobolev/Unitary/UnitaryLSI.lean) proves Theorem 15 of
[Meckes–Meckes, *Spectral Measures of Powers of Random Matrices*, Appendix](https://arxiv.org/pdf/1210.2681):

```lean
theorem unitary_metricLSI (N : ℕ) (hN : 0 < N) :
    MetricLSI (unitaryHaar (Fin N)) (6 / (N : NNReal))
```

`unitary_entropy_sq_le_of_locallyLipschitz` gives the real form:

```lean
theorem unitary_entropy_sq_le_of_locallyLipschitz (N : ℕ) (hN : 0 < N)
    {f : Matrix.unitaryGroup (Fin N) ℂ → ℝ} (hf : LocallyLipschitz f) :
    entropy (unitaryHaar (Fin N)) (fun U => f U ^ 2) ≤
      (12 / (N : ℝ)) *
        ∫ U, (localSlope f U).toReal ^ 2 ∂unitaryHaar (Fin N)
```

These statements cover **every positive dimension, including N=1**, and every
locally Lipschitz real observable. They impose no smoothness, polynomial,
semigroup, curvature, LSI, or energy-control hypothesis on the input.
`unitary_regular` proves square, square-log, and squared-local-slope integrability.
Continuity supplies measurability; the local slope is Borel measurable and finite,
and the total slope energy is finite. Thus the real-valued integral is substantive,
not a zero obtained from totalizing a nonintegrable expression.

An intermediate theorem, `unitary_entropy_sq_le_pi_of_locallyLipschitz`, proves
the stronger real coefficient `π²/N`; the requested coefficient follows from
`π² ≤ 12`. No optimality claim is made.

## Measure, group, metric, and entropy audit

* **Group:** Mathlib's `Matrix.unitaryGroup (Fin N) ℂ`, consisting of actual
  finite-dimensional unitary matrices. SU uses `Matrix.specialUnitaryGroup`.
* **Measure:** `unitaryHaar n = Measure.haarMeasure ⊤`, with proved
  `Measure.IsHaarMeasure`, `IsProbabilityMeasure`, and right invariance.
  `map_intervalPhaseMap` proves the exact normalized interval × SU Haar
  pushforward identity, using group invariance and Haar uniqueness.
* **Metric:** all group statements elaborate under
  `open scoped Matrix.Norms.Frobenius`. The distance is the ambient matrix
  Frobenius norm of the difference. `frobenius_norm_sq_eq_trace` proves
  `((‖A‖² : ℝ) : ℂ) = Matrix.trace (star A * A)`, with no division by N.
* **Slope:** `localSlope` is the extended-nonnegative limsup of
  `dist (f y) (f x) / dist y x` as `y → x`.
  `localSlope_eq_limsup_nhdsNE` proves agreement with the punctured convention.
  The real theorem uses `toReal` only after finiteness is proved for locally
  Lipschitz functions. It uses the chordal HS metric required in the paper.
* **Entropy:** `entropy μ g = ∫ g log g - (∫ g) log (∫ g)`, with the standard
  real-log convention at zero. Signed functions and zeros are permitted in `f`.
* **Constant:** `MetricLSI μ C` uses `Ent(f²) ≤ 2 C slopeEnergy`; hence `C=6/N`
  corresponds exactly to the real coefficient `12/N`.
* **Endpoints:** the normalized measure is on the closed Euclidean subtype
  `[0,L]`. Verified Lebesgue restriction identities handle endpoints; almost-
  everywhere differentiation transfers to this actual normalized measure.
  Division by the dimension is used only with explicit `0 < N`.

## Proof route

The formal proof uses a different energy assembly from the paper's suggested
sharp-interval-plus-global-Lipschitz argument. Every ingredient below is proved.

1. **SU(N):** construct the smooth matrix SU atlas and invariant derivatives;
   prove the exact HS algebraic normalization and `Γ₂ ≥ (N/2) Γ`; construct
   finite-degree polynomial heat flow; prove entropy dissipation, equilibrium,
   and SU polynomial LSI with real coefficient `4/N`. Positive polynomial
   convolution and a proved slope estimate extend this to all locally
   Lipschitz SU observables. No Bakry–Émery criterion is assumed.
2. **Interval:** two-point entropy, dyadic weighted path energy, and a verified
   continuum limit prove coefficient `L²/4`. Absolute continuity and the
   fundamental theorem of calculus give the full locally Lipschitz extension.
   The LSI constant is `L²/8`; the sharp constant `L²/π²` is not needed.
3. **Regularization:** average a U(N) function against the actual normalized SU
   polynomial power kernel. These continuous U(N) functions converge uniformly
   and in squared entropy. At each phase, the average lies in a fixed finite-
   dimensional SU polynomial space; its phase curve is Lipschitz in uniform
   norm. Mathlib's proved Rademacher theorem gives a simultaneous derivative
   almost everywhere. Finite basis expansion proves joint differentiation.
4. **Exact combined energy:** for phase speed `c` and traceless generator `A`,
   the combined U(N) curve has squared speed `‖A‖² + 2c²`. Testing with the SU
   gradient and `c = p′(t)(U)/2`, the proved derivative-of-an-average estimate
   gives `Q = p′(t)(U)²/2 + Γ_SU(p(t),p(t))(U)` bounded by averaged original
   squared slopes. Haar decomposition and invariance give integrated
   `Q ≤ slopeEnergy(U Haar,f)` without a constant loss.
5. **Slice entropy:** binary entropy subadditivity, the interval derivative
   bound, and SU polynomial LSI bound product entropy by
   `(L²/4) ∫ p′² + (4/N) ∫ Γ`. All joint measurability, integrability, and
   Fubini requirements are proved. At `L = π sqrt(2/N)`, this is at most
   `(π²/N) ∫ Q`.
6. **Limit:** entropy transport identifies product entropy with U Haar entropy.
   The integrated energy bound and proved entropy convergence yield coefficient
   `π²/N`, and then `12/N`, for the original locally Lipschitz function.

This route works also for N=1. The earlier independent U(1) theorem is retained.
General metric-space tensorization, the sharp interval constant, and the optional
Herbst/concentration corollary are not asserted; none is needed for the completed
main theorem. General entropy subadditivity, Lipschitz pushforward, isometric
transport, and interval scaling remain reusable components.

## Principal sources

| Module under `LogSobolev/` | Main result |
|---|---|
| `Unitary/UnitaryLSI.lean` | `unitary_metricLSI`, `unitary_entropy_sq_le_of_locallyLipschitz`, stronger π² coefficient |
| `Unitary/SpecialUnitaryLSI.lean` | Full locally Lipschitz SU(N) LSI, constant `2/N` |
| `Analysis/IntervalDerivativeLSI.lean` | Interval LSI for an a.e. derivative representative |
| `Geometry/IntervalMetricLSI.lean` | Full locally Lipschitz interval LSI, constant `L²/8` |
| `Unitary/SpecialUnitaryPolynomialFamilyRegularity.lean` | Joint measurability, continuity, and derivative-square integrability |
| `Unitary/PolynomialPhaseEntropy.lean` | Weighted slice-entropy bound |
| `Unitary/PhaseEntropyEnergy.lean` | Product entropy bounded by `(π²/N)` times combined energy |
| `Unitary/PhaseEntropyTransport.lean` | Entropy transported through actual Haar decomposition |
| `Unitary/UnitaryPhaseIntegratedEnergy.lean` | Constructed polynomial phase approximants with integrated energy bound |
| `Unitary/UnitarySUConvolution.lean` | Uniform and squared-entropy approximation on U(N) |
| `Unitary/PhaseHaar.lean` | Actual Haar pushforward, including N=1 |
| `Unitary/HilbertSchmidt.lean`, `Unitary/Haar.lean` | Exact normalization, actual group, normalized Haar |
| `Geometry/CompactRegularity.lean`, `Unitary/Observables.lean` | Integrability, finite energy, and nonconstant admissible tests |
| `AuditUnitary.lean`, `ExamplesUnitary.lean` | Recursive axiom/statement audit and independent final clients |

## Reproducibility and ecosystem

Lean is pinned to 4.28.0; Mathlib is pinned to
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. No external research library is a
dependency. [ECOSYSTEM.md](ECOSYSTEM.md) records declaration-level inspection,
versions, compatibility, and the custom-axiom findings for `markov-semigroups`.
A compatible two-point entropy port from StatsMLlib is attributed in its source;
its dependency closure is audited with the rest of this project.

Run `bash scripts/check.sh`. This builds the root library, compiles all seven
independent example files, and recursively audits every project declaration.
The audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
Full elaborated final statements and the entropy, measure, slope, and LSI
definitions are recorded in `unitary-axiom-audit.txt`.

Earlier milestone reports are preserved in
[DEVELOPMENT_HISTORY.md](DEVELOPMENT_HISTORY.md); their open-goal statements
are historical. The detailed SU proof remains in [SU_LSI.md](SU_LSI.md).

## Final verification results

The final proof is committed as **`8ea00af`**.

* `bash scripts/check.sh` exited successfully after the final edits.
* `lake build` passed: **3199 jobs**.
* All seven independent clients compiled: `Examples.lean`,
  `ExamplesInterval.lean`, `ExamplesProductEntropy.lean`,
  `ExamplesIntervalMetric.lean`, `ExamplesPhasePolynomial.lean`,
  `ExamplesPhaseEnergy.lean`, and `ExamplesUnitary.lean`.
* The recursive audit passed for **1017 LogSobolev declarations**, including
  their full dependency closures. All 16 selected `#print axioms` checks use
  only **`propext`, `Classical.choice`, and `Quot.sound`**.
* Full elaborated statements show the actual matrix subtype and
  `Matrix.frobeniusNormedRing` metric instance. The final metric theorem has
  only `N` and `0<N`; the real theorem additionally takes the function and
  its local Lipschitz proof. The printed measure, entropy, slope, energy, and
  LSI definitions match the conventions audited above.
* Final examples verify the arbitrary-N theorem, N=1, a nonsmooth U(2)
  distance observable, a U(3) matrix coordinate that is not Haar-a.e. constant,
  all integrability and measurability obligations, finite energy, normalized
  Haar, the exact distance formula, and the HS trace normalization.
* The source scan found no `sorry`, `admit`, custom `axiom`, `unsafe`
  declaration, or kernel-check bypass. `git diff --check` passed.
* The Mathlib checkout is clean and matches the pinned revision. No dependency
  was added or changed for the final proof.

Audit artifact: [`unitary-axiom-audit.txt`](unitary-axiom-audit.txt).
There are no remaining proof obligations for the stated U(N) theorem.

## Git milestones

| Commit | Completed result |
|---|---|
| `1e46e9a` | Full locally Lipschitz SU(N) LSI |
| `3680ea6` | Two-point/dyadic construction and C¹ interval LSI |
| `0f8e487` | Full locally Lipschitz interval LSI and independent U(1) proof |
| `357ce62` | Polynomial phase regularization, joint derivative, orthogonality |
| `85a8c1e` | Integrated combined energy bound and U(N) entropy approximation |
| **`8ea00af`** | **Slice entropy and complete U(N) Theorem 15, with final audit and clients** |

Documentation is committed separately after the final proof; `git log --oneline`
identifies that report commit. All earlier completed reusable modules are retained.
