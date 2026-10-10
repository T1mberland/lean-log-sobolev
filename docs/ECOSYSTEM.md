# Source audit (2026-10-10)

This is a declaration-level source inspection, not a certification of whole
external libraries. External projects were cloned into `/tmp/lsi-survey`, their
Lean sources and manifests inspected, and **none was added as a dependency**.
Only Mathlib is imported by this project. Negative search results below mean
“not found in the inspected checkout”, not a claim of mathematical impossibility.

## Versions inspected

| Project | Commit | Lean |
|---|---|---|
| [Mathlib current](https://github.com/leanprover-community/mathlib4/tree/a02a63c2100af866343c74550041885f8f39f099) | `a02a63c2100af866343c74550041885f8f39f099` | 4.35.0-rc4 |
| Mathlib used here | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` | 4.28.0 |
| [StatsMLlib](https://github.com/Lean-MoDS/StatsMLlib/tree/75611ba335ee4ff2fb8b09938f6319d2cbf3d804) | `75611ba335ee4ff2fb8b09938f6319d2cbf3d804` | 4.34.0 |
| [lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory/tree/d0f506f0a695018265dccb33bcb05e2f5ca1c876) | `d0f506f0a695018265dccb33bcb05e2f5ca1c876` | 4.32.0 |
| [statlean4](https://github.com/statopia/statlean4/tree/dd2c4bbc72b7c643e62985d77c84755b31aec9f5) | `dd2c4bbc72b7c643e62985d77c84755b31aec9f5` | 4.28.0-rc1 |
| [markov-semigroups](https://github.com/mrdouglasny/markov-semigroups/tree/0b5dd80ad918f7e8ab23bb2fac5eb9c7d373a795) | `0b5dd80ad918f7e8ab23bb2fac5eb9c7d373a795` | 4.30.0 |
| [Lean-QIT](https://github.com/QuAIR/Lean-QIT/tree/15a0a5ef13e5824327e0850ea896e472366287af) | `15a0a5ef13e5824327e0850ea896e472366287af` | 4.34.0 |
| [lean-quantum](https://github.com/Hayata-Yamasaki-Group/lean-quantum/tree/bf1c4f6aaec84948f1a1c76c0728432813404a0f) | `bf1c4f6aaec84948f1a1c76c0728432813404a0f` | 4.29.0-rc6 |

The external manifests pin different Mathlib revisions. There is no justified
drop-in import across these versions. This project keeps the installed 4.28.0
toolchain and pins its matching Mathlib release. Its ignored `.lake/packages`
initially reuses an existing local cache; this is not a declared dependency.
A fresh checkout can obtain the exact dependencies from `lake-manifest.json`.

## Reusable declarations and their actual scope

### Mathlib

* `LinearAlgebra/UnitaryGroup.lean`: `Matrix.unitaryGroup`,
  `Matrix.specialUnitaryGroup`, group structures, determinant and membership
  lemmas. SU is already defined; no replacement matrix group is needed.
* `Analysis/Matrix/Normed.lean`: `Matrix.frobeniusNormedAddCommGroup`,
  `Matrix.frobeniusNormedSpace`, `Matrix.frobenius_norm_def`, activated by
  `Matrix.Norms.Frobenius`. This is the unnormalized sum-of-squares norm.
* `MeasureTheory/Measure/Haar/Basic.lean` and `Unique.lean`:
  `Measure.haarMeasure`, `haarMeasure_self`,
  `isMulInvariant_eq_smul_of_compactSpace`,
  `isHaarMeasure_eq_of_isProbabilityMeasure`.
  The hypotheses include the appropriate topological group and Borel structures;
  using `⊤` as the positive compact normalizing set requires compactness.
* `Topology/EMetricSpace/Lipschitz.lean`: `LocallyLipschitz` means a finite
  Lipschitz constant on a neighborhood of every point.
* `Analysis/Normed/Lp/ProdLp.lean`: `WithLp 2` and `prod_dist_eq_add` give the
  genuine L² product metric.
* `Analysis/Convex/Integral.lean` and `SpecialFunctions/Log/NegMulLog.lean`
  supply integral Jensen and continuity of `x * log x`, including at zero.

Searches in both the pinned and current Mathlib checkouts found no matching
general metric-slope LSI, SU(N) LSI, interval LSI, or Bakry–Émery-to-LSI theorem.
The ordinary Sobolev inequality and topological/binary entropy files are not
substitutes for these results. No Ricci-based analytic criterion suitable for
this task was found.

### StatsMLlib and lean-stat-learning-theory

Inspected `StatsMLlib/Probability/Entropy/Basic.lean` and its earlier counterpart
`SLT/GaussianLSI/Entropy.lean`. Both define `LogSobolev.entropy` by the required
integral formula; `entropy_nonneg` requires nonnegativity a.e., integrability of
the function, and integrability of its log moment. We port the small compatible
definition/API, with attribution, rather than introduce another entropy convention.

The product chain rule and marginal log-integrability arguments from
`Conditional/Decomposition.lean` and `Conditional/Subadditivity.lean` are now
adapted in `LogSobolev/Measure/ProductEntropy.lean` to heterogeneous binary
products. These compiled proofs do not supply metric-LSI tensorization.

`Probability/Entropy/Conditional/Subadditivity.lean:entropy_subadditive` proves
an entropy bound for finite independent products. It assumes measurability,
nonnegativity a.e., integrability, and log-moment integrability. This is a useful
reference, but it is not metric-slope tensorization on two different manifolds.
The project now proves heterogeneous binary subadditivity for continuous
nonnegative densities on compact metric probability spaces in
`ProductEntropySubadditivity.lean`. Its real Gibbs argument avoids importing
the external extended-real variational API; positive regularization handles zeros.

`Probability/Concentration/LogSobolev/GaussianTensorization.lean:
gaussian_logSobolev_W12_pi` (and `SLT/GaussianLSI/TensorizedGLSI.lean`) assumes
`MemW12GaussianPi`, differentiability, continuous coordinate derivatives, and an
integrable squared-function log moment. Its energy is a sum of squared partial
derivatives, and its measure is the standard product Gaussian. It does not
establish the interval or SU(N) result. The positive-density two-point upper bound in
`Probability/Concentration/LogSobolev/TwoPoint.lean` is now ported (with attribution)
to `LogSobolev/Analysis/TwoPointEntropy.lean`; unused lower-bound arguments were
omitted, and zero/signed cases were added by verified limits. This requires no
external dependency or toolchain upgrade. The compact-support and one-dimensional
Gaussian LSI files also have substantial, concrete analytic proofs worth reusing
in a future Gaussian route. No full dependency-closure audit of these external
theorems was run, since they are not imported here.

### statlean4

`Statlean/Entropy/Basic.lean:SatisfiesLSI` is a real-line C¹ derivative inequality
with coefficient `c` (rather than `2c`), and requires L² membership of the function
and derivative plus continuity of the derivative. `TensorizationLSIAt` concerns
standard Gaussian products. The early `tensorization_lsi` theorem takes a
tensorization hypothesis, but the later `tensorization_lsi_core` in
`Entropy/LogSobolev.lean` actually supplies a proof for `c ≥ 0`; these must not be
confused. Its Gaussian specialization still needs adaptation to metric slopes
and does not solve the SU(N) analytic step. Source comments also discuss
totalized Bochner integrals; our interfaces retain log-integrability explicitly.

### markov-semigroups: trust-boundary findings

Inspected `Abstract/DirichletForm.lean`, `Diffusion/CarreDuChamp.lean`,
`Abstract/Concentration.lean`, `Abstract/Hypercontractivity.lean`, and searched
the full Lean source tree for custom axioms and relevant instances.

`BakryEmerySpace` **assumes** `semigroup_entropy_sq_decay_bound` and
`semigroup_entropy_sq_ergodic`, as well as gradient decay, core preservation,
and other semigroup properties. `BakryEmerySpace.satisfiesLogSobolev` takes the
limit of that assumed entropy decay estimate. The theorem body is a legitimate
abstract implication; it is not a construction of a diffusion or a proof of
the entropy estimate from Ricci curvature. Instantiating this class for SU(N)
would still require proving those central analytic statements.

Actual custom axiom declarations include:

* `Abstract/Concentration.lean`: `herbst_mgf_bound`, `poincare_of_lsi`.
* `Abstract/Hypercontractivity.lean`: `stroock_varopoulos`,
  `gross_lsi_implies_hypercontractive`, `gross_hypercontractive_implies_lsi`.
* `DobrushinZegarlinski/GlobalLSI.lean`: `zegarlinski_lsi_inequality`.
* Other declarations exist in smoothing, matrix resolvent, covariance and
  work-in-progress files.

`Abstract/LogSobolev.lean` in this snapshot contains a descriptive block comment,
not the advertised theorem implementations. README status alone is insufficient.
No result from this project is a foundation of our development.

### Quantum projects

`QIT/Symmetry/UnitaryTwirl.lean` constructs compactness and
`unitaryHaarMeasure` on `Matrix.unitaryGroup`, normalizing `haarMeasure` on `⊤`.
Its probability and left-invariance proofs are concrete. These declarations
confirm the same economical Mathlib Haar construction used here.

`Quantum/QuantumEntropy/HaarUnitary.lean` constructs `haarUnitary` on unitary
operators of a finite-dimensional Hilbert space, using the operator norm to
prove compactness. Its quantum relative-entropy and Haar-twirling results do
not directly give classical metric LSI. Neither inspected project supplied the
SU(N) Ricci calculation or the short-interval Haar decomposition needed here.

## Source proof

[Meckes–Meckes, Appendix, Theorem 15 and Lemma 16](https://arxiv.org/pdf/1210.2681)
uses a short interval times SU(N), entropy tensorization, and a Lipschitz
pushforward. The interval and SU constants are `2/N`; the phase map has
Lipschitz constant `sqrt(3)`, giving `C = 6/N` in the `2C` convention. N=1 uses
the circle inequality. The SU step cites a curvature criterion and the interval
step cites the sharp circle inequality: these citations are not Lean proofs.
The metric estimate is a useful independently provable milestone.


## Locally Lipschitz interval extension

The pinned Mathlib declarations `LipschitzOnWith.absolutelyContinuousOnInterval`,
`AbsolutelyContinuousOnInterval.intervalIntegrable_deriv`, and
`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` now supply the actual
FTC step in `LipschitzIntervalEnergy.lean`. The proof establishes squared
integrability using the Lipschitz derivative bound, then reuses the dyadic
entropy limit. `IntervalMetricLSI.lean` proves the full locally Lipschitz
normalized-interval LSI with constant `L²/8`. `DimensionOneLSI.lean` combines it
with the previously verified Haar decomposition to prove U(1) constant `6`.
No external dependency or assumed analytic criterion was added.


## Simultaneous phase differentiation

`Mathlib/Analysis/Calculus/Rademacher.lean` in the pinned version proves
`LipschitzWith.ae_differentiableAt` for finite-dimensional real normed spaces
under additive Haar measure. The new `SpecialUnitaryPolynomialFamily.lean`
applies it to a curve from the real line into the actual finite-degree SU
polynomial space with its induced uniform norm. A proved positive-kernel
contraction supplies the Lipschitz hypothesis. This avoids any assumption
about Rademacher under manifold charts or about exceptional sets uniform in
an arbitrary family of scalar functions. The joint evaluation derivative is
proved separately by expansion in `Module.finBasis`.
