# Gaussian LSI: source audit and port

## Sources inspected

The selected source is [AI4SLT](https://github.com/YuanheZ/lean-stat-learning-theory),
commit `d0f506f0a695018265dccb33bcb05e2f5ca1c876` (Lean 4.32.0).
The corresponding implementation in [StatsMLlib](https://github.com/Lean-MoDS/StatsMLlib),
commit `75611ba335ee4ff2fb8b09938f6319d2cbf3d804` (Lean 4.34.0),
has the same authors and Bernoulli approximation strategy. Both repositories
ship Apache-2.0 licenses. The original port targeted Lean 4.28.0; the project now targets Lean 4.34.1.

Actual declarations examined:

- AI4SLT `SLT/GaussianLSI/OneDimGLSICompSmo.lean`,
  `GaussianLSI.gaussian_logSobolev_CompSmo`: real standard Gaussian,
  compact support and `ContDiff ℝ 2 f`, coefficient 2 and ordinary derivative.
- AI4SLT `SLT/GaussianLSI/OneDimGLSI.lean`,
  `GaussianSobolevReal.gaussian_logSobolev_W12_real`: additionally requires
  everywhere differentiability and continuity of the Fréchet derivative.
  The name W12 does not mean that arbitrary weakly differentiable functions are covered.
- StatsMLlib `Probability/Concentration/LogSobolev/GaussianTensorization.lean`,
  `GaussianLSI.gaussian_logSobolev_W12_pi`: L² function and coordinate derivatives,
  everywhere differentiability, continuous partial derivatives, and integrability
  of `g² log(g²)`. The energy is a **sum of squared partial derivatives**,
  not the operator norm for the sup norm on `Fin n → ℝ`.
- StatsMLlib `Probability/Gaussian/Sobolev/Defs.lean`: `MemW12Gaussian` alone
  is a pair of `MemLp` assertions using the totalized `fderiv`; additional
  regularity assumptions on the actual LSI theorem are essential.
- StatsMLlib `Probability/Gaussian/LipschitzConcentration.lean`,
  `lipschitz_cgf_bound`, proves concentration for globally Lipschitz functions
  by mollification (positive dimension and positive global Lipschitz constant).
  It bounds the centered CGF using the global constant; it is not an LSI
  with the integrated local-slope energy. Its supporting
  `Probability/Gaussian/Sobolev/LipschitzMollification.lean` proves smoothness,
  pointwise convergence, and preservation of the global Lipschitz constant.
  These Apache-2.0 components are relevant to a future nonsmooth extension
  but are not needed for the C¹ theorem ported here.
- `markov-semigroups/MarkovSemigroups/Abstract/LogSobolev.lean` contains
  documentation advertising `gross_log_sobolev_gaussian`, but no declaration
  in that file. Its hypercontractivity development has custom axioms
  `gross_lsi_implies_hypercontractive` and `gross_hypercontractive_implies_lsi`.
  It is not imported.
- Mathlib 4.28 has Gaussian measures and characteristic functions but no
  Gaussian LSI theorem found by declaration/source search.

## Attribution and modifications

Files below `LogSobolev/Gaussian/Port` are selective compatibility ports, not
a dependency on either research library. Their path after `Port/` corresponds
to the path after `SLT/` in the pinned AI4SLT revision. Original copyright
and author notices are retained; the repository LICENSE is Apache-2.0.
The Lévy continuity file additionally credits Thomas Zhu and Rémy Degenne
and records its origin in the CLT project.

The ports reuse this repository's existing `LogSobolev.entropy` and
`LogSobolev.TwoPoint.rothaus_lemma`, rather than introducing duplicate
entropy definitions or two-point proofs. Further Lean 4.28 compatibility
changes are recorded in Git. The Lean 4.34.1 migration also reuses the
Apache-2.0 StatsMLlib Gaussian Sobolev files at the revision above; see
[the migration report](UPGRADE_LEAN.md) for paths and API changes.

## Public theorem and mathematical scope

`LogSobolev/Gaussian/LSI.lean` provides:

- `LogSobolev.standardGaussian n`: the product of `n` copies of Mathlib's
  `ProbabilityTheory.gaussianReal 0 1`, transported by the canonical continuous
  linear equivalence to `EuclideanSpace ℝ (Fin n)`. This is a probability measure.
- `LogSobolev.gaussian_entropy_sq_le_of_contDiff`: for every natural `n`,
  including zero, and `f : EuclideanSpace ℝ (Fin n) → ℝ`, assuming
  `ContDiff ℝ 1 f`, `MemLp f 2 γ`, `MemLp (fun x => ‖fderiv ℝ f x‖) 2 γ`,
  and `Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) γ`, proves
  `entropy γ (fun x => f x ^ 2) ≤ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂γ`.
  Square integrability follows from the stated `MemLp` assumption.
- `LogSobolev.gaussian_entropy_sq_le_of_contDiff_of_hasCompactSupport`: the
  same inequality from just `ContDiff ℝ 1 f` and `HasCompactSupport f`.
  All three moment assumptions are proved automatically.
- `LogSobolev.gaussian_entropy_sq_le_slopeEnergy_of_contDiff`: under the
  first theorem's hypotheses, the shared metric-energy formulation
  `ENNReal.ofReal (entropy γ (fun x => f x ^ 2)) ≤ 2 * slopeEnergy γ f`.

The constant is dimension-free and has the requested coefficient **2**.
The norm in the public theorem is Euclidean. In
`LogSobolev/Gaussian/EuclideanEnergy.lean`,
`LogSobolev.sum_sq_apply_single_eq_norm_sq` proves the exact Parseval identity
for real linear functionals on Euclidean space. It is used to identify the
ported coordinate sum of squares with the squared operator norm of `Df`.
No sup-norm operator estimate is substituted for the Euclidean energy.

`LogSobolev/Geometry/LocalSlopeFDeriv.lean` adds the reusable theorems
`LogSobolev.ofReal_norm_fderiv_le_localSlope` and
`LogSobolev.ofReal_integral_norm_fderiv_sq_le_slopeEnergy`. These hold on
general real normed spaces; the integrated statement explicitly assumes
finite derivative energy and does not assume compactness.

The underlying port also proves
`GaussianLSI.gaussian_logSobolev_CompSmo` for real compactly supported C²
functions, and `GaussianSobolevReal.gaussian_logSobolev_W12_real` for real
everywhere differentiable functions with continuous derivative and the two
L² moments. The latter does not require a separate entropy integrability
hypothesis. The finite-dimensional coordinate theorem is
`GaussianLSI.gaussian_logSobolev_W12_pi`; the public Euclidean theorem
uses it with all hypotheses discharged from the stated regularity and moments.

## Proof and compatibility details

The proof establishes Bernoulli-cube LSI from the two-point inequality,
passes to the Gaussian law using characteristic functions and Lévy convergence,
extends the real theorem by cutoff and mollification in the Gaussian L²
function and derivative norms, and tensorizes entropy over finite products.
No Bakry–Émery, hypercontractivity, or Gaussian LSI assumption is imported.

The original Lean 4.28 port used older Lévy convergence and Taylor proofs
from Apache-2.0 AI4SLT revision
`be5d5a8a1a1f46f2ec9502980ff10a39e17e3820`. The Lean 4.34.1 migration
replaces the duplicated Lévy proof with Mathlib’s
`Mathlib.MeasureTheory.Measure.LevyConvergence` and restores the Taylor
argument from the pinned Lean 4.32 AI4SLT source above. Integral and
linear-map API adaptations are recorded in Git.
The obsolete alternate entropy-notation alias is omitted.
`GaussianMeasure.lean` retains only measure definitions, transport, and
coordinate marginals; unused concentration/MGF infrastructure is omitted.

There are no new research-library Lake dependencies. Lean and Mathlib
are upgraded together to 4.34.1. All original
ported copyright notices are retained. Neither source repository has a
separate NOTICE file. The full Apache-2.0 license is in the repository LICENSE.

Ported files (relative to `LogSobolev/Gaussian/Port/`; each corresponds to
`SLT/` in AI4SLT):

- `ConvergenceL1Subseq.lean`
- `EfronStein.lean`
- `GaussianLSI/BernoulliLSI.lean`
- `GaussianLSI/DualEntApp.lean`
- `GaussianLSI/DualityEntropy.lean`
- `GaussianLSI/OneDimGLSI.lean`
- `GaussianLSI/OneDimGLSICompSmo.lean`
- `GaussianLSI/SubAddEnt/Basic.lean`
- `GaussianLSI/SubAddEnt/Decomposition.lean`
- `GaussianLSI/SubAddEnt/Subadditivity.lean`
- `GaussianLSI/TensorizedGLSI.lean`
- `GaussianMeasure.lean`
- `GaussianPoincare/EfronSteinApp.lean`
- `GaussianPoincare/LevyContinuity.lean`
- `GaussianPoincare/Limit.lean`
- `GaussianPoincare/RademacherApprox.lean`
- `GaussianPoincare/TaylorBound.lean`
- `GaussianSobolevDense/Cutoff.lean`
- `GaussianSobolevDense/Defs.lean`
- `GaussianSobolevDense/Density.lean`
- `GaussianSobolevDense/Mollification.lean`

## Remaining extension

This is a complete proof for the stated C¹ class, not a proof for all
locally Lipschitz or weak Sobolev functions. In particular,
`MetricLSI (standardGaussian n) 1` is not asserted. The port's predicates named
`MemW12Gaussian*` express L² moments of totalized classical derivatives; alone
they must not be interpreted as weak Sobolev membership.

The remaining target is precisely:

```lean
theorem gaussian_metricLSI (n : ℕ) : MetricLSI (standardGaussian n) 1
```

Unfolding `MetricLSI`, this quantifies over every locally Lipschitz real
function with integrable square and square-log density and uses the extended
squared local-slope integral, allowing infinite energy.

The bottleneck is analytic: extend weighted cutoff/mollification approximation
from C¹ functions to locally Lipschitz functions, controlling the limiting
Euclidean derivative energy by the original local-slope energy. Gaussian
measure is noncompact and is not translation invariant, so compact Haar-space
regularity cannot simply be reused. A shortest sound route is to establish
that energy-controlled density statement (reusing the inspected Lipschitz
mollification helpers where possible), then use entropy lower
semicontinuity already present in the real extension argument. A weak Sobolev
API additionally needs a genuine weak-derivative definition and the matching
density theorem. The current proof does not hide either step as a hypothesis
of an advertised all-functions LSI.

## Original Lean 4.28 verification

See [the migration report](UPGRADE_LEAN.md) for the subsequent Lean 4.34.1 upgrade.

- Lean **4.28.0**, with the existing pinned Mathlib revision unchanged.
- `lake build`: passed, **3356 jobs**.
- All new modules were also built individually through Lake in dependency order.
- `LogSobolev/ExamplesGaussian.lean` independently exercises the public
  compact-support theorem, probability normalization, dimension zero, the real
  identity function, Euclidean energy, and a concrete smooth bump in every
  dimension. It proves that the dimension-two bump is not Gaussian-almost-
  everywhere constant.
- `LogSobolev/AuditGaussian.lean` selects declarations by their originating
  module, including upstream namespaces, and recursively checks each complete
  dependency closure. The final run passed for **950 declarations** with only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Source scans found no `sorry`, `admit`, custom `axiom`, `unsafe`, or
  `implemented_by` declarations in the Gaussian development or geometry bridge.

`bash scripts/check.sh` completed successfully: the full library build, all
eight independent client files (including the existing unitary examples), and
both recursive audits passed. The expanded `LogSobolev` namespace audit
covered **1079 declarations**. The unitary theorem statements and their
printed axiom lists are unchanged; its audit artifact differs only in the
number of declarations after adding the Gaussian infrastructure.

Audit artifacts with full elaborated theorem statements and key definitions:

- `docs/gaussian-axiom-audit.txt`
- `docs/unitary-axiom-audit.txt`

The first attempted concurrent Lake build was stopped to avoid memory
pressure. Individual sequential Lake builds passed, followed by the complete
check script. `scripts/build-gaussian-sequential.sh` provides optional
low-memory scheduling without changing the library, dependencies, or proofs.

## Git milestones

- `3315813`: compactly supported C² real Gaussian LSI, with its approximation
  chain compiled and its main theorem's transitive axioms checked.
- `1185375`: dimension-free C¹ Gaussian theorem on Euclidean space, automatic
  compact-support integrability, shared slope-energy bounds, independent
  examples, and the successful full build and recursive audits.

The prior completed U(N) proof (`8ea00af`, with report `aad1e98`) is preserved;
no existing unitary proof file was changed by this extension.
