# Gaussian and unitary logarithmic Sobolev inequalities in Lean 4

**Theorem 15 of Meckes–Meckes is proved for all locally Lipschitz real functions
and every positive dimension, including N=1.**

The theorem uses Mathlib's actual matrix unitary group, normalized Haar
probability, and the **unnormalized Hilbert–Schmidt metric**. There are no
assumed logarithmic Sobolev or curvature criteria in its dependency closure.

```lean
import LogSobolev
open MeasureTheory LogSobolev
open scoped Matrix.Norms.Frobenius NNReal

example (N : ℕ) (hN : 0 < N) :
    MetricLSI (unitaryHaar (Fin N)) (6 / (N : NNReal)) :=
  unitary_metricLSI N hN

example (N : ℕ) (hN : 0 < N)
    (f : Matrix.unitaryGroup (Fin N) ℂ → ℝ) (hf : LocallyLipschitz f) :
    entropy (unitaryHaar (Fin N)) (fun U => f U ^ 2) ≤
      (12 / (N : ℝ)) * ∫ U, (localSlope f U).toReal ^ 2 ∂unitaryHaar (Fin N) :=
  unitary_entropy_sq_le_of_locallyLipschitz N hN hf
```

`unitary_regular` establishes square, square-log, and squared-slope integrability.
Independent examples include nonsmooth distance functions and a matrix coordinate
proved not to be Haar-almost-everywhere constant.

The proof constructs SU polynomial heat flow and proves its entropy inequality;
uses a proved interval inequality; and regularizes U(N) functions by positive SU
convolution. Exact central/traceless orthogonality controls the combined phase
and SU energy. The resulting real coefficient is `π²/N`, which implies `12/N`.
The proof includes the almost-everywhere differentiation and entropy-limit steps.

Reusable infrastructure includes entropy subadditivity, Lipschitz pushforward,
local-slope measurability and integrability, exact Haar decomposition, the full
SU(N) LSI with constant `2/N`, and an interval LSI with constant `L²/8`.
General metric tensorization and the sharp interval constant are not claimed.

## Gaussian LSI

`LogSobolev.gaussian_entropy_sq_le_of_contDiff` proves the sharp, dimension-free
Gaussian inequality `Ent(f²) ≤ 2 ∫ ‖Df‖²` on `EuclideanSpace ℝ (Fin n)`,
including dimension zero. It assumes `C¹` regularity, Gaussian L² moments of
`f` and its derivative norm, and integrability of `f² log(f²)`.
The compact-support corollary proves these integrability conditions automatically.

The proof selectively ports the Apache-2.0 AI4SLT development,
reuses this library's entropy and two-point inequality, and identifies the
coordinate sum of squares with the **Euclidean** derivative norm. A corollary
uses the same `slopeEnergy` as the unitary API. An all-locally-Lipschitz Gaussian
`MetricLSI` theorem is **not** claimed. See [the Gaussian report](docs/GAUSSIAN.md)
for precise scope, source attribution, verification, and remaining work.

## Herbst argument and concentration

The shared Herbst proof gives centered sub-Gaussian MGF bounds and upper,
lower, and two-sided concentration for globally Lipschitz real functions.
The variance proxies for an `L`-Lipschitz observable are `6 L²/N` on U(N),
`2 L²/N` on SU(N), and `L²` on Euclidean standard Gaussian space. The Gaussian
result includes nonsmooth functions, dimension zero, and L=0; all moment
conditions are proved. The Haar results include N=1.

`gaussian_measure_abs_ge_le` gives `P(|f - E f| ≥ r) ≤ 2 exp(-r²/(2 L²))`.
`unitary_measure_abs_ge_le` gives the corresponding Haar bound with exponent
`-N r²/(12 L²)`. The generic API is `MetricLSI.hasSubgaussianMGF_of_compact`
and `MetricLSI.measure_abs_ge_le`; the noncompact MGF transfer has explicit
exponential-moment hypotheses. See [the concentration report](docs/CONCENTRATION.md)
for theorem names, proof, source licenses, and verification.

## Build and verify

Lean 4.34.1 and matching Mathlib v4.34.1 are pinned in the toolchain and manifest.

```sh
lake exe cache get
bash scripts/check.sh
```

On memory-constrained machines, run `python3 scripts/build-sequential.py`
first to compile local modules in dependency order.

The check script builds the library, independently compiles nine client files,
and audits the transitive dependencies of exported project declarations,
including their private proof dependencies. Only
`propext`, `Classical.choice`, and `Quot.sound` are allowed. It saves the audit
and full elaborated final theorem statements in `docs/unitary-axiom-audit.txt`
and `docs/gaussian-axiom-audit.txt`. The concentration audit also checks every
visible project declaration by originating module, including upstream namespaces,
and saves `docs/concentration-axiom-audit.txt`.

## Sources and report

* [Lean 4.34.1 migration](docs/UPGRADE_LEAN.md)
* [Unitary theorem](LogSobolev/Unitary/UnitaryLSI.lean)
* [Gaussian theorem](LogSobolev/Gaussian/LSI.lean)
* [Gaussian source audit and report](docs/GAUSSIAN.md)
* [Independent Gaussian examples](LogSobolev/ExamplesGaussian.lean)
* [Unitary proof report, validation, and commits](docs/REPORT.md)
* [Declaration-level ecosystem and compatibility inspection](docs/ECOSYSTEM.md)
* [Detailed SU proof](docs/SU_LSI.md)
* [Independent final examples](LogSobolev/ExamplesUnitary.lean)
* [Reference paper, Appendix, Theorem 15](https://arxiv.org/pdf/1210.2681)

No external research library is added as a dependency. Selectively ported
StatsMLlib and AI4SLT proofs retain their Apache-2.0 notices and attribution.
Historical milestone
reports are preserved in `docs/DEVELOPMENT_HISTORY.md`.
