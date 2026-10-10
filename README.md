# Logarithmic Sobolev inequality on U(N) in Lean 4

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
General metric tensorization, the sharp interval constant, and the optional
concentration corollary are not claimed.

## Build and verify

Lean 4.28.0 and Mathlib are pinned in the toolchain and manifest.

```sh
lake exe cache get
bash scripts/check.sh
```

The check script builds the library, independently compiles seven client files,
and audits the transitive dependencies of every project declaration. Only
`propext`, `Classical.choice`, and `Quot.sound` are allowed. It saves the audit
and full elaborated final theorem statements in `docs/unitary-axiom-audit.txt`.

## Sources and report

* [Main theorem](LogSobolev/Unitary/UnitaryLSI.lean)
* [Final mathematical report, validation, and commits](docs/REPORT.md)
* [Declaration-level ecosystem and compatibility inspection](docs/ECOSYSTEM.md)
* [Detailed SU proof](docs/SU_LSI.md)
* [Independent final examples](LogSobolev/ExamplesUnitary.lean)
* [Reference paper, Appendix, Theorem 15](https://arxiv.org/pdf/1210.2681)

No external research library is imported. The small StatsMLlib entropy
compatibility port retains attribution in its source. Historical milestone
reports are preserved in `docs/DEVELOPMENT_HISTORY.md`.
