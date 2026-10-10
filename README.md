# Logarithmic Sobolev infrastructure for U(N)

**Status: verified partial development. Theorem 15 is not proved.**

This Lean 4.28.0 / Mathlib project develops components for the logarithmic
Sobolev inequality in [Meckes–Meckes](https://arxiv.org/pdf/1210.2681).
It uses Mathlib's actual matrix unitary and special unitary groups and the
**unnormalized Frobenius (Hilbert–Schmidt) metric**.

Proved components include:

* Entropy transport, the product entropy chain rule with proved marginal
  log-integrability, and an explicit-energy LSI transport/scaling API.
* The upper local metric slope: agreement with the punctured limsup,
  finiteness for locally Lipschitz functions, Borel measurability, a Lipschitz
  chain bound, and invariance under domain isometries.
* Metric-LSI Lipschitz pushforward with the squared Lipschitz factor.
* Square, log-moment and slope-energy integrability for **all locally Lipschitz
  functions** on compact metric spaces, and the finite real-valued LSI form.
* Exact Hilbert–Schmidt trace normalization and unitary multiplication isometries
  at the norm level.
* Compactness and Haar probability on U(N) and SU(N).
* The normalized interval and its L² product with SU(N).
* The paper's phase map into U(N), with the `sqrt(3)` Lipschitz bound.
* **The exact short-interval Haar decomposition (Lemma 16)** for every positive N,
  including N=1, proved from Haar invariance and periodic integration.
* Conditional final transfer from an explicitly assumed product LSI with
  constant `2/N` to U(N) with constant `6/N`.
* A 1-Lipschitz diagonal coordinate that is not Haar-a.e. constant in every
  positive dimension.

No LSI for U(N), SU(N), the interval, or the circle is claimed. In particular,
the transfer theorems take an explicit source LSI assumption; no such source
inequality is supplied for these spaces.

## Build and audit

```sh
lake exe cache get
bash scripts/check.sh
```

`scripts/check.sh` builds the library and independently compiles the examples
and recursive axiom audit. The audit rejects every axiom except `propext`,
`Classical.choice`, and `Quot.sound`, in the transitive dependencies of every
declaration in the `LogSobolev` namespace.

When using the matrix metric, write:

```lean
import LogSobolev
open LogSobolev
open scoped Matrix.Norms.Frobenius

example : LipschitzWith ⟨Real.sqrt 3, Real.sqrt_nonneg 3⟩ (intervalPhaseMap 2) :=
  intervalPhaseMap_lipschitz 2 (by decide)
```

See [the source audit](docs/ECOSYSTEM.md) for inspected versions, actual
external theorem assumptions and the `markov-semigroups` trust-boundary findings.
See [the mathematical report](docs/REPORT.md) for the exact scope and open goals.

## Layout

`Measure/` holds entropy, explicit-energy LSI, and normalized interval measure.
`Geometry/` holds the metric slope, its measurability and integrability, and
metric-LSI transport. `Unitary/` holds matrix normalization, Haar constructions,
the phase map and nonconstant observables. `Audit.lean` and `Examples.lean` are
independent validation files.

The small entropy compatibility port is attributed in its source file. No
external research library is imported; Mathlib is pinned in the manifest.
