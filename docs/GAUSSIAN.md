# Gaussian LSI: source audit and port

## Sources inspected

The selected source is [AI4SLT](https://github.com/YuanheZ/lean-stat-learning-theory),
commit `d0f506f0a695018265dccb33bcb05e2f5ca1c876` (Lean 4.32.0).
The corresponding implementation in [StatsMLlib](https://github.com/Lean-MoDS/StatsMLlib),
commit `75611ba335ee4ff2fb8b09938f6319d2cbf3d804` (Lean 4.34.0),
has the same authors and Bernoulli approximation strategy. Both repositories
ship Apache-2.0 licenses. This project remains on Lean 4.28.0.

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
changes are recorded in Git.
