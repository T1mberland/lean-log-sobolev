# Herbst argument and concentration

The library proves centered Gaussian concentration from its logarithmic Sobolev
inequalities. Every result below is a theorem with a checked proof, not an axiom
or an assumed concentration property. Constants use `Ent(f²) ≤ 2 C ∫ |∇f|²`.

## Public statements and exact scope

For an observable `f`, write `m = ∫ f dμ`. For every real `t`, nonnegative
threshold `r`, and nonnegative Lipschitz constant `K`, the results provide

```
∫ exp(t (f - m)) dμ ≤ exp(v t²/2),
μ {f - m ≥ r} ≤ exp(-r²/(2v)),
μ {m - f ≥ r} ≤ exp(-r²/(2v)),
μ {|f - m| ≥ r} ≤ 2 exp(-r²/(2v)).
```

Here `μ.real` is the real value of the actual event measure. In Lean the MGF
statement uses Mathlib's `ProbabilityTheory.HasSubgaussianMGF`. Its two fields
are exponential integrability and the displayed MGF inequality; it does not
encode any unproved LSI assertion.

| Measure and metric | Variance proxy `v` | Public theorem prefix |
| --- | --- | --- |
| Compact metric probability satisfying `MetricLSI μ C` | `C K²` | `MetricLSI` |
| Normalized Haar on actual matrix U(N), unnormalized Hilbert–Schmidt | `6 K²/N` | `unitary` |
| Normalized Haar on actual matrix SU(N), same metric | `2 K²/N` | `specialUnitary` |
| Standard Gaussian on `EuclideanSpace ℝ (Fin n)` | `K²` | `gaussian` |

Each prefix has `hasSubgaussianMGF`, `measure_ge_le`, `measure_le_le`, and
`measure_abs_ge_le`. The compact generic MGF theorem is named
`MetricLSI.hasSubgaussianMGF_of_compact`. All these applications cover **all
globally Lipschitz real functions**, including nonsmooth functions. Haar results
assume `0 < N` and include N=1. Gaussian results include every `n`, including
zero. Integrability and exponential moments are proved, not caller obligations.

The Haar tail statements keep the denominator `2 * ((6/N) * K²)` (or `2/N`
for SU). For positive K these exponents are `-N r²/(12 K²)` and
`-N r²/(4 K²)`. The statements also permit K=0 and r=0 using Lean's total
real division convention. The MGF theorem gives zero proxy when K=0; Mathlib's
`HasSubgaussianMGF.ae_eq_zero_of_hasSubgaussianMGF_zero` then gives almost-everywhere
zero centered observable, so positive-threshold events have measure zero.

The generic noncompact theorem `MetricLSI.hasSubgaussianMGF` explicitly assumes
all exponential moments. It is useful independently of compactness. Those
moments are established separately in the Gaussian application. The Gaussian
LSI itself remains the existing C¹ theorem with explicit moments; the new
all-Lipschitz **concentration** result does not assert an all-locally-Lipschitz
Gaussian `MetricLSI` or a Sobolev LSI. Globally Lipschitz concentration is the
natural claim here; local Lipschitz regularity alone supplies no global K.

## Source modules and proof

- `LogSobolev/Concentration/Herbst.lean`:
  `herbst_ratio_nonpos`, `quadratic_bound_of_herbst`,
  `entropy_exp_eq_mgf_mul`, `hasSubgaussianMGF_of_entropy_exp_bound`.
  The entropy identity is `Ent(exp(tf)) = M(t) (t (log M)'(t) - log M(t))`.
  The scalar differential inequality integrates in both signs of t, with the
  derivative at zero giving the actual mean.
- `LogSobolev/Geometry/LocalSlopeChain.lean`:
  `localSlope_comp_hasDerivAt_le`. A scalar outer derivative gives the exact
  pointwise chain factor for a globally Lipschitz inner observable. Its proof
  uses the continuous extension of the difference quotient and the defining
  local-slope limsup, without assuming that the observable is differentiable.
- `LogSobolev/Concentration/Metric.lean`:
  `MetricLSI.entropy_exp_le` applies LSI to `exp(tf/2)`, proving its square-log
  integrability and bounding energy by `t² K² M(t)/4`. The shared Herbst theorem
  and Mathlib's verified Chernoff theorem then give the stated bounds.
- `LogSobolev/Concentration/Approximation.lean`:
  `hasSubgaussianMGF_of_uniform_approximation`. Uniform errors δ control means
  by δ and centered exponentials by `exp(2 |t| δ)`. Taking δ to zero transfers
  the same variance proxy. This is independent of Gaussian measures.
- `LogSobolev/Concentration/Unitary.lean`: specializes the compact theorem to
  the existing unconditional U(N) and SU(N) LSI proofs.
- `LogSobolev/Concentration/Gaussian.lean`:
  `gaussian_integrable_exp_mul` proves exponential moments from Euclidean
  Lipschitz growth and integrability of products of `exp(c |xᵢ|)`.
  `gaussian_hasSubgaussianMGF_of_contDiff` applies the existing Gaussian LSI
  to the exponential test, proving every moment and energy condition.
  `gaussian_hasSubgaussianMGF` uses Lipschitz mollification and the generic
  approximation theorem to remove smoothness without changing K.

No normalized matrix norm or sup-norm gradient is substituted. The Gaussian
product coordinates are only used to prove integrability; all Lipschitz and
derivative bounds in the public Gaussian statements use the Euclidean norm.
No external dependency or toolchain change is introduced.

## Reuse, licenses, and modifications

The actual source was inspected at
[StatsMLlib](https://github.com/Lean-MoDS/StatsMLlib), commit
`75611ba335ee4ff2fb8b09938f6319d2cbf3d804` (Lean 4.34.0), under Apache-2.0:

- `StatsMLlib/Probability/Gaussian/LipschitzConcentration.lean`:
  `GaussianLipConcen.ratio_bound_gronwall` supplies the ratio lemma. Its
  `lipschitz_exp_integrable` supplies the product domination strategy. The
  source Gaussian-specific CGF proof was inspected but is replaced here by
  the shared measure-independent entropy/MGF proof. The original final
  Lipschitz concentration requires positive dimension and positive Lipschitz
  constant; the new proof includes both zero endpoints.
- `StatsMLlib/Probability/Gaussian/Sobolev/LipschitzMollification.lean` is ported
  to `LogSobolev/Gaussian/Port/GaussianSobolevDense/LipschitzMollification.lean`.
  It proves preservation of the Euclidean Lipschitz constant, smoothness,
  and the uniform error `K ε √n`. Modifications are import paths, public module
  visibility, and Lean 4.34.1 compatibility; copyright and author notices are
  retained. The upstream repository has no additional NOTICE file.

The existing Gaussian analytic LSI port from AI4SLT and StatsMLlib is reused
unchanged; its detailed provenance is in [GAUSSIAN.md](GAUSSIAN.md). The repository
LICENSE contains Apache-2.0. New measure-independent transfer lemmas connect the
ported pieces to the shared entropy and `MetricLSI` definitions. Mathlib supplies
MGF differentiability and sub-Gaussian Chernoff bounds, not an assumed Herbst
or Gaussian LSI theorem.

## Verification

Run `bash scripts/check.sh`. It builds the entire library, compiles all nine
independent client modules, and runs the unitary, Gaussian, and concentration
axiom audits. `ExamplesConcentration.lean` covers an abstract compact space,
a U(3) matrix coordinate proved not Haar-a.e. constant, nonsmooth U(1) distance,
SU(2) distance, nonsmooth Euclidean Gaussian norm, both zero endpoints, and the
explicit MGF bound.

`AuditConcentration.lean` selects declarations by originating project module,
including ports retaining upstream namespaces, and recursively collects every
root's dependency axioms. It permits only `propext`, `Classical.choice`, and
`Quot.sound`. Selected final theorems additionally have `#print axioms` and
fully elaborated `#check` output. The actual measure, entropy, slope, energy,
MGF predicate, and mollification definitions are printed for inspection.
The saved output is `docs/concentration-axiom-audit.txt`.

The remaining Gaussian local-slope/Sobolev LSI extension and general metric
LSI tensorization are separate tasks; neither is hidden in a hypothesis of the
new unconditional Gaussian or Haar concentration theorems.

Verification completed on Lean/Mathlib 4.34.1:

- `lake build`: passed, 3653 jobs.
- All nine independent example modules: passed.
- Existing unitary audit: passed for 1008 `LogSobolev` declarations.
- Existing Gaussian audit: passed for 637 declarations; its saved output is
  unchanged by the new concentration imports.
- New project-wide concentration audit: passed for 1602 declarations and their
  transitive dependencies, including upstream namespaces.
- Every selected `#print axioms`: only the three allowed foundational axioms.
- New implementation source scan: no `sorry`, `admit`, or custom `axiom`.
- `git diff --check`: passed.

Implementation milestone: Git commit
`7f8fe7748bff4d93943ab3f8474e9b57e9fa9b1c`.
The audit source, saved logs, and this report are committed separately after
that milestone. Existing U(N), SU(N), and C¹ Gaussian LSI source files are
unchanged.
