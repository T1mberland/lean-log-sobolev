# Lean 4.34.1 migration

The `upgrade-lean` branch upgrades Lean 4.28.0 to stable Lean 4.34.1,
released September 24, 2026, and pins matching Mathlib tag `v4.34.1`
(commit `d13f23b723b8a846827a245b89c10fc7d3f11612`).

Release: https://github.com/leanprover/lean4/releases/tag/v4.34.1

## Compatibility changes

- Adopt Lean's module system with public imports and exposed public definitions,
  preserving the library's import and definition-unfolding behavior.
- Make function compositions, subtype metrics, measure transports, and
  derivative equalities explicit where elaboration changed.
- Restore associative-ring Lie instances locally where required. Selected
  matrix modules use the previous backward-elaboration transparency behavior;
  this affects elaboration only, not kernel verification or theorem assumptions.
- Replace the ported Lévy convergence proof by Mathlib's existing theorem in
  `Mathlib.MeasureTheory.Measure.LevyConvergence`.
- Update Gaussian cutoff and mollification proofs from Apache-2.0 StatsMLlib
  commit `75611ba335ee4ff2fb8b09938f6319d2cbf3d804`, files
  `StatsMLlib/Probability/Gaussian/Sobolev/{Defs,Cutoff,Mollification,Density}.lean`.
  Mathlib now incorporates measurability into `eLpNorm`: the two generic
  uniform-convergence helpers in `Mollification.lean` consequently require
  measurability of the differences. Their applications establish it; the
  final Gaussian LSI hypotheses are unchanged. Density triangle-inequality
  helpers drop measurability arguments that the new API no longer needs.
- Update the one-dimensional C¹ Gaussian proof from the same StatsMLlib
  revision, `StatsMLlib/Probability/Concentration/LogSobolev/GaussianOneDim.lean`,
  retaining the shared entropy definition. Its entropy-density definition
  `GaussianSobolevReal.phi` is public because public helper statements use it.
- The Rademacher support lemma now takes `AEMeasurable` explicitly, as in
  StatsMLlib `StatsMLlib/Probability/Gaussian/Poincare/EfronStein.lean` at
  the same revision. Nonzero `Measure.map` no longer implies measurability.
  Coordinate projections satisfy the new premise directly.
- Restore the Taylor argument from the Apache-2.0 AI4SLT source recorded in
  `GAUSSIAN.md`, retaining attribution, and adapt Gaussian integral APIs.
- Use Lean's public `collectAxioms` API. Under the module system this reads
  transitive axiom sets recorded during export, including private proof
  dependencies. The audits reject everything except `propext`,
  `Classical.choice`, and `Quot.sound`.
- Add `scripts/build-sequential.py` to build local modules in import order on
  machines with limited memory; Lake still tracks all dependencies.

The dependency directory was isolated from a pre-existing symlink into another
project before updating. No files in that project's checkout were changed.

## Mathematical scope

The migration preserves the existing statements: the full locally Lipschitz
U(N) and SU(N) inequalities, and the dimension-free C¹ Gaussian inequality
with its stated moment assumptions. It does not claim a new nonsmooth Gaussian
extension. No research library is added as a dependency.

## Verification

All checks passed on Lean 4.34.1 with the pinned Mathlib revision:

- `lake build`: **3,590 jobs**, successful.
- All eight independent clients compile: `Examples`, `ExamplesInterval`,
  `ExamplesProductEntropy`, `ExamplesIntervalMetric`, `ExamplesPhasePolynomial`,
  `ExamplesPhaseEnergy`, `ExamplesUnitary`, and `ExamplesGaussian`.
- `lake env lean LogSobolev/AuditUnitary.lean`: **980** exported `LogSobolev`
  declarations audited, including the final U(N) and SU(N) theorems.
- `lake env lean LogSobolev/AuditGaussian.lean`: **637** declarations selected
  by Gaussian source module, plus the local-slope derivative bridge, audited.
- Every selected declaration's complete transitive axiom closure contains only
  `propext`, `Classical.choice`, and `Quot.sound`. The lower declaration counts
  compared with Lean 4.28 reflect module visibility and removal of duplicated
  Lévy infrastructure; private proof dependencies remain in the audited closures.
- Full elaborated theorem statements and definitions were inspected and saved
  in `unitary-axiom-audit.txt` and `gaussian-axiom-audit.txt`.
- Source scan found no `sorry`, `admit`, custom `axiom`, `unsafe`, or
  `implemented_by` declarations in `LogSobolev`; `git diff --check` passed.

Client checks retain actual normalized Haar probability, unnormalized
Hilbert–Schmidt norm, positive dimensions including N = 1, and nonconstant
unitary observables. Gaussian examples retain dimension zero, an unbounded
one-dimensional linear function, and a nonconstant smooth bump with Euclidean
energy. The final theorem statements and constants have not changed.

Some upstream deprecation and style warnings remain; there are no build errors.
No theorem assumes an LSI or an unproved analytic/geometric criterion.

