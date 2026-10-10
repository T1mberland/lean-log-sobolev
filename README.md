# Logarithmic Sobolev infrastructure for U(N)

**Status: verified partial development. Theorem 15 is not proved.**

This Lean 4.28.0 / Mathlib project develops components for the logarithmic
Sobolev inequality in [Meckes–Meckes](https://arxiv.org/pdf/1210.2681).
It uses Mathlib's actual matrix unitary and special unitary groups and the
**unnormalized Frobenius (Hilbert–Schmidt) metric**.

Proved components include:

* Entropy continuity under uniform convergence on compact finite-measure spaces,
  including squared observables with zeros and varying polynomial degree.
* Polynomial convolution on SU preserves degree; normalized averaging preserves
  Haar mass and nonnegative normalized kernels preserve upper bounds.
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
* The traceless skew-Hermitian matrix Lie algebra, its trace pairing, and the
  exact `2N` matrix commutator-energy identity (not yet a Ricci or LSI theorem).
* Actual SU exponential curves, their trace-zero determinant identity, exact
  Hilbert–Schmidt speed, and characterization of velocities at identity.
* The real Hilbert–Schmidt inner product on the SU Lie algebra, isometric
  unitary conjugation, the exact Killing coefficient `−2N`, and the `2N`
  commutator-energy identity for every real orthonormal basis.
* The full determinant-exponential identity and exponential homeomorphisms
  between open identity neighborhoods in su(N) and the actual SU(N) group.
* A proved smooth atlas on the actual matrix SU(N) group, with every translated
  exponential chart transition verified on its domain. Smooth matrix inclusion,
  multiplication, inversion, and exponential give an actual Lie group instance.
  Its inclusion derivative is `A ↦ U A`, preserving the exact Frobenius norm.
* Actual left-invariant SU fields and directional derivatives, local smooth
  ambient extensions, preservation of smoothness, and the operator identity
  `D_A D_B − D_B D_A = D_[A,B]` for every smooth SU test.
* The exact `N/2` lower bound on second-derivative energy, and a constructed
  sum-of-squares operator whose carré du champ is proved to be first-derivative
  energy. Generator commutation, the Γ₂ identity, and `Γ₂ ≥ (N/2) Γ` are
  now proved for all smooth real SU tests. The entropy inequality is proved
  on polynomial tests below; the full smooth and locally Lipschitz classes remain open.
* Haar integration by parts for actual SU derivatives and the generator,
  with symmetry, nonpositivity, and the integrated estimate
  `(N/2) ∫ Γ(f,f) ≤ ∫ (Lf)²` for every smooth real test.
* Scalar diffusion/logarithm chain rules, the logarithmic Haar energy identity,
  and entropy differentiation on compact probability spaces. Entropy
  dissipation is proved **for a supplied positive family satisfying the heat
  equation at the specified time**; a general heat construction remains open.
  The weighted logarithmic Γ₂ curvature bound is also proved.
* The spatial Fisher dissipation identity and its exact `−N` bound. For
  supplied time-dependent families with explicit joint-continuity and mixed
  time/spatial derivative hypotheses, Fisher dissipation and `I′ ≤ −N I` are
  proved. These hypotheses are now discharged for the constructed polynomial
  heat flow below.
* The actual generator maximum principle and preservation of initial bounds
  for supplied classical heat solutions. An explicit heat solution is now
  constructed for every affine matrix observable `c + l(U)`, with verified
  initial value, PDE, smooth spatial slices, continuity, and preservation of
  positivity.
* Finite-dimensional spaces of polynomial matrix observables, invariant under
  the actual generator. Its exponential constructs polynomial heat evolution
  with the semigroup law, positivity, supremum-norm contraction, and normalized
  Haar-mass conservation. All regularity needed for entropy and Fisher
  differentiation is proved. For strictly positive polynomial data,
  `I(Pₜ f) ≤ exp(−Nt) I(f)` holds for every `t ≥ 0`.
* Connectedness of the actual U(N) and SU(N), proved using finite-spectrum
  functional calculus and a continuous determinant-correcting retraction.
  Smooth SU functions with zero Haar energy are proved equal to their Haar
  mean; in particular, the actual Laplacian has only constants in its kernel.
* Polynomial heat converges uniformly to its Haar mean and has vanishing limiting
  entropy. The resulting **polynomial LSI is proved**:
  `Ent(f²) ≤ (4/N) ∫ Γ(f,f)` for every real finite-degree polynomial observable,
  with no positivity restriction on `f`.
* Actual invariant derivative energy is proved bounded by the paper's squared
  local Hilbert–Schmidt slope. Every polynomial has a global smooth ambient
  extension and is locally Lipschitz, with finite slope energy. The polynomial
  LSI now holds with the **actual local slope**, both in extended form with
  constant `2/N` and in real-integral form with coefficient `4/N`.
  Extension to all locally Lipschitz functions remains open.
* The normalized interval and its L² product with SU(N).
* The paper's phase map into U(N), with the `sqrt(3)` Lipschitz bound.
* **The exact short-interval Haar decomposition (Lemma 16)** for every positive N,
  including N=1, proved from Haar invariance and periodic integration.
* Conditional final transfer from an explicitly assumed product LSI with
  constant `2/N` to U(N) with constant `6/N`.
* A 1-Lipschitz diagonal coordinate that is not Haar-a.e. constant in every
  positive dimension.

The full metric LSI on SU(N), U(N), the interval, and the circle remains open.
The proved SU inequality currently covers polynomial observables with both
actual carré-du-champ energy and the paper's local metric slope. The U(N) transfer still takes an explicit product
`MetricLSI` assumption, which this development has not discharged.

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
See [the mathematical report](docs/REPORT.md) for the exact scope and open goals,
and [the SU proof boundary](docs/SU_LSI.md) for the remaining geometric and analytic steps.

## Layout

`Measure/` holds entropy, explicit-energy LSI, and normalized interval measure.
`Geometry/` holds the metric slope, its measurability and integrability, and
metric-LSI transport. `Unitary/` holds matrix normalization, Haar constructions,
the phase map and nonconstant observables. `Audit.lean` and `Examples.lean` are
independent validation files.

The small entropy compatibility port is attributed in its source file. No
external research library is imported; Mathlib is pinned in the manifest.
