/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.LevyConvergence

@[expose] public section

/-!
# Lévy convergence compatibility import

The earlier Lean 4.28 port supplied the Lévy convergence theorem from the
Apache-2.0 CLT/AI4SLT development here. Mathlib 4.34.1 now proves
`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun` with the required
statement. We use that theorem directly, removing the duplicate local proofs.
The import path is retained for downstream Gaussian approximation modules.
-/
