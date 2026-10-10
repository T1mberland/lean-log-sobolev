#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
for example in Examples ExamplesInterval ExamplesProductEntropy ExamplesIntervalMetric ExamplesPhasePolynomial ExamplesPhaseEnergy ExamplesUnitary ExamplesGaussian; do
  lake env lean "LogSobolev/${example}.lean"
done
# The audits inspect complete transitive closures; Gaussian ports are also
# selected by originating module because some retain upstream namespaces.
lake env lean LogSobolev/AuditUnitary.lean | tee docs/unitary-axiom-audit.txt
lake env lean LogSobolev/AuditGaussian.lean | tee docs/gaussian-axiom-audit.txt
