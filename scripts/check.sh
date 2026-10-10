#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
for example in Examples ExamplesInterval ExamplesProductEntropy ExamplesIntervalMetric ExamplesPhasePolynomial ExamplesPhaseEnergy ExamplesUnitary; do
  lake env lean "LogSobolev/${example}.lean"
done
# This audit traverses every project declaration and its complete dependency closure.
lake env lean LogSobolev/AuditUnitary.lean | tee docs/unitary-axiom-audit.txt
