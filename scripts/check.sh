#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
lake env lean LogSobolev/Examples.lean
lake env lean LogSobolev/ExamplesInterval.lean
lake env lean LogSobolev/ExamplesIntervalMetric.lean
lake env lean LogSobolev/Audit.lean
lake env lean LogSobolev/AuditIntervalMetric.lean
lake env lean LogSobolev/ExamplesPhasePolynomial.lean
lake env lean LogSobolev/AuditPhasePolynomial.lean
