#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
lake env lean LogSobolev/Examples.lean
lake env lean LogSobolev/Audit.lean
