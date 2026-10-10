#!/usr/bin/env bash
# Optional build scheduling for machines with limited memory.
# Build independent branches in sequence; each target still uses ordinary Lake.
set -euo pipefail
cd "$(dirname "$0")/.."
for module in \
  LogSobolev.Gaussian.Port.GaussianPoincare.RademacherApprox \
  LogSobolev.Gaussian.Port.EfronStein \
  LogSobolev.Gaussian.Port.GaussianPoincare.LevyContinuity \
  LogSobolev.Gaussian.Port.GaussianMeasure \
  LogSobolev.Gaussian.Port.GaussianSobolevDense.Density \
  LogSobolev.Gaussian.Port.GaussianLSI.OneDimGLSICompSmo \
  LogSobolev.Gaussian.Port.ConvergenceL1Subseq \
  LogSobolev.Gaussian.Port.GaussianLSI.OneDimGLSI \
  LogSobolev.Gaussian.Port.GaussianLSI.SubAddEnt.Decomposition \
  LogSobolev.Gaussian.Port.GaussianLSI.DualEntApp \
  LogSobolev.Gaussian.Port.GaussianLSI.SubAddEnt.Subadditivity \
  LogSobolev.Gaussian.Port.GaussianLSI.TensorizedGLSI \
  LogSobolev.Gaussian.EuclideanEnergy \
  LogSobolev.Geometry.LocalSlopeFDeriv \
  LogSobolev.Gaussian.LSI; do
  lake build "$module"
done
lake build
