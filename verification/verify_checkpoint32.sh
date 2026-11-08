#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build \
  SupersingularCurves.Geometry.ScalarFrobeniusTatePolarizedGraph \
  SupersingularCurves.Geometry.AbelianVerschiebungBinaryProducts \
  SupersingularCurves.Geometry.FiniteBySectionsExternalProduct \
  SupersingularCurves.Geometry.PolarisationRootKernel \
  SupersingularCurves.Geometry.AbelianProductLineBundle
lake env lean verification/Checkpoint32Audit.lean
python3 verification/check_sources.py
python3 verification/scan_sources.py
