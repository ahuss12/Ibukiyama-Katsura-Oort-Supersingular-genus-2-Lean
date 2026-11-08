#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean --version > verification/checkpoint-30-toolchain.log 2>&1
lake build SupersingularCurves.Geometry.ScalarFrobeniusTateFiniteModels \
  > verification/checkpoint-30-project-build.log 2>&1
lake env lean verification/Checkpoint30Audit.lean \
  > verification/checkpoint-30-axiom-audit.log 2>&1
python3 verification/check_sources.py > verification/checkpoint-30-source-audit.log 2>&1
python3 verification/scan_sources.py >> verification/checkpoint-30-source-audit.log 2>&1
