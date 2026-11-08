#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean --version > verification/checkpoint-29-toolchain.log 2>&1
lake build SupersingularCurves.Geometry.ScalarFrobeniusTateEllipticSubgroup \
  > verification/checkpoint-29-project-build.log 2>&1
lake env lean verification/Checkpoint29Audit.lean \
  > verification/checkpoint-29-axiom-audit.log 2>&1
python3 verification/check_sources.py > verification/checkpoint-29-source-audit.log 2>&1
python3 verification/scan_sources.py >> verification/checkpoint-29-source-audit.log 2>&1
