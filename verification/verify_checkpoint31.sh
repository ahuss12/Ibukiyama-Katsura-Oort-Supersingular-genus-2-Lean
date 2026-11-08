#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build SupersingularCurves.Geometry.ScalarFrobeniusTateGraphQuotients
lake env lean verification/Checkpoint31Audit.lean
python verification/check_sources.py
python verification/scan_sources.py
