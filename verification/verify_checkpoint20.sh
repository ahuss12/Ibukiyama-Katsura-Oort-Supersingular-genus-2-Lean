#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"
lake build > verification/checkpoint-20-project-build.log 2>&1
python3 verification/check_sources.py > verification/checkpoint-20-source-audit.log 2>&1
python3 verification/scan_sources.py >> verification/checkpoint-20-source-audit.log 2>&1
lake env lean verification/FrobeniusCechExamples.lean > verification/frobenius-cech-examples.log 2>&1
lake env lean verification/Checkpoint20Audit.lean > verification/checkpoint-20-axiom-audit.log 2>&1
printf 'Checkpoint 20 build, retained-source verification, source scan, actual-curve Frobenius/Cech examples and new project/vendor transitive axiom audit passed.\n'
