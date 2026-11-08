#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"
lake build > verification/project-build.log 2>&1
python3 verification/check_sources.py > verification/source-audit.log 2>&1
python3 verification/scan_sources.py >> verification/source-audit.log 2>&1
lake env lean verification/RepartitionExamples.lean > verification/repartition-examples.log 2>&1
lake env lean verification/Checkpoint18Audit.lean > verification/checkpoint-18-axiom-audit.log 2>&1
printf 'Checkpoint 18 build, retained-source verification, source scan, actual-curve examples and new-module transitive axiom audit passed.\n'
