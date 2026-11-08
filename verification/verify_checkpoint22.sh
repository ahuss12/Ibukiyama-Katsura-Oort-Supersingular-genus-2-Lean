#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"
lake build > verification/checkpoint-22-project-build.log 2>&1
python3 verification/check_sources.py > verification/checkpoint-22-source-audit.log 2>&1
python3 verification/scan_sources.py >> verification/checkpoint-22-source-audit.log 2>&1
lake env lean verification/SupersingularGeometryExamples.lean > verification/supersingular-geometry-examples.log 2>&1
lake env lean verification/Checkpoint22Audit.lean > verification/checkpoint-22-axiom-audit.log 2>&1
printf 'Checkpoint 22 build, source integrity, geometric example and transitive axiom audit passed.\n'
