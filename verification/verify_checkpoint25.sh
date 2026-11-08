#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"
lake build > verification/checkpoint-25-project-build.log 2>&1
python3 verification/check_sources.py > verification/checkpoint-25-source-audit.log 2>&1
python3 verification/scan_sources.py >> verification/checkpoint-25-source-audit.log 2>&1
lake env lean verification/Checkpoint25Examples.lean > verification/checkpoint-25-examples.log 2>&1
lake env lean verification/Checkpoint25Audit.lean > verification/checkpoint-25-axiom-audit.log 2>&1
printf 'Checkpoint 25 build, source integrity, examples and transitive axiom audit passed.\n'
