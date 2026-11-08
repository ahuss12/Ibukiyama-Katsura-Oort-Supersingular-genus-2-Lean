#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"
lake build > verification/checkpoint-26-project-build.log 2>&1
python3 verification/check_sources.py > verification/checkpoint-26-source-audit.log 2>&1
python3 verification/scan_sources.py >> verification/checkpoint-26-source-audit.log 2>&1
lake env lean verification/Checkpoint26Examples.lean > verification/checkpoint-26-examples.log 2>&1
lake env lean verification/Checkpoint26Audit.lean > verification/checkpoint-26-axiom-audit.log 2>&1
printf 'Checkpoint 26 build, source integrity, examples and transitive axiom audit passed.\n'
