#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"
lake build > verification/checkpoint-23-project-build.log 2>&1
python3 verification/check_sources.py > verification/checkpoint-23-source-audit.log 2>&1
python3 verification/scan_sources.py >> verification/checkpoint-23-source-audit.log 2>&1
lake env lean verification/Checkpoint23Examples.lean > verification/checkpoint-23-examples.log 2>&1
lake env lean verification/Checkpoint23Audit.lean > verification/checkpoint-23-axiom-audit.log 2>&1
printf 'Checkpoint 23 build, source integrity, examples and transitive axiom audit passed.\n'
