#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"
lake build > verification/checkpoint-24-project-build.log 2>&1
python3 verification/check_sources.py > verification/checkpoint-24-source-audit.log 2>&1
python3 verification/scan_sources.py >> verification/checkpoint-24-source-audit.log 2>&1
lake env lean verification/Checkpoint24Examples.lean > verification/checkpoint-24-examples.log 2>&1
lake env lean verification/Checkpoint24Audit.lean > verification/checkpoint-24-axiom-audit.log 2>&1
printf 'Checkpoint 24 build, source integrity, examples and transitive axiom audit passed.\n'
