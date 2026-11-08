#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"
lake build > verification/checkpoint-19-project-build.log 2>&1
python3 verification/check_sources.py > verification/checkpoint-19-source-audit.log 2>&1
python3 verification/scan_sources.py >> verification/checkpoint-19-source-audit.log 2>&1
lake env lean verification/ResidueExamples.lean > verification/residue-examples.log 2>&1
lake env lean verification/Checkpoint19Audit.lean > verification/checkpoint-19-axiom-audit.log 2>&1
printf 'Checkpoint 19 build, retained-source verification, source scan, actual-curve examples and new project/vendor transitive axiom audit passed.\n'
