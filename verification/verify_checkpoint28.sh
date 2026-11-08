#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean --version > verification/checkpoint-28-toolchain.log 2>&1
python3 - <<'PY'
import json,subprocess
from pathlib import Path
r=Path('.')
mods=[x['module'] for x in json.loads((r/'provenance/checkpoint-28-foundation-imports.json').read_text())['files']]
with (r/'verification/checkpoint-28-project-build.log').open('w') as f:
    subprocess.run(['lake','build','SupersingularCurves',*mods],stdout=f,stderr=subprocess.STDOUT,check=True)
PY
lake env lean verification/Checkpoint28Examples.lean > verification/checkpoint-28-examples.log 2>&1
lake env lean verification/Checkpoint28Audit.lean > verification/checkpoint-28-axiom-audit.log 2>&1
python3 verification/check_sources.py > verification/checkpoint-28-source-audit.log 2>&1
python3 verification/scan_sources.py >> verification/checkpoint-28-source-audit.log 2>&1
