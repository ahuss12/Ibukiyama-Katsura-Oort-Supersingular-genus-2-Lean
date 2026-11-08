#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mapfile -t targets < <(python3 - <<'PYCODE'
import json
s=json.load(open('verification/checkpoint-status.json'))
assert s['checkpoint']==33
for module in s['current_build_targets']:
    print('+'+module)
PYCODE
)
python3 verification/build_incremental.py \
  --cache-manifest verification/checkpoint-33-build-cache-manifest.json "${targets[@]}"
lake env lean verification/Checkpoint33Audit.lean
lake env lean verification/Checkpoint33RepairsAudit.lean
python3 verification/check_sources.py
python3 verification/scan_sources.py
