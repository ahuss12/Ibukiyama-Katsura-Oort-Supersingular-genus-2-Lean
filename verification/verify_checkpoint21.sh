#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"
lake build > verification/checkpoint-21-project-build.log 2>&1
python3 verification/check_sources.py > verification/checkpoint-21-source-audit.log 2>&1
python3 verification/scan_sources.py >> verification/checkpoint-21-source-audit.log 2>&1
lake env lean verification/CartierVerschiebungExamples.lean > verification/cartier-verschiebung-examples.log 2>&1
lake env lean verification/GenusTwoPRankExamples.lean > verification/genus-two-prank-examples.log 2>&1
lake env lean verification/Checkpoint21Audit.lean > verification/checkpoint-21-axiom-audit.log 2>&1
printf 'Checkpoint 21 project build, source integrity, Cartier/Verschiebung examples and transitive axiom audit passed.\n'
