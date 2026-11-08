#!/usr/bin/env python3
"""Compatibility entry point for checkpoint-28 source checks.

The draft snapshot was superseded by the checked foundation checkpoint.
This script checks sources only. Run verify_checkpoint28.sh for Lean builds,
examples and declaration audits; Block 1 classification remains incomplete.
"""
import json, subprocess, sys
from pathlib import Path
r=Path(__file__).resolve().parents[1]
for script in ['check_sources.py','scan_sources.py']:
    subprocess.run([sys.executable,str(r/'verification'/script)],cwd=r,check=True)
print(json.dumps({'checkpoint':28,'source_checks_passed':True,
 'full_verification_record':'verification/checkpoint-28-run.json',
 'global_zero_dV_product_isogeny_proved':False,'block_1_complete':False}))
