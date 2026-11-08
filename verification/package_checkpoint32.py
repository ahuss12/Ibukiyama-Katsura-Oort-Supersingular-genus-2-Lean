#!/usr/bin/env python3
"""Preserve completed source-backed Lean artifacts without unchecked drafts."""
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(2**20), b''):
            h.update(chunk)
    return h.hexdigest()


parser = argparse.ArgumentParser()
parser.add_argument('output', type=Path)
args = parser.parse_args()
args.output.mkdir(parents=True, exist_ok=True)
archive = args.output.resolve() / 'supersingular-curves-checkpoint-32-build-cache.tar.zst'
sources, artifacts, counts = [], set(), {}
for prefix, label in [(Path('.'), 'project'), (Path('vendor/flt'), 'vendor')]:
    base = ROOT / prefix
    lib = base / '.lake/build/lib/lean'
    ir = base / '.lake/build/ir'
    count = 0
    for olean in sorted(lib.rglob('*.olean')):
        rel = olean.relative_to(lib).with_suffix('')
        source = base / rel.with_suffix('.lean')
        trace = lib / rel.with_suffix('.trace')
        if not source.is_file() or not trace.is_file():
            continue
        if label == 'project' and rel.parts[0] != 'SupersingularCurves':
            continue
        record = json.loads(trace.read_text())
        if not record.get('outputs', {}).get('o'):
            continue
        count += 1
        sources.append({'path': source.relative_to(ROOT).as_posix(), 'sha256': digest(source)})
        for folder in [lib / rel.parent, ir / rel.parent]:
            if not folder.is_dir():
                continue
            for p in folder.glob(rel.name + '.*'):
                if p.is_file() and '.setup.json' not in p.name and not p.name.endswith('.tmp'):
                    artifacts.add(p)
    counts[label] = count
assert counts['project'] >= 208 and counts['vendor'] >= 2397
manifest = {
    'checkpoint': 32, 'created_at_utc': datetime.now(timezone.utc).isoformat(),
    'platform': 'Linux x86_64', 'lean': '4.34.0-rc2',
    'mathlib_commit': '85e3a25e006c35636f0e53b0e9296caca2685bc0',
    'partial_cache': True, 'full_aggregate_checked_this_turn': False,
    'external_dependencies_included': False, 'compiler_included': False,
    'unchecked_drafts_excluded': True, 'diagnostic_copies_excluded': True,
    'project_olean_count': counts['project'], 'vendor_olean_count': counts['vendor'],
    'source_hashes': sources,
    'files': [{'path': p.relative_to(ROOT).as_posix(), 'size': p.stat().st_size,
               'sha256': digest(p)} for p in sorted(artifacts)],
}
manifest_path = ROOT / 'verification/checkpoint-32-build-cache-manifest.json'
manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
with archive.open('wb') as output:
    proc = subprocess.Popen(['zstd', '-5', '-T2', '-q', '-c'], stdin=subprocess.PIPE, stdout=output)
    assert proc.stdin is not None
    with tarfile.open(fileobj=proc.stdin, mode='w|') as tar:
        for p in sorted(artifacts):
            tar.add(p, arcname=p.relative_to(ROOT).as_posix(), recursive=False)
        tar.add(manifest_path, arcname=manifest_path.relative_to(ROOT).as_posix(), recursive=False)
    proc.stdin.close()
    assert proc.wait() == 0
record = {'archive': archive.name, 'bytes': archive.stat().st_size, 'sha256': digest(archive),
          'project_olean_count': counts['project'], 'vendor_olean_count': counts['vendor'],
          'artifact_files': len(artifacts)}
(ROOT / 'verification/checkpoint-32-build-cache-record.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record), flush=True)
