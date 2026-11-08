#!/usr/bin/env python3
"""Reuse a verified checkpoint cache and build only requested Lean modules.

Lake's --old mode ignores changed dependency timestamps. We use it only after
checking the archived sources and artifact hashes, the exact dependency pins,
and clean external package sources. No trace or proof object is synthesized.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache-manifest', type=Path, required=True)
    parser.add_argument('modules', nargs='+', help='Project or @package/+module targets')
    args = parser.parse_args()
    manifest = json.loads(args.cache_manifest.read_text())
    sources = manifest['source_hashes']
    files = manifest['files']
    for item in sources + files:
        path = ROOT / item['path']
        if not path.is_file() or digest(path) != item['sha256']:
            raise SystemExit(f'Cache mismatch: {item["path"]}; restore the matching cache before reuse.')
    lock = json.loads((ROOT / 'lake-manifest.json').read_text())
    for package in lock['packages']:
        if package['type'] != 'git':
            continue
        directory = ROOT / '.lake/packages' / package['name']
        actual = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
        if actual != package['rev']:
            raise SystemExit(f'Incorrect revision: {package["name"]}')
        subprocess.run(['git', '-C', str(directory), 'diff', '--exit-code', 'HEAD', '--'], check=True)
    # ZIP extractors may give old source files a fresh mtime. Restore a source
    # timestamp only for the exact source/artifact pair validated above.
    for item in sources:
        source = ROOT / item['path']
        base = ROOT / 'vendor/flt' if item['path'].startswith('vendor/flt/') else ROOT
        trace = base / '.lake/build/lib/lean' / source.relative_to(base).with_suffix('.trace')
        if not trace.is_file():
            raise SystemExit(f'Missing successful build trace: {trace}')
        when = min(source.stat().st_mtime, trace.stat().st_mtime - 1)
        os.utime(source, (when, when))
    print(f'Validated {len(sources)} unchanged sources and {len(files)} cached artifacts.', flush=True)
    subprocess.run(['lake', '--old', 'build', *args.modules], cwd=ROOT, check=True)


if __name__ == '__main__':
    main()
