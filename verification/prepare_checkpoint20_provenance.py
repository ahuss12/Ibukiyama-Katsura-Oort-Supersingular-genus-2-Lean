#!/usr/bin/env python3
"""Reproduce CP20's retained-source and pinned-vendor provenance.

Run with the checkpoint-19 ZIP and the downloaded additions manifest.  This
does not claim that any new project proof has compiled, or edit its hash.
"""
import argparse
import hashlib
import json
from pathlib import Path
import zipfile


ROOT = Path(__file__).resolve().parents[1]
VENDOR = ROOT / 'vendor/flt'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write_json(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n')


def imports(source):
    cleaned, depth, i = [], 0, 0
    while i < len(source):
        pair = source[i:i + 2]
        if pair == '/-':
            depth += 1
            i += 2
        elif depth and pair == '-/':
            depth -= 1
            i += 2
        else:
            cleaned.append(source[i] if not depth or source[i] == '\n' else ' ')
            i += 1
    assert depth == 0, 'Unclosed block comment'
    result = []
    for line in ''.join(cleaned).splitlines():
        line = line.split('--', 1)[0].strip()
        if line.startswith('import '):
            result.extend(line[7:].split())
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--previous-archive', type=Path, required=True)
    parser.add_argument('--additions', type=Path, required=True)
    args = parser.parse_args()
    retained_proofs, retained_vendor = [], []
    prefix = ROOT.name + '/'
    with zipfile.ZipFile(args.previous_archive) as archive:
        previous = json.loads(archive.read(prefix + 'vendor/flt/upstream-manifest.json'))
        for name in sorted(archive.namelist()):
            rel = name.removeprefix(prefix)
            if rel.startswith('SupersingularCurves/') and rel.endswith('.lean'):
                data = archive.read(name)
                assert (ROOT / rel).read_bytes() == data, rel
                retained_proofs.append({'path': rel, 'sha256': sha(data)})
        for item in previous['files']:
            rel = 'vendor/flt/' + item['path']
            data = archive.read(prefix + rel)
            assert sha(data) == item['current_sha256'], rel
            assert (ROOT / rel).read_bytes() == data, rel
            retained_vendor.append({'path': rel, 'sha256': sha(data)})
    assert len(retained_proofs) == 78
    assert len(retained_vendor) == 1519
    assert previous['commit'] == 'aa2d8b34692b16c70f699536de0d8e75b9a3e9ef'

    additions = json.loads(args.additions.read_text())
    assert len(additions['files']) == 8
    old_modules = {item['module'] for item in previous['files']}
    for item in additions['files']:
        assert item['module'] not in old_modules, item['module']
        data = (VENDOR / item['path']).read_bytes()
        assert sha(data) == item['current_sha256'] == item['upstream_sha256'], item['path']
        blob = b'blob ' + str(len(data)).encode() + b'\0' + data
        assert hashlib.sha1(blob).hexdigest() == item['upstream_git_blob'], item['path']
        assert imports(data.decode()) == item['imports'], item['path']

    manifest = previous
    manifest['files'] = sorted(previous['files'] + additions['files'], key=lambda r: r['module'])
    manifest['roots'] = sorted(set(previous['roots']) | set(additions['roots']))
    modules = {item['module']: item for item in manifest['files']}
    assert len(modules) == len(manifest['files']) == 1527
    pending, visited, external = list(manifest['roots']), set(), set()
    while pending:
        name = pending.pop()
        if name in visited or name in external:
            continue
        if name not in modules:
            external.add(name)
        else:
            visited.add(name)
            pending.extend(modules[name]['imports'])
    assert visited == set(modules), 'Not the exact selected import closure'
    actual = {path.relative_to(VENDOR).as_posix()
              for folder in ['Definitions', 'Theorems', 'P2M']
              for path in (VENDOR / folder).rglob('*.lean')}
    assert actual == {item['path'] for item in modules.values()}
    manifest['external_imports'] = sorted(external)

    write_json(ROOT / 'provenance/mini-checkpoint-19.json', {
        'checkpoint': 19,
        'source_archive_sha256': sha(args.previous_archive.read_bytes()),
        'unchanged_proof_modules': retained_proofs,
        'unchanged_vendor_module_count': len(retained_vendor),
        'unchanged_vendor_modules': retained_vendor,
    })
    write_json(ROOT / 'provenance/cech-pullback-vendor-additions.json', {
        'checkpoint': 20,
        'upstream_commit': manifest['commit'],
        'vendor_additions': additions['files'],
        'new_compatibility_ports': [],
        'selected_roots': additions['roots'],
        'scope': 'Exact pinned upstream local-frame pullback theorems and their missing import closure. Compilation and transitive axiom audit are recorded separately.',
    })
    write_json(VENDOR / 'upstream-manifest.json', manifest)
    print('PASS: 78 checkpoint-19 project modules and 1,519 vendor modules are byte-identical;')
    print('8 added vendor sources match pinned SHA-256 and Git blob hashes; exact closure is 1,527 modules.')


if __name__ == '__main__':
    main()
