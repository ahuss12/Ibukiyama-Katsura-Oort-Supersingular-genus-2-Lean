#!/usr/bin/env python3
"""Verify vendored bytes, notices, exact import closure, and pinned versions."""
import hashlib
import json
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VENDOR = ROOT / 'vendor' / 'flt'
manifest = json.loads((VENDOR / 'upstream-manifest.json').read_text())
assert manifest['commit'] == 'aa2d8b34692b16c70f699536de0d8e75b9a3e9ef'
ports = json.loads((VENDOR / 'port-manifest.json').read_text())
assert ports['upstream_commit'] == manifest['commit']
ported = {r['path']: r for r in ports['files']}

# Historical snapshots predate this proof-preserving implementation port.
# Current vendor bytes are still checked against upstream-manifest.json below;
# reconstruct only this exact documented old text for historical comparisons.
DENSITY_PORT = 'P2M/Sol/S_GoodReductionJacobian_AbelianSchemePropertyBundle_forall_mem_of_isClosed_of_forall_torsion_mem.lean'
FAITHFUL_FLAT_PORT = 'P2M/Sol/S_Module_FaithfullyFlat_exists_submodule_isBaseChange_of_cocycle.lean'
CHECKPOINT_33_PORTS = (DENSITY_PORT, FAITHFUL_FLAT_PORT)
@lru_cache(maxsize=None)
def historical_source_bytes(path):
    data = (ROOT / path).read_bytes()
    if path.removeprefix('vendor/flt/') in CHECKPOINT_33_PORTS:
        port = ported[path.removeprefix('vendor/flt/')]
        assert hashlib.sha256(data).hexdigest() == port['ported_sha256']
        source = data.decode()
        for replacement in reversed(port['replacements']):
            assert source.count(replacement['new']) == 1
            source = source.replace(replacement['new'], replacement['old'])
        data = source.encode()
        assert hashlib.sha256(data).hexdigest() == port['upstream_sha256']
    for repair in json.loads((ROOT / 'provenance/checkpoint-33-project-repairs.json').read_text()):
        if path == repair['path']:
            assert hashlib.sha256(data).hexdigest() == repair['new_sha256']
            assert data == repair['new'].encode()
            data = repair['old'].encode()
            assert hashlib.sha256(data).hexdigest() == repair['prior_sha256']
    return data


def historical_vendor_record(module):
    record = dict(modules[module])
    if record['path'] in CHECKPOINT_33_PORTS:
        # This exact port is validated and reversed above; older inventories
        # describe its upstream bytes, not the new checked implementation.
        record['current_sha256'] = ported[record['path']]['upstream_sha256']
    return record


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
    out = []
    for line in ''.join(cleaned).splitlines():
        line = line.split('--', 1)[0].strip()
        if line.startswith('import '):
            out.extend(line[7:].split())
    return out

modules = {r['module']: r for r in manifest['files']}
assert len(modules) == len(manifest['files'])
for r in modules.values():
    data = (VENDOR / r['path']).read_bytes()
    assert hashlib.sha256(data).hexdigest() == r['current_sha256'], r['path']
    upstream = data
    if r['path'] in ported:
        port = ported[r['path']]
        assert port['ported_sha256'] == r['current_sha256']
        assert port['upstream_sha256'] == r['upstream_sha256']
        source = data.decode()
        for replacement in reversed(port['replacements']):
            assert source.count(replacement['new']) == 1
            source = source.replace(replacement['new'], replacement['old'])
        upstream = source.encode()
    assert hashlib.sha256(upstream).hexdigest() == r['upstream_sha256'], r['path']
    blob = b'blob ' + str(len(upstream)).encode() + b'\0' + upstream
    assert hashlib.sha1(blob).hexdigest() == r['upstream_git_blob'], r['path']
    assert imports(data.decode()) == r['imports'], r['path']
for r in manifest['notices']:
    assert hashlib.sha256((VENDOR / r['path']).read_bytes()).hexdigest() == r['sha256'], r['path']
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
assert external == set(manifest['external_imports'])
actual = {p.relative_to(VENDOR).as_posix() for folder in ['Definitions', 'Theorems', 'P2M']
          for p in (VENDOR / folder).rglob('*.lean')}
assert actual == {r['path'] for r in modules.values()}
assert set(ported) <= actual
assert (ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.0-rc2'
lock = json.loads((ROOT / 'lake-manifest.json').read_text())
mathlib = next(p for p in lock['packages'] if p['name'] == 'mathlib')
assert mathlib['rev'] == '85e3a25e006c35636f0e53b0e9296caca2685bc0'
reuse = json.loads((ROOT / 'provenance' / 'cartier-reuse.json').read_text())
for r in reuse['reused_modules']:
    assert hashlib.sha256((ROOT / r['new_path']).read_bytes()).hexdigest() == r['adapted_sha256']
previous = json.loads((ROOT / 'provenance' / 'checkpoint-2.json').read_text())
for r in previous['unchanged_proof_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
checkpoint3 = json.loads((ROOT / 'provenance' / 'checkpoint-3.json').read_text())
for r in checkpoint3['unchanged_proof_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
generalized = json.loads((ROOT / 'provenance' / 'function-field-generalization.json').read_text())
assert hashlib.sha256((ROOT / generalized['new_path']).read_bytes()).hexdigest() == generalized['new_sha256']
checkpoint4 = json.loads((ROOT / 'provenance' / 'checkpoint-4.json').read_text())
for r in checkpoint4['unchanged_proof_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
print(f'PASS: {len(modules)} pinned upstream modules '
      f'({len(modules) - len(ported)} unchanged, {len(ported)} documented compatibility port), '
      f'Git blob hashes, exact import closure, '
      f'{len(manifest["notices"])} notices, and pinned Lean/mathlib versions.')
print(f'PASS: {len(reuse["reused_modules"])} recorded Cartier adaptations and '
      f'{len(previous["unchanged_proof_modules"])} unchanged checkpoint-2 proof modules.')
print(f'PASS: {len(checkpoint3["unchanged_proof_modules"])} unchanged checkpoint-3 proof modules '
      'and the recorded generalized quadratic-field construction.')
print(f'PASS: {len(checkpoint4["unchanged_proof_modules"])} unchanged checkpoint-4 proof modules.')

ramification = json.loads((ROOT / "provenance" / "ramification-generalization.json").read_text())
for r in ramification["modules"]:
    assert hashlib.sha256((ROOT / r["new_path"]).read_bytes()).hexdigest() == r["new_sha256"]
print("PASS: recorded quadratic ramification/genus generalizations.")

checkpoint5 = json.loads((ROOT / 'provenance' / 'checkpoint-5.json').read_text())
for r in checkpoint5['unchanged_proof_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
picard_reuse = json.loads((ROOT / 'provenance' / 'picard-reuse.json').read_text())
for r in picard_reuse['reused_modules']:
    assert hashlib.sha256((ROOT / r['new_path']).read_bytes()).hexdigest() == r['adapted_sha256']
print(f'PASS: {len(checkpoint5["unchanged_proof_modules"])} unchanged checkpoint-5 proof modules '
      f'and {len(picard_reuse["reused_modules"])} recorded Picard adaptations.')

checkpoint6 = json.loads((ROOT / 'provenance' / 'checkpoint-6.json').read_text())
for r in checkpoint6['unchanged_proof_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
print(f'PASS: {len(checkpoint6["unchanged_proof_modules"])} unchanged checkpoint-6 proof modules.')

checkpoint7 = json.loads((ROOT / 'provenance' / 'checkpoint-7.json').read_text())
for r in checkpoint7['unchanged_proof_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
print(f'PASS: {len(checkpoint7["unchanged_proof_modules"])} unchanged checkpoint-7 proof modules.')

checkpoint8 = json.loads((ROOT / 'provenance' / 'checkpoint-8.json').read_text())
for r in checkpoint8['unchanged_proof_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
print(f'PASS: {len(checkpoint8["unchanged_proof_modules"])} unchanged checkpoint-8 proof modules.')

checkpoint9 = json.loads((ROOT / 'provenance' / 'checkpoint-9.json').read_text())
for r in checkpoint9['unchanged_proof_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
print(f'PASS: {len(checkpoint9["unchanged_proof_modules"])} unchanged checkpoint-9 proof modules.')

hypergeometric = json.loads((ROOT / 'provenance' / 'hypergeometric-generalization.json').read_text())
assert hashlib.sha256((ROOT / hypergeometric['upstream_source']).read_bytes()).hexdigest() == hypergeometric['upstream_source_sha256']
for r in hypergeometric['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
print(f'PASS: {len(hypergeometric["new_modules"])} recorded IKO simple-root modules and upstream proof attribution.')

checkpoint10 = json.loads((ROOT / 'provenance' / 'checkpoint-10.json').read_text())
for r in checkpoint10['unchanged_proof_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
print(f'PASS: {len(checkpoint10["unchanged_proof_modules"])} unchanged checkpoint-10 proof modules.')
geometric = json.loads((ROOT / 'provenance' / 'geometric-obstructions.json').read_text())
for r in geometric['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
print(f'PASS: {len(geometric["new_modules"])} recorded geometric-obstruction modules and upstream attribution.')

checkpoint11 = json.loads((ROOT / 'provenance' / 'checkpoint-11.json').read_text())
for r in checkpoint11['unchanged_proof_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
print(f'PASS: {len(checkpoint11["unchanged_proof_modules"])} unchanged checkpoint-11 proof modules.')
general = json.loads((ROOT / 'provenance' / 'general-genus-two.json').read_text())
for r in general['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
print(f'PASS: {len(general["new_modules"])} recorded general genus-two modules and proof attribution.')

checkpoint12 = json.loads((ROOT / 'provenance' / 'mini-checkpoint-12.json').read_text())
for r in checkpoint12['unchanged_proof_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
print(f'PASS: {len(checkpoint12["unchanged_proof_modules"])} unchanged mini-checkpoint-12 proof modules.')
infinitesimal = json.loads((ROOT / 'provenance' / 'infinitesimal-picard.json').read_text())
for r in infinitesimal['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
print(f'PASS: {len(infinitesimal["new_modules"])} recorded infinitesimal Picard/cotangent modules and proof attribution.')

checkpoint13 = json.loads((ROOT / 'provenance/mini-checkpoint-13.json').read_text())
for r in checkpoint13['unchanged_proof_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
print(f"PASS: {len(checkpoint13['unchanged_proof_modules'])} unchanged mini-checkpoint-13 proof modules.")
frob = json.loads((ROOT / 'provenance/frobenius-verschiebung.json').read_text())
for r in frob['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
for r in frob['vendor_additions']:
    assert historical_vendor_record(r['module']) == r
print(f"PASS: {len(frob['new_modules'])} Frobenius/Verschiebung modules and {len(frob['vendor_additions'])} pinned foundation additions.")

checkpoint14 = json.loads((ROOT / 'provenance/mini-checkpoint-14.json').read_text())
for r in checkpoint14['unchanged_proof_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
print(f"PASS: {len(checkpoint14['unchanged_proof_modules'])} unchanged mini-checkpoint-14 proof modules.")
perfect = json.loads((ROOT / 'provenance/perfect-field-verschiebung.json').read_text())
for r in perfect['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
for r in perfect['vendor_additions']:
    assert historical_vendor_record(r['module']) == r
print(f"PASS: {len(perfect['new_modules'])} perfect-field V/Picard/cotangent modules and {len(perfect['vendor_additions'])} pinned additions.")

checkpoint15 = json.loads((ROOT / 'provenance/mini-checkpoint-15.json').read_text())
for r in checkpoint15['unchanged_proof_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
print(f"PASS: {len(checkpoint15['unchanged_proof_modules'])} unchanged mini-checkpoint-15 proof modules.")
comparison = json.loads((ROOT / 'provenance/frobenius-picard-comparison.json').read_text())
for r in comparison['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
for r in comparison['vendor_additions']:
    assert historical_vendor_record(r['module']) == r
print(f"PASS: {len(comparison['new_modules'])} line-bundle/Picard comparison modules and {len(comparison['vendor_additions'])} pinned additions.")

checkpoint16 = json.loads((ROOT / 'provenance/mini-checkpoint-16.json').read_text())
for r in checkpoint16['unchanged_proof_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
print(f"PASS: {len(checkpoint16['unchanged_proof_modules'])} unchanged mini-checkpoint-16 proof modules.")
cech = json.loads((ROOT / 'provenance/picard-cech-comparison.json').read_text())
for r in cech['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
assert cech['vendor_additions'] == [] and cech['new_compatibility_ports'] == []
print(f"PASS: {len(cech['new_modules'])} Picard/Cech comparison modules, recorded proof attribution, and no new vendor additions or ports.")

checkpoint17 = json.loads((ROOT / 'provenance/mini-checkpoint-17.json').read_text())
for r in checkpoint17['unchanged_proof_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
print(f"PASS: {len(checkpoint17['unchanged_proof_modules'])} unchanged mini-checkpoint-17 proof modules.")
repartition = json.loads((ROOT / 'provenance/cech-repartition-comparison.json').read_text())
for r in repartition['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
assert repartition['vendor_additions'] == [] and repartition['new_compatibility_ports'] == []
print(f"PASS: {len(repartition['new_modules'])} Cech/repartition comparison modules, attributed proofs and unchanged vendor closure.")

checkpoint18 = json.loads((ROOT / 'provenance/mini-checkpoint-18.json').read_text())
for r in checkpoint18['unchanged_proof_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
print(f"PASS: {len(checkpoint18['unchanged_proof_modules'])} unchanged mini-checkpoint-18 proof modules.")
residue = json.loads((ROOT / 'provenance/residue-duality-comparison.json').read_text())
for r in residue['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256']
for r in residue['vendor_additions']:
    assert historical_vendor_record(r['module']) == r
assert residue['new_compatibility_ports'] == []
print(f"PASS: {len(residue['new_modules'])} residue-duality comparison modules and {len(residue['vendor_additions'])} exact pinned additions, with proof attribution.")

checkpoint19 = json.loads((ROOT / 'provenance/mini-checkpoint-19.json').read_text())
for r in checkpoint19['unchanged_proof_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
assert len(checkpoint19['unchanged_vendor_modules']) == checkpoint19['unchanged_vendor_module_count']
for r in checkpoint19['unchanged_vendor_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
print(f"PASS: {len(checkpoint19['unchanged_proof_modules'])} unchanged mini-checkpoint-19 proof modules and {len(checkpoint19['unchanged_vendor_modules'])} unchanged vendor modules.")
cech_pullback = json.loads((ROOT / 'provenance/cech-pullback-vendor-additions.json').read_text())
assert cech_pullback['upstream_commit'] == manifest['commit']
for r in cech_pullback['vendor_additions']:
    assert historical_vendor_record(r['module']) == r
    assert r['upstream_sha256'] == r['current_sha256']
assert cech_pullback['new_compatibility_ports'] == []
assert set(cech_pullback['selected_roots']) <= set(manifest['roots'])
print(f"PASS: {len(cech_pullback['vendor_additions'])} exact pinned local-frame pullback additions, with no new compatibility ports.")

curve_naturality = json.loads((ROOT / 'provenance/cech-curve-naturality.json').read_text())
for r in curve_naturality['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
assert curve_naturality['new_compatibility_ports'] == []
print(f"PASS: {len(curve_naturality['new_modules'])} curve-pullback and Frobenius/Cech comparison modules with proof attribution.")

checkpoint20 = json.loads((ROOT / 'provenance/mini-checkpoint-20.json').read_text())
for r in checkpoint20['unchanged_proof_modules'] + checkpoint20['unchanged_vendor_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
continuation = json.loads((ROOT / 'provenance/checkpoint-21-sources.json').read_text())
for r in continuation['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
assert continuation['vendor_additions'] == []
assert continuation['new_compatibility_ports'] == []
expected_project = {r['path'] for r in checkpoint20['unchanged_proof_modules']}
expected_project.update(r['path'] for r in continuation['new_modules'])
checkpoint21 = json.loads((ROOT / 'provenance/mini-checkpoint-21.json').read_text())
for r in checkpoint21['unchanged_proof_modules'] + checkpoint21['unchanged_vendor_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
geometric22 = json.loads((ROOT / 'provenance/checkpoint-22-sources.json').read_text())
for r in geometric22['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
isogeny_vendor = json.loads((ROOT / 'provenance/geometric-isogeny-vendor-additions.json').read_text())
assert isogeny_vendor['upstream_commit'] == manifest['commit']
assert set(isogeny_vendor['roots']) <= set(manifest['roots'])
for r in isogeny_vendor['files']:
    assert historical_vendor_record(r['module']) == r, r['module']
expected_project.update(r['path'] for r in geometric22['new_modules'])
checkpoint22 = json.loads((ROOT / 'provenance/mini-checkpoint-22.json').read_text())
for r in checkpoint22['unchanged_proof_modules'] + checkpoint22['unchanged_vendor_lean_files']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
continuation23 = json.loads((ROOT / 'provenance/checkpoint-23-sources.json').read_text())
for r in continuation23['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
assert continuation23['vendor_additions'] == []
assert continuation23['new_compatibility_ports'] == []
expected_project.update(r['path'] for r in continuation23['new_modules'])
checkpoint23 = json.loads((ROOT / 'provenance/mini-checkpoint-23.json').read_text())
for r in checkpoint23['unchanged_proof_modules'] + checkpoint23['unchanged_vendor_lean_files']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
continuation24 = json.loads((ROOT / 'provenance/checkpoint-24-sources.json').read_text())
for r in continuation24['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
degree24 = json.loads((ROOT / 'provenance/checkpoint-24-degree-imports.json').read_text())
assert degree24['upstream_commit'] == manifest['commit']
assert set(degree24['roots']) <= set(manifest['roots'])
assert continuation24['vendor_additions'] == degree24['files']
for r in degree24['files']:
    assert historical_vendor_record(r['module']) == r, r['module']
for r in continuation24['new_compatibility_ports']:
    assert ported[r['path']] == r, r['path']
expected_project.update(r['path'] for r in continuation24['new_modules'])
checkpoint24 = json.loads((ROOT / 'provenance/mini-checkpoint-24.json').read_text())
for r in checkpoint24['unchanged_proof_modules'] + checkpoint24['unchanged_vendor_lean_files']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
continuation25 = json.loads((ROOT / 'provenance/checkpoint-25-sources.json').read_text())
for r in continuation25['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
assert continuation25['vendor_additions'] == []
assert continuation25['new_compatibility_ports'] == []
expected_project.update(r['path'] for r in continuation25['new_modules'])
checkpoint25 = json.loads((ROOT / 'provenance/mini-checkpoint-25.json').read_text())
for r in checkpoint25['unchanged_proof_modules'] + checkpoint25['unchanged_vendor_lean_files']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
continuation26 = json.loads((ROOT / 'provenance/checkpoint-26-sources.json').read_text())
for r in continuation26['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
quotient26 = json.loads((ROOT / 'provenance/checkpoint-26-quotient-imports.json').read_text())
assert quotient26['upstream_commit'] == manifest['commit']
assert set(quotient26['roots']) <= set(manifest['roots'])
assert continuation26['vendor_additions'] == quotient26['files']
assert continuation26['new_compatibility_ports'] == []
for r in quotient26['files']:
    assert historical_vendor_record(r['module']) == r, r['module']
    assert r['upstream_sha256'] == r['current_sha256']
expected_project.update(r['path'] for r in continuation26['new_modules'])
print(f"PASS: all {len(checkpoint25['unchanged_proof_modules'])} checkpoint-25 proof modules "
      f"and {len(checkpoint25['unchanged_vendor_lean_files'])} historical vendor Lean files are verified (documented port reversed); "
      f"{len(continuation26['new_modules'])} new modules and {len(quotient26['files'])} exact pinned additions verified.")
print(f"PASS: all {len(checkpoint24['unchanged_proof_modules'])} checkpoint-24 proof modules "
      f"and {len(checkpoint24['unchanged_vendor_lean_files'])} historical vendor Lean files are verified (documented port reversed); "
      f"{len(continuation25['new_modules'])} new checkpoint-25 modules have recorded hashes.")
print(f"PASS: all {len(checkpoint23['unchanged_proof_modules'])} checkpoint-23 proof modules "
      f"and {len(checkpoint23['unchanged_vendor_lean_files'])} historical vendor Lean files are verified (documented port reversed); "
      f"{len(continuation24['new_modules'])} new modules and {len(degree24['files'])} pinned additions verified.")

print(f"PASS: all {len(checkpoint22['unchanged_proof_modules'])} checkpoint-22 proof modules "
      f"and {len(checkpoint22['unchanged_vendor_lean_files'])} historical vendor Lean files are verified (documented port reversed); "
      f"{len(continuation23['new_modules'])} new continuation modules have recorded hashes.")
# Checkpoint 27 source inventory.
base27 = json.loads((ROOT / 'provenance/mini-checkpoint-26.json').read_text())
for r in base27['unchanged_proof_modules'] + base27['unchanged_vendor_lean_files']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
continuation27 = json.loads((ROOT / 'provenance/checkpoint-27-sources.json').read_text())
for r in continuation27['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
foundation27 = json.loads((ROOT / 'provenance/checkpoint-27-foundation-imports.json').read_text())
assert foundation27['upstream_commit'] == manifest['commit']
assert len({r['module'] for r in foundation27['files']}) == len(foundation27['files'])
assert {r['module'] for r in foundation27['files']} == set(json.loads((ROOT / 'provenance/mini-checkpoint-27.json').read_text())['vendor_modules']) - set(base27['vendor_modules'])
assert continuation27['vendor_additions'] == foundation27['files']
assert set(foundation27['roots']) <= set(manifest['roots'])
for r in continuation27['new_compatibility_ports']:
    assert ported[r['path']] == r, r['path']
for r in foundation27['files']:
    assert historical_vendor_record(r['module']) == r, r['module']
    if r['path'] not in ported:
        assert r['current_sha256'] == r['upstream_sha256']
expected_project.update(r['path'] for r in continuation27['new_modules'])
print(f"PASS: all {len(base27['unchanged_proof_modules'])} checkpoint-26 proof modules and {len(base27['unchanged_vendor_lean_files'])} historical vendor Lean files verified (documented port reversed); {len(continuation27['new_modules'])} new modules and {len(foundation27['files'])} exact pinned additions verified.")

# Checkpoint 28 source inventory.
base28 = json.loads((ROOT / 'provenance/mini-checkpoint-27.json').read_text())
for r in base28['unchanged_proof_modules'] + base28['unchanged_vendor_lean_files']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
continuation28 = json.loads((ROOT / 'provenance/checkpoint-28-sources.json').read_text())
for r in continuation28['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
foundation28 = json.loads((ROOT / 'provenance/checkpoint-28-foundation-imports.json').read_text())
assert foundation28['upstream_commit'] == manifest['commit']
assert len({r['module'] for r in foundation28['files']}) == len(foundation28['files'])
base29 = json.loads((ROOT / 'provenance/mini-checkpoint-28.json').read_text())
assert {r['module'] for r in foundation28['files']} == set(base29['vendor_modules']) - set(base28['vendor_modules'])
assert continuation28['vendor_additions'] == foundation28['files']
assert set(foundation28['roots']) <= set(manifest['roots'])
for r in continuation28['new_compatibility_ports']:
    assert ported[r['path']] == r, r['path']
for r in foundation28['files']:
    assert historical_vendor_record(r['module']) == r, r['module']
    if r['path'] not in ported:
        assert r['current_sha256'] == r['upstream_sha256']
expected_project.update(r['path'] for r in continuation28['new_modules'])
print(f"PASS: all {len(base28['unchanged_proof_modules'])} checkpoint-27 proof modules and {len(base28['unchanged_vendor_lean_files'])} historical vendor Lean files verified (documented port reversed); {len(continuation28['new_modules'])} new modules and {len(foundation28['files'])} exact pinned additions verified.")

# Checkpoint 29 source inventory.
for r in base29['unchanged_proof_modules'] + base29['unchanged_vendor_lean_files']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
continuation29 = json.loads((ROOT / 'provenance/checkpoint-29-sources.json').read_text())
foundation29 = json.loads((ROOT / 'provenance/checkpoint-29-foundation-imports.json').read_text())
assert foundation29['upstream_commit'] == manifest['commit']
assert {r['module'] for r in foundation29['files']} == set(modules) - set(base29['vendor_modules'])
assert continuation29['vendor_additions'] == foundation29['files']
assert continuation29['new_compatibility_ports'] == []
assert set(foundation29['roots']) <= set(manifest['roots'])
for r in foundation29['files']:
    assert historical_vendor_record(r['module']) == r
    assert r['current_sha256'] == r['upstream_sha256']
for r in continuation29['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
expected_project.update(r['path'] for r in continuation29['new_modules'])
print(f"PASS: all {len(base29['unchanged_proof_modules'])} checkpoint-28 project and {len(base29['unchanged_vendor_lean_files'])} historical vendor sources verified (documented port reversed); {len(continuation29['new_modules'])} new project and {len(foundation29['files'])} pinned vendor sources verified.")

# Checkpoint 30 source inventory; all checkpoint-29 proof sources are retained.
base30 = json.loads((ROOT / 'provenance/mini-checkpoint-29.json').read_text())
for r in base30['unchanged_proof_modules'] + base30['unchanged_vendor_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
continuation30 = json.loads((ROOT / 'provenance/checkpoint-30-sources.json').read_text())
assert continuation30['vendor_additions'] == []
assert continuation30['new_compatibility_ports'] == []
for r in continuation30['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
expected_project.update(r['path'] for r in continuation30['new_modules'])
print(f"PASS: all {len(base30['unchanged_proof_modules'])} checkpoint-29 project proof modules "
      f"and {len(base30['unchanged_vendor_modules'])} historical vendor Lean files verified (documented port reversed); "
      f"{len(continuation30['new_modules'])} new project modules, no vendor additions or ports.")

# Checkpoint 31 source inventory; preserve every checkpoint-30 proof module.
base31 = json.loads((ROOT / 'provenance/mini-checkpoint-30.json').read_text())
for r in base31['unchanged_proof_modules'] + base31['unchanged_vendor_lean_files']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
continuation31 = json.loads((ROOT / 'provenance/checkpoint-31-sources.json').read_text())
assert continuation31['vendor_additions'] == []
assert continuation31['new_compatibility_ports'] == []
for r in continuation31['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
expected_project.update(r['path'] for r in continuation31['new_modules'])
print(f"PASS: all {len(base31['unchanged_proof_modules'])} checkpoint-30 project proof modules "
      f"and {len(base31['unchanged_vendor_lean_files'])} historical vendor Lean files verified (documented port reversed); "
      f"{len(continuation31['new_modules'])} new project modules, no vendor additions or ports.")

# Checkpoint 32 source inventory; every prior project/vendor proof is retained.
base32 = json.loads((ROOT / 'provenance/mini-checkpoint-31.json').read_text())
for r in base32['unchanged_proof_modules'] + base32['unchanged_vendor_lean_files']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
continuation32 = json.loads((ROOT / 'provenance/checkpoint-32-sources.json').read_text())
assert continuation32['vendor_additions'] == []
assert continuation32['new_compatibility_ports'] == []
for r in continuation32['new_modules']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
for r in continuation32['draft_modules_excluded_from_build_and_proved_inventory']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
expected_project.update(r['path'] for r in continuation32['new_modules'])
assert len(continuation32['checked_public_theorems']) == 12
print(f"PASS: all {len(base32['unchanged_proof_modules'])} checkpoint-31 project proof modules "
      f"and {len(base32['unchanged_vendor_lean_files'])} historical vendor Lean files verified (documented port reversed); "
      f"{len(continuation32['new_modules'])} new checked modules and seven separately hashed unchecked drafts.")

# Checkpoint 33 promotes only modules that passed a focused build and audit.
base33 = json.loads((ROOT / 'provenance/mini-checkpoint-32.json').read_text())
for r in base33['unchanged_proof_modules'] + base33['unchanged_vendor_lean_files']:
    assert hashlib.sha256(historical_source_bytes(r['path'])).hexdigest() == r['sha256'], r['path']
continuation33 = json.loads((ROOT / 'provenance/checkpoint-33-sources.json').read_text())
assert continuation33['vendor_additions'] == []
assert {r['path'] for r in continuation33['new_compatibility_ports']} == set(CHECKPOINT_33_PORTS)
for r in continuation33['new_modules']:
    assert hashlib.sha256((ROOT / r['path']).read_bytes()).hexdigest() == r['sha256'], r['path']
expected_project.update(r['path'] for r in continuation33['new_modules'])
assert len(continuation33['project_proof_repairs']) == 1
print(f"PASS: checkpoint-32 sources reconstructed exactly; {len(continuation33['new_modules'])} "
      f"new checked modules, two reversible vendor proof ports and one project proof repair verified.")

assert expected_project == {p.relative_to(ROOT).as_posix()
                            for p in (ROOT / 'SupersingularCurves').rglob('*.lean')}
print(f"PASS: all {len(checkpoint20['unchanged_proof_modules'])} checkpoint-20 proof modules "
      f"and {len(checkpoint20['unchanged_vendor_modules'])} vendor Lean files match the attachment; "
      f"{len(continuation['new_modules'])} continuation modules have recorded hashes.")
print(f"PASS: all {len(checkpoint21['unchanged_proof_modules'])} checkpoint-21 proof modules "
      f"and {len(checkpoint21['unchanged_vendor_modules'])} historical vendor Lean files are verified (documented port reversed); "
      f"{len(geometric22['new_modules'])} geometric continuation modules have recorded hashes.")

checked = json.loads((ROOT / 'verification' / 'checked-source-hashes.json').read_text())
assert len({r['path'] for r in checked}) == len(checked)
for r in checked:
    assert hashlib.sha256((ROOT / r['path']).read_bytes()).hexdigest() == r['sha256'], r['path']
print(f'PASS: {len(checked)} current proof, example, build, audit, and provenance source hashes.')
