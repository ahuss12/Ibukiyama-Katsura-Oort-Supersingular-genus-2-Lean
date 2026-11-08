#!/usr/bin/env python3
"""Record checkpoint 33 only after its focused build and declaration audit pass."""
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
BASE_NAMES = [
    'PolarisationRootNumerics', 'AbelianIsogenyRootNumerics',
    'AbelianTateProductPolarization', 'ScalarFrobeniusTateQuotientRoots',
    'ScalarFrobeniusTateUniformPolarization',
]
CONDITIONAL_NAMES = ['ScalarFrobeniusPolarizedDescentRank', 'PolarizedFiniteModels']


def read_json(path):
    return json.loads((ROOT / path).read_text())


def write_json(path, data):
    (ROOT / path).write_text(json.dumps(data, indent=2) + '\n')


def row(path):
    return {'path': path.relative_to(ROOT).as_posix(),
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--include-finite-models', action='store_true')
    args = parser.parse_args()
    names = BASE_NAMES + (CONDITIONAL_NAMES if args.include_finite_models else [])
    expected_public = 26 if args.include_finite_models else 22
    build = (ROOT / 'verification/checkpoint-33-final-build.log').read_text()
    audit = (ROOT / 'verification/checkpoint-33-audit.log').read_text()
    repairs_audit = (ROOT / 'verification/checkpoint-33-repairs-audit.log').read_text()
    for label, content in [('build', build), ('audit', audit), ('repairs', repairs_audit)]:
        assert not re.search(r'^error:|: error|exited with code [1-9]', content, re.M), label
    assert 'Build completed successfully' in build
    match = re.search(r'Checkpoint 33 transitive axiom audit passed: (\d+) new project declaration entries', audit)
    assert match, 'New-module audit did not pass'
    count = int(match.group(1))
    for name in names:
        assert f'declarations from SupersingularCurves.Geometry.{name}.' in audit
    assert 'Density proof port:' in repairs_audit
    files = [ROOT / 'SupersingularCurves/Geometry' / f'{name}.lean' for name in names]
    theorems = []
    for file in files:
        module_path = file.relative_to(ROOT).with_suffix('')
        assert (ROOT / '.lake/build/lib/lean' / module_path.with_suffix('.olean')).is_file()
        trace = read_json(str(Path('.lake/build/lib/lean') / module_path.with_suffix('.trace')))
        assert trace.get('outputs', {}).get('o'), file
        namespace = ''
        for line in file.read_text().splitlines():
            if line.startswith('namespace '):
                namespace = line[10:].strip()
            found = re.match(r'(?:@\[[^]]*\]\s*)?theorem ([\w.]+)', line)
            if found:
                theorems.append({'name': namespace + '.' + found.group(1),
                                 'source': file.relative_to(ROOT).as_posix(),
                                 'origin': 'checkpoint-33-checked'})
    assert len(theorems) == expected_public
    base = read_json('provenance/mini-checkpoint-32.json')
    project_repairs = read_json('provenance/checkpoint-33-project-repairs.json')
    by_path = {r['path']: r for r in project_repairs}
    for old in base['unchanged_proof_modules']:
        current = row(ROOT / old['path'])['sha256']
        if current != old['sha256']:
            repair = by_path[old['path']]
            assert current == repair['new_sha256'] and old['sha256'] == repair['prior_sha256']
            assert hashlib.sha256(repair['old'].encode()).hexdigest() == old['sha256']
            assert hashlib.sha256(repair['new'].encode()).hexdigest() == current
    ports = read_json('vendor/flt/port-manifest.json')['files']
    new_ports = []
    for old in base['unchanged_vendor_lean_files']:
        current = row(ROOT / old['path'])['sha256']
        if current != old['sha256']:
            port = next(r for r in ports if 'vendor/flt/' + r['path'] == old['path'])
            assert port['ported_sha256'] == current
            source = (ROOT / old['path']).read_text()
            for replacement in reversed(port['replacements']):
                assert source.count(replacement['new']) == 1
                source = source.replace(replacement['new'], replacement['old'])
            assert hashlib.sha256(source.encode()).hexdigest() == old['sha256']
            new_ports.append(port)
    inventory = [r for r in read_json('verification/proved-theorems.json')
                 if r.get('origin') != 'checkpoint-33-checked']
    assert len(inventory) == 1862
    write_json('verification/proved-theorems.json', inventory + theorems)
    now = datetime.now(timezone.utc).isoformat()
    remainder = [] if args.include_finite_models else CONDITIONAL_NAMES
    write_json('provenance/checkpoint-33-sources.json', {
        'checkpoint': 33, 'new_modules': [row(p) for p in files],
        'vendor_additions': [], 'new_compatibility_ports': new_ports,
        'project_proof_repairs': project_repairs,
        'checked_public_theorems': theorems,
        'remaining_unchecked_draft_modules': remainder,
        'historical_checkpoint_32_drafts_retained_unchanged': True,
    })
    aggregate = ROOT / 'SupersingularCurves.lean'
    body = aggregate.read_text()
    for name in names:
        item = 'import SupersingularCurves.Geometry.' + name
        if item not in body:
            body += item + '\n'
    aggregate.write_text(body)
    status = read_json('verification/checkpoint-status.json')
    status.update({
        'schema_version': 33, 'checkpoint': 33, 'date': now[:10],
        'build_exit_code': 0, 'audit_exit_code': 0, 'new_module_axiom_audit_exit_code': 0,
        'source_audit_exit_code': None, 'verification_completed_at_utc': now,
        'project_public_theorem_declarations': 1862 + expected_public,
        'checkpoint_newly_written_public_theorem_declarations': 0,
        'checkpoint_promoted_previously_unchecked_public_theorems': expected_public,
        'checkpoint_added_public_theorem_declarations': expected_public,
        'project_private_supporting_lemmas': 83, 'checkpoint_added_private_supporting_lemmas': 1,
        'project_proof_modules': 340 + len(names), 'checkpoint_added_proof_modules': len(names),
        'new_project_declaration_entries_audited': count,
        'retained_checkpoint_32_public_theorem_declarations': 1862,
        'full_aggregate_build_rerun': False,
        'current_build_targets': ['SupersingularCurves.Geometry.' + n for n in names],
        'current_build_target': 'Focused checkpoint-33 continuation; see current_build_targets',
        'verification_status': f'{expected_public} newly checked public theorems passed focused Lean compilation and a transitive axiom audit.',
        'new_verification_scope': 'All advertised public theorems and all stored declarations in the new modules, plus separate audits of repaired proofs. Earlier checked source/cache pairs reused.',
        'axiom_audit_scope': 'All stored declarations in the new project modules and mathematical declarations in repaired vendor modules; only propext, Classical.choice, and Quot.sound allowed transitively.',
        'all_checkpoint_31_project_proof_modules_unchanged': False,
        'all_checkpoint_31_vendor_lean_files_unchanged': False,
        'checkpoint_32_project_proof_modules_unchanged': 340 - len(project_repairs),
        'checkpoint_32_vendor_lean_files_unchanged': 4667 - len(new_ports),
        'actual_uniform_quotient_polarization_section_bounds_complete': True,
        'finite_models_from_uniform_very_ampleness_complete': args.include_finite_models,
        'unchecked_draft_modules': len(remainder),
        'unchecked_draft_public_theorem_declarations': 0 if args.include_finite_models else 4,
        'global_zero_dV_elliptic_map_complete': False,
        'finite_graph_quotient_models_from_zero_dV_complete': False,
        'global_zero_dV_product_isogeny_complete': False,
        'oort_integral_splitting_complete': False,
        'geometric_classification_block_complete': False, 'full_iko_section_1_complete': False,
        'latest_recompilation': {'completed_at_utc': now, 'all_current_checks_passed': False,
            'verification_mode': 'Focused builds and axiom audits passed; source checks follow.',
            'record': 'verification/checkpoint-33-run.json'},
    })
    status.pop('current_build_jobs', None)
    write_json('verification/checkpoint-status.json', status)
    write_json('verification/checkpoint-33-run.json', {
        'checkpoint': 33, 'completed_at_utc': now,
        'build_targets': status['current_build_targets'],
        'build_exit_code': 0, 'audit_exit_code': 0, 'source_audit_exit_code': None,
        'public_theorems_checked': expected_public, 'stored_declaration_entries_audited': count,
        'standard_axiom_allowlist': ['propext', 'Classical.choice', 'Quot.sound'],
        'original_project_sources_unchanged': 340 - len(project_repairs),
        'original_vendor_sources_unchanged': 4667 - len(new_ports),
        'documented_project_proof_repairs': len(project_repairs),
        'documented_vendor_proof_ports': len(new_ports),
        'full_aggregate_rerun': False, 'historical_examples_rerun': False,
        'draft_modules_not_checked': len(remainder),
        'compiler_modified': False, 'diagnostics_certified': False,
        'build_mode': 'Hash-verified old cache, targeted lake --old build, new modules normally kernel checked.',
    })
    print(f'Recorded {expected_public} checked public theorems; finalize reports and source hashes, then run the source audits.')


if __name__ == '__main__':
    main()
