#!/usr/bin/env python3
"""Record checkpoint 31 only after its canonical build and axiom audit pass."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
NAMES = ['ScalarFrobeniusTateQuotientDegree', 'ScalarFrobeniusTateQuotientPairing',
         'ScalarFrobeniusTateGraphQuotients']


def write_json(path, data):
    (ROOT / path).write_text(json.dumps(data, indent=2) + '\n')


def row(path):
    return {'path': str(path.relative_to(ROOT)),
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


build = (ROOT / 'verification/checkpoint-31-final-build.log').read_text()
audit = (ROOT / 'verification/checkpoint-31-audit.log').read_text()
assert 'Build completed successfully' in build
assert not re.search(r'^error:|: error', build, re.M)
match = re.search(r'Checkpoint 31 transitive axiom audit passed: (\d+) new project declaration entries', audit)
assert match and not re.search(r'^error:|: error', audit, re.M)
count = int(match.group(1))
now = datetime.now(timezone.utc).isoformat()
base = json.loads((ROOT / 'provenance/mini-checkpoint-30.json').read_text())
for old in base['unchanged_proof_modules'] + base['unchanged_vendor_lean_files']:
    assert row(ROOT / old['path'])['sha256'] == old['sha256'], old['path']

files = [ROOT / 'SupersingularCurves/Geometry' / (name + '.lean') for name in NAMES]
theorems = []
for file in files:
    ns = ''
    for line in file.read_text().splitlines():
        if line.startswith('namespace '):
            ns = line[len('namespace '):].strip()
        found = re.match(r'(?:@\[[^]]*\]\s*)?theorem ([\w.]+)', line)
        if found:
            theorems.append({'name': ns + '.' + found.group(1),
                             'source': str(file.relative_to(ROOT)), 'origin': 'checkpoint-31-checked'})
assert len(theorems) == 10
inventory = json.loads((ROOT / 'verification/proved-theorems.json').read_text())
inventory = [r for r in inventory if r.get('origin') != 'checkpoint-31-checked']
assert len(inventory) == 1840
write_json('verification/proved-theorems.json', inventory + theorems)
draft_files = sorted((ROOT / 'drafts/checkpoint31/SupersingularCurves/Geometry').glob('*.lean'))
assert len(draft_files) == 5
write_json('provenance/checkpoint-31-sources.json', {
    'checkpoint': 31, 'new_modules': [row(p) for p in files],
    'vendor_additions': [], 'new_compatibility_ports': [],
    'draft_modules_excluded_from_build_and_proved_inventory': [row(p) for p in draft_files],
})
status = json.loads((ROOT / 'verification/checkpoint-status.json').read_text())
status.update({
    'schema_version': 31, 'checkpoint': 31, 'date': '2026-09-28',
    'build_exit_code': 0, 'audit_exit_code': 0, 'source_audit_exit_code': None,
    'project_public_theorem_declarations': 1850,
    'checkpoint_newly_written_public_theorem_declarations': 10,
    'checkpoint_added_public_theorem_declarations': 10,
    'project_private_supporting_lemmas': 82, 'checkpoint_added_private_supporting_lemmas': 0,
    'project_proof_modules': 335, 'checkpoint_added_proof_modules': 3,
    'new_project_declaration_entries_audited': count,
    'retained_checkpoint_30_public_theorem_declarations': 1840,
    'full_aggregate_build_rerun': False,
    'current_build_target': 'SupersingularCurves.Geometry.ScalarFrobeniusTateGraphQuotients',
    'current_build_jobs': None,
    'verification_status': 'Ten new public theorems passed the canonical focused build and transitive axiom audit. Five root/descent/moduli modules with 22 public theorem drafts are unchecked and excluded from the build and proved inventory.',
    'new_verification_scope': f'Three canonical modules and all {count} stored declaration entries audited, including generated declarations and transitive types/bodies. Prior checked sources and caches reused.',
    'checkpoint_geometric_bridge_scope': 'Actual rational graph intersections now supply integral complements and half-ranks. Actual graph quotient families have exact degrees and inherit zero dV. Isotropy implies divisibility on actual Tate images. Finite models from zero dV and the unconditional elliptic-map theorem remain open.',
    'all_checkpoint_30_project_proof_modules_unchanged': True,
    'all_checkpoint_30_vendor_lean_files_unchanged': True,
    'actual_half_rank_quotient_residual_degree_complete': True,
    'actual_graph_integral_rank_and_complement_complete': True,
    'actual_graph_quotient_family_with_degree_and_zero_dV_complete': True,
    'actual_quotient_tate_pairing_divisibility_from_isotropy_complete': True,
    'checkpoint_31_polarization_root_numerics_checked': False,
    'checkpoint_31_uniform_rank_descent_moduli_assembly_checked': False,
    'unchecked_draft_modules': 5, 'unchecked_draft_public_theorem_declarations': 22,
    'global_zero_dV_elliptic_map_complete': False,
    'finite_graph_quotient_models_from_zero_dV_complete': False,
    'global_zero_dV_product_isogeny_complete': False,
    'oort_integral_splitting_complete': False,
    'full_iko_section_1_complete': False,
    'latest_recompilation': {'completed_at_utc': now, 'all_current_checks_passed': False,
        'verification_mode': 'Canonical focused build and axiom audit passed; source checks run next.',
        'record': 'verification/checkpoint-31-run.json'},
})
write_json('verification/checkpoint-status.json', status)
write_json('verification/checkpoint-31-run.json', {
    'checkpoint': 31, 'completed_at_utc': now,
    'build_target': status['current_build_target'], 'build_exit_code': 0, 'audit_exit_code': 0,
    'public_theorems_checked': 10, 'stored_declaration_entries_audited': count,
    'standard_axiom_allowlist': ['propext', 'Classical.choice', 'Quot.sound'],
    'original_project_sources_unchanged': 332, 'original_vendor_lean_files_unchanged': 4667,
    'full_aggregate_rerun': False, 'historical_examples_rerun': False,
    'draft_modules_not_checked': 5, 'draft_public_theorems_not_checked': 22,
    'abandoned_experiment': 'Combined-source checking did not preserve upstream module isolation; no result from that experiment is certified.',
    'initial_broader_build': 'Interrupted while rebuilding missing dependencies; never reached the five draft modules.',
})

body = f'''# Checkpoint 31 — actual graph quotient degrees and divisibility

**Block 1 is not complete. Every zero-dV surface having an elliptic map is still unproved.**

Ten new public theorems in three modules have passed normal Lean compilation and
the transitive axiom audit. They establish:

- Equal half-degrees for the actual factors of multiplication, and degree
  `(ell^n)^g` for the residual maps in a prescribed half-rank quotient family.
- Divisibility of a bilinear pairing by `ell^n` on `U + ell^n T` when it vanishes
  on `U`, including on the actual quotient Tate images.
- A degree-controlled family whose members inherit zero actual dV, using the
  previously proved prime-to-characteristic preservation theorem.
- The actual integral rational-graph intersection has a complement and the
  required rank. These are derived, not supplied as additional assumptions.
- Rational isotropy gives integral isotropy for the unchanged original pairing.
- Actual graph quotient families with the exact degree and zero dV.

For two g-dimensional varieties, the graph construction concerns their
2g-dimensional product, so the residual degree is `(ell^n)^(g+g)`. The final
graph-family theorem assumes an actual rational Tate isomorphism and zero dV
on the product. It does not assert finitely many isomorphism classes.

## Verification

`lake build SupersingularCurves.Geometry.ScalarFrobeniusTateGraphQuotients`
and `lake env lean verification/Checkpoint31Audit.lean` passed. All ten named
theorems and all {count} stored declaration entries in the three new modules were
audited, including generated declarations, stored types/bodies and transitive
dependencies. The only allowed axioms are `propext`, `Classical.choice`, and
`Quot.sound`. Source-integrity and admission scans are separate recorded checks.
The full aggregate and historical examples were not rerun.

All 332 previous project proof modules and all 4,667 vendor Lean files (including
the vendor lakefile) remain byte-identical. The checked project has 335 proof
modules and 1,850 public theorem declarations. These are inventories, not a
percentage of the mathematical goal completed.

## Unchecked work and the remaining gap

Five additional root/numerical/descent/moduli modules, containing 22 public
theorem drafts, are preserved under `drafts/checkpoint31/`. They have **not** passed
Lean and are excluded from the project import tree and proved inventory.
The initial broader build was blocked by more than 1,500 missing compiled
dependencies in the restored partial cache. A combined-source experiment was
abandoned because the upstream files rely on separate module environments.
No successful proof result is claimed for that experiment.

The remaining route requires checked numerical bounds for the actual quotient
roots, a uniform very-ampleness theorem for the nonprincipal polarizations,
and the finite-field descent/moduli assembly proving `HasFiniteModels` for a
suitable graph family. The available theorem with `KernelTrivial` cannot be
applied merely from a finite polarization kernel. The unconditional elliptic
map and product isogeny therefore remain open. Oort integral splitting is a
further requirement for the superspecial product isomorphism. Both positive
geometric Cartier converses, Block 1, and the full IKO/Newton project remain
unfinished.

Reproduce the checked additions with `bash verification/verify_checkpoint31.sh`.
The compiler and external package revisions remain pinned. The separate build
cache is partial; use the matching Mathlib cache as documented in the environment
restoration note. Do not count the drafts as completed work.
'''
(ROOT / 'CONTINUATION_STATUS.md').write_text(body)
(ROOT / 'verification/CHECKPOINT_31_REPORT.md').write_text(body)
(ROOT / 'provenance/checkpoint-31-quotient-graphs.md').write_text(body)
readme = ROOT / 'README.md'
old = readme.read_text()
if not old.startswith('# Checkpoint 31'):
    readme.write_text('''# Checkpoint 31: checked graph quotient step

The actual quotient degrees, rational-graph integral rank/complement, pairing
divisibility and degree-controlled zero-dV quotient families are checked.
There are ten new public theorems in three modules. Block 1 and the global
zero-dV elliptic-map theorem remain incomplete. Five further modules are
explicitly unchecked drafts, outside the project import tree.

Run `bash verification/verify_checkpoint31.sh`. See `CONTINUATION_STATUS.md`
and `verification/CHECKPOINT_31_REPORT.md` for the exact scope and evidence.
The following older sections are historical.

'''+old)
coverage = ROOT / 'SECTION1_COVERAGE.md'
old = coverage.read_text()
if not old.startswith('# Checkpoint 31'):
    coverage.write_text('''# Checkpoint 31 — current scope

The graph quotient construction now includes derived integral complement and
rank, exact residual degree, inherited zero dV, and Tate pairing divisibility.
The uniform numerical/very-ampleness bound and finite-model assembly remain
unchecked or unproved. Both positive geometric Cartier converses and Block 1
remain incomplete. IKO §1 and Newton-polygon coverage otherwise stays unchanged.
Five continuation modules are unchecked drafts, excluded from all proved counts.
Current verification is `verification/verify_checkpoint31.sh`; earlier coverage
descriptions below retain their historical scope.

'''+old)
checked = json.loads((ROOT / 'verification/checked-source-hashes.json').read_text())
paths = {r['path'] for r in checked}
paths.update(str(p.relative_to(ROOT)) for p in files)
paths.update(['provenance/mini-checkpoint-30.json', 'provenance/checkpoint-31-sources.json',
              'provenance/checkpoint-31-quotient-graphs.md', 'verification/Checkpoint31Audit.lean',
              'verification/verify_checkpoint31.sh', 'verification/finalize_checkpoint31.py',
              'verification/CHECKPOINT_31_REPORT.md',
              'verification/environment/CHECKPOINT_31_ENVIRONMENT.md',
              'verification/environment/self-exe-compat.c'])
write_json('verification/checked-source-hashes.json', [row(ROOT / p) for p in sorted(paths)])
print(f'Recorded ten checked theorems and {count} audited entries; source checks must now run.')
