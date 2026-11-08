#!/usr/bin/env python3
"""Record only the five successfully compiled and audited checkpoint-32 modules."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
NAMES = [
    'ScalarFrobeniusTatePolarizedGraph', 'AbelianVerschiebungBinaryProducts',
    'FiniteBySectionsExternalProduct', 'PolarisationRootKernel', 'AbelianProductLineBundle',
]


def write_json(path, data):
    (ROOT / path).write_text(json.dumps(data, indent=2) + '\n')


def row(path):
    return {'path': str(path.relative_to(ROOT)),
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


build = (ROOT / 'verification/checkpoint-32-final-build.log').read_text()
audit = (ROOT / 'verification/checkpoint-32-audit.log').read_text()
assert 'Build completed successfully' in build
assert not re.search(r'^error:|: error', build, re.M)
match = re.search(r'Checkpoint 32 transitive axiom audit passed: (\d+) new project declaration entries', audit)
assert match and not re.search(r'^error:|: error', audit, re.M)
count = int(match.group(1))
assert count == 19
now = datetime.now(timezone.utc).isoformat()
base = json.loads((ROOT / 'provenance/mini-checkpoint-31.json').read_text())
assert len(base['unchanged_proof_modules']) == 335
assert len(base['unchanged_vendor_lean_files']) == 4667
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
                             'source': str(file.relative_to(ROOT)), 'origin': 'checkpoint-32-checked'})
assert len(theorems) == 12
inventory = json.loads((ROOT / 'verification/proved-theorems.json').read_text())
inventory = [r for r in inventory if r.get('origin') != 'checkpoint-32-checked']
assert len(inventory) == 1850
write_json('verification/proved-theorems.json', inventory + theorems)
draft_files = sorted((ROOT / 'drafts/checkpoint32/SupersingularCurves/Geometry').glob('*.lean'))
assert len(draft_files) == 7
assert sum(len(re.findall(r'(?m)^theorem ', p.read_text())) for p in draft_files) == 26
write_json('provenance/checkpoint-32-sources.json', {
    'checkpoint': 32, 'new_modules': [row(p) for p in files],
    'vendor_additions': [], 'new_compatibility_ports': [],
    'draft_modules_excluded_from_build_and_proved_inventory': [row(p) for p in draft_files],
    'checked_public_theorems': theorems,
})
status = json.loads((ROOT / 'verification/checkpoint-status.json').read_text())
status.update({
    'schema_version': 32, 'checkpoint': 32, 'date': now[:10],
    'build_exit_code': 0, 'audit_exit_code': 0, 'new_module_axiom_audit_exit_code': 0,
    'source_audit_exit_code': None, 'verification_completed_at_utc': now,
    'project_public_theorem_declarations': 1862,
    'checkpoint_newly_written_public_theorem_declarations': 9,
    'checkpoint_promoted_previously_unchecked_public_theorems': 3,
    'checkpoint_added_public_theorem_declarations': 12,
    'project_private_supporting_lemmas': 82, 'checkpoint_added_private_supporting_lemmas': 0,
    'project_proof_modules': 340, 'checkpoint_added_proof_modules': 5,
    'new_project_declaration_entries_audited': count,
    'retained_checkpoint_31_public_theorem_declarations': 1850,
    'full_aggregate_build_rerun': False,
    'current_build_targets': ['SupersingularCurves.Geometry.' + n for n in NAMES],
    'current_build_target': 'Five checkpoint-32 modules; see current_build_targets',
    'current_build_jobs': 11170,
    'verification_status': 'Twelve public theorems in five modules passed focused Lake compilation and the transitive axiom audit. Seven continuation files with 26 public theorem drafts remain unchecked and excluded.',
    'new_verification_scope': 'All twelve advertised theorems and all 19 stored declaration entries, including generated entries, their stored types/bodies, and transitive axioms. Earlier checked sources/caches reused.',
    'axiom_audit_scope': 'All 19 stored declaration entries in five new project modules; only propext, Classical.choice, and Quot.sound allowed transitively.',
    'checkpoint_geometric_bridge_scope': 'Constructed rational anti-isometry and isotropic actual integral graph from perfect alternating pairings on two surfaces; actual degree-controlled zero-dV quotient families and divisibility; zero-dV binary products; actual finite-by-sections product bundles; finite kernel of a polarization root.',
    'all_checkpoint_31_project_proof_modules_unchanged': True,
    'all_checkpoint_31_vendor_lean_files_unchanged': True,
    'actual_isotropic_graph_from_perfect_pairings_complete': True,
    'actual_binary_product_zero_dV_complete': True,
    'actual_finite_by_sections_external_product_complete': True,
    'actual_polarization_root_finite_kernel_complete': True,
    'actual_uniform_quotient_polarization_section_bounds_complete': False,
    'unchecked_draft_modules': 7, 'unchecked_draft_public_theorem_declarations': 26,
    'global_zero_dV_elliptic_map_complete': False,
    'finite_graph_quotient_models_from_zero_dV_complete': False,
    'global_zero_dV_product_isogeny_complete': False,
    'oort_integral_splitting_complete': False,
    'geometric_classification_block_complete': False,
    'full_iko_section_1_complete': False,
    'latest_recompilation': {'completed_at_utc': now, 'all_current_checks_passed': False,
        'verification_mode': 'Focused build and axiom audit passed; source integrity/admission checks run next.',
        'record': 'verification/checkpoint-32-run.json'},
})
write_json('verification/checkpoint-status.json', status)
write_json('verification/checkpoint-32-run.json', {
    'checkpoint': 32, 'completed_at_utc': now,
    'build_targets': status['current_build_targets'], 'build_exit_code': 0, 'audit_exit_code': 0,
    'source_audit_exit_code': None, 'public_theorems_checked': 12,
    'stored_declaration_entries_audited': count,
    'standard_axiom_allowlist': ['propext', 'Classical.choice', 'Quot.sound'],
    'original_project_sources_unchanged': 335, 'original_vendor_lean_files_unchanged': 4667,
    'full_aggregate_rerun': False, 'historical_examples_rerun': False,
    'draft_modules_not_checked': 7, 'draft_public_theorems_not_checked': 26,
    'draft_build_blocker': 'Pinned upstream torsion-density dependency exceeded the 8 GiB workspace memory limit during import/initialization. Drafts were not reached.',
    'diagnostics_certified': False,
    'compiler_source_and_vendor_proof_sources_modified': False,
})

body = '''# Checkpoint 32 — checked isotropic graph and polarization foundations

**Block 1 is not complete.** The unconditional elliptic-map theorem and global
supersingular product-isogeny theorem remain open.

Twelve newly checked public theorems in five modules passed normal focused
Lake compilation and a transitive axiom audit. Nine are newly written; three
root-kernel lemmas were promoted from the previously unchecked numerical draft.

## What is now proved

1. **Isotropic graphs from perfect alternating pairings.** For two actual
   abelian surfaces over an algebraically closed field and an auxiliary prime
   different from the characteristic,
   perfect alternating integral Tate pairings construct a rational
   anti-isometry. Its graph has the required rank and integral complement.
   The original integral product pairing vanishes on the actual integral
   graph intersection. The pairings are inputs here; their realization by
   actual line bundles is still in the unchecked assembly.
2. **Actual graph quotient families.** The resulting family has residual
   isogeny degrees `(ell^n)^4`, inherits zero actual dV when the product has
   zero dV, and has the pairing divisibility needed for the proposed root
   construction. An anti-isometry is constructed rather than assumed.
3. **Zero dV on actual binary products.** Over perfect fields, in arbitrary dimensions, zero dV
   on both factors implies zero dV on their actual scheme-theoretic product.
   The supporting differential-detection theorem uses square-zero points
   and the actual product's universal property.
4. **Finite projective presentations on products.** An actual Segre
   construction shows that exterior tensor products of bundles finite by
   sections are finite by sections on the scheme fibre product. The actual
   abelian product bundle is constructed and proved invertible and finite
   by sections from the corresponding properties on the factors.
5. **Finite set of translation-kernel points of a root.** For an invertible root R with
   `M ≅ R^n ⊗ P` and `P` in Pic0, finiteness of the set `kernelPts(M)`
   implies finiteness of `kernelPts(R)`. Kernel invariance under sheaf isomorphism and
   inclusion under tensor powers are also checked.

These statements concern actual schemes, maps, line bundles and Tate modules.
They do not identify finite projective maps with closed immersions.

## Verification and preservation

`bash verification/verify_checkpoint32.sh` reproduces the focused build,
declaration audit, source-integrity check and admission scan. All twelve
advertised theorem names and all 19 stored declaration entries in the five
new modules were audited, including generated entries, stored types/bodies
and transitive dependencies. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed. No new axiom or proof admission was introduced.

All 335 previous project proof modules and all 4,667 vendor Lean files remain
byte-identical to checkpoint 31. The checked inventory is now 340 project
proof modules, 1,862 public theorems and 82 private supporting lemmas. Those
counts measure declarations, not a completion percentage. The full aggregate
build and historical example suite were not rerun.

## Work that is still unchecked or unproved

Seven continuation files with 26 public theorem drafts are preserved under
`drafts/checkpoint32/`, outside the build and proved inventory. They include
the exact root-section scaling, cancellation against isogeny degrees,
construction of common actual Riemann pairings, the uniform symmetric-bundle
assembly, and the conditional descent/moduli assembly. The new assembly keeps
one quotient family throughout and attempts to choose its starting bundles.
These files have not passed Lean and must not be counted as completed.

The broader build failed before reaching them. Loading the pinned upstream
torsion-density dependency exceeded the workspace's 8 GiB memory limit.
Single-compiler scheduling, synchronous elaboration, and direct compilation
did not resolve that import problem. No diagnostic experiment is certified.
Completed dependencies are preserved in the expanded partial build cache.

The mathematical route still needs checked uniform section bounds, a uniform
very-ampleness/closed-immersion theorem for the resulting nonprincipal
polarizations, and the actual finite-model conclusion `HasFiniteModels`.
Finiteness of a polarization kernel does not imply `KernelTrivial`.
The previously checked finite-model-to-elliptic-map and product-isogeny chain
becomes applicable only after those hypotheses are proved. Integral splitting
is a further requirement for the superspecial product isomorphism. Neither
positive geometric Cartier converse, Block 1, nor the full IKO/Newton project
is finished by this checkpoint.

The separate cache and environment note document the pinned compiler/packages
and reuse procedure. Proof sources and their audits remain authoritative.
'''
(ROOT / 'CONTINUATION_STATUS.md').write_text(body)
(ROOT / 'verification/CHECKPOINT_32_REPORT.md').write_text(body)
(ROOT / 'provenance/checkpoint-32-polarized-graphs.md').write_text(body)
for filename, prefix in [
    ('README.md', '# Checkpoint 32: checked isotropic graphs and product polarizations\n\nTwelve new public theorems in five modules are compiled and axiom-audited.\nBlock 1 remains incomplete. Seven continuation files are explicitly unchecked.\nRun `bash verification/verify_checkpoint32.sh`; see `CONTINUATION_STATUS.md`\nfor the exact results, build blocker and remaining mathematical gaps.\nThe sections below are historical.\n\n'),
    ('SECTION1_COVERAGE.md', '# Checkpoint 32 — current scope\n\nNew checked results construct isotropic actual graphs from perfect pairings,\nzero-dV binary products, actual finite-by-sections product line bundles, and\nfinite translation kernels for polarization roots. Uniform numerical bounds,\nvery ampleness, finite models, the unconditional elliptic map, and integral\nsuperspecial splitting remain open or unchecked. IKO section 1 and both\npositive geometric Cartier converses are not complete. Earlier coverage\nnotes below retain their historical scope.\n\n'),
]:
    p = ROOT / filename
    old = p.read_text()
    if not old.startswith('# Checkpoint 32'):
        p.write_text(prefix + old)

checked = json.loads((ROOT / 'verification/checked-source-hashes.json').read_text())
paths = {r['path'] for r in checked}
paths.update(str(p.relative_to(ROOT)) for p in files)
paths.update([
    'provenance/mini-checkpoint-31.json', 'provenance/checkpoint-32-sources.json',
    'provenance/checkpoint-32-polarized-graphs.md', 'verification/Checkpoint32Audit.lean',
    'verification/verify_checkpoint32.sh', 'verification/finalize_checkpoint32.py',
    'verification/CHECKPOINT_32_REPORT.md',
    'verification/environment/CHECKPOINT_32_ENVIRONMENT.md',
    'verification/environment/checkpoint32-runtime-compat.c',
    'verification/environment/checkpoint32-runtime-launcher.py',
])
write_json('verification/checked-source-hashes.json', [row(ROOT / p) for p in sorted(paths)])
print('Recorded twelve checked theorems and 19 audited entries; run source checks next.')
