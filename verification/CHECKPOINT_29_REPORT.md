# Checkpoint 29 — checked elliptic subgroup constructions

**The subgroup construction from an actual nonzero elliptic map is finished in
both directions. The unconditional global existence theorem is not finished,
so Block 1 remains incomplete.**

## New checked results

Let K be algebraically closed and A an actual abelian surface. Given an actual
group-scheme morphism E → A or A → E, with E an elliptic abelian variety and
nonzero induced rational Tate map, Lean now constructs a genuine smooth
connected closed subgroup of A of dimension one.

For E → A, it is the scheme-theoretic image. Reducedness, the group law,
smoothness, connectedness, and dimension are proved. For A → E, it is the
reduced identity component of the actual kernel; dimension one is a conclusion,
not an input.

This closes the geometric construction after either direction of the existing
Tate cross-morphism extraction. Given the existing nonzero graph operator in
the span of actual endomorphisms, and p-rank zero for A, the final theorem
produces actual supersingular elliptic factors E₁ and E₂ and actual isogenies
E₁ × E₂ → A and A → E₁ × E₂. It proves the original independent
`A.IsSupersingularOver p` predicate.

Principal new declarations, under `SupersingularCurves.Geometry`:

- `AbelianVariety.exists_closed_elliptic_subgroup_of_rationalMap_ne_zero`
- `AbelianVariety.exists_closed_elliptic_subgroup_of_to_elliptic_rationalMap_ne_zero`
- `ScalarFrobeniusTate.exists_closed_elliptic_subgroup_of_actualEndSpan_graph`
- `ScalarFrobeniusTate.exists_supersingular_product_isogenies_of_actualEndSpan_graph`
- `ScalarFrobeniusTate.isSupersingularOver_of_actualEndSpan_graph`

The source map and proof details are in
`provenance/checkpoint-29-elliptic-subgroup.md`.

## Still required for Block 1

1. Prove that every zero-dV surface supplies the nonzero actual elliptic map
   (the missing graph-operator existence step is the current route to this). Uniformly bounded very ample polarizations for the
   actual nonprincipal quotient roots, finite-model recurrence, and normalized
   actual operators remain to be constructed.
2. Prove the integral splitting needed to upgrade an isogeny to the
   superspecial product isomorphism.
3. Apply these classification results to the retained Cartier/Verschiebung
   comparison and the retained square-zero-to-zero-dV isogeny construction.

Thus C = 0 ⇒ geometric superspeciality and C² = 0 ⇒ geometric supersingularity
remain unproved in their full intended scope. The new results do not assume
either conclusion or redefine supersingularity. The other IKO §1 and crystalline
Newton comparison gaps are unchanged.

## Verification

- The new final module and its import closure build successfully: 11,115 Lake
  jobs, including reused dependencies. All five new project modules compile.
- All 16 new public theorem names resolve to theorem declarations.
- All 28 stored declaration entries from the five new project modules and
  four new vendor modules pass the transitive axiom audit, including generated
  entries and stored types and bodies. The only allowed axioms are `propext`,
  `Classical.choice`, and `Quot.sound`.
- All 323 checkpoint-28 project proof files and 4,662 vendor Lean files are
  byte-identical. The original geometric definitions are unchanged.
- Source integrity and the admission/native-evaluation scan cover all 4,995
  project, aggregate, and vendor Lean source files.

The current inventory contains 328 project proof modules, 1,825 public theorem
declarations, 82 private supporting lemmas, and 4,666 pinned vendor modules.
Five project modules and 16 public theorems are new. There are no new
compatibility ports. These counts are not a completion percentage.

Run `bash verification/verify_checkpoint29.sh` with the pinned Lean
4.34.0-rc2 toolchain and package lock. This is a targeted build of the new
geometric chain and its dependencies; the full aggregate, historical example
suites, and historical audits were not rerun. Their source-identical prior
evidence is retained. Exact current check results and log hashes are in
`verification/checkpoint-29-run.json`.
