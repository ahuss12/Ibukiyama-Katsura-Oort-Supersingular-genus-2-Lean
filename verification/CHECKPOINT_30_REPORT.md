# Checkpoint 30 — recurrence and compactness checked

**The global theorem “every zero-dV surface has the required elliptic map” is still unproved. The isogeny classification and Block 1 are not closed.**

This checkpoint proves the remaining recurrence/compactness implication:

> Finitely many actual graph-quotient models imply a genuine nonzero elliptic map; for a p-rank-zero surface they imply actual supersingular elliptic-product isogenies in both directions.

The proof constructs actual endomorphisms from quotient isogenies, takes an integral p-adic limit, proves that the limit is nonzero, and proves that it stays in the rational span of actual geometric endomorphisms. It then applies the checked graph extraction, elliptic-subgroup construction, and product-complement results. The nonzero graph operator is now a conclusion under the finite-model hypothesis.

## What remains

The explicit input `PrescribedLatticeQuotients.HasFiniteModels` must still be proved for a suitable graph-quotient family arising from a zero-dV surface. The intended route needs a uniform projective closed-immersion bound for the actual nonprincipal quotient-root polarizations, the accompanying numerical estimates, and the finite-field descent/moduli assembly. The available principal-polarization theorem cannot be applied: its `KernelTrivial` hypothesis is stronger than a finite polarization kernel.

Consequently the unconditional zero-dV elliptic-map theorem, the unconditional product-isogeny result, both positive geometric Cartier converses, and Block 1 remain open. Oort's integral splitting for a product isomorphism is a further unresolved part. The IKO/Newton scope is unchanged.

Zero-dV preservation under the relevant prime-to-characteristic quotient maps was already proved in `VerschiebungPrimeToCharacteristicIsogeny.lean`; it is not counted as a new result.

## Checked changes

Four new modules contain 15 public theorems:

- `PadicLatticeCompactness.lean`: compactness of integral matrix/operator data, nonvanishing of the limit, and the limiting-image condition.
- `PadicLatticeOperators.lean`: passage from matrices to the rationalization of the actual integral lattice, integral error vectors, and clearing denominators.
- `ScalarFrobeniusTateRecurrence.lean`: finite-model recurrence, actual integral endomorphisms from recurring isogeny domains, and nonzero limiting operators from finite quotient models.
- `ScalarFrobeniusTateFiniteModels.lean`: existence of actual prescribed quotient families and the full finite-model-to-elliptic-map/product-isogeny implications.

The main final declarations, in `SupersingularCurves.Geometry.ScalarFrobeniusTate`, are:

- `exists_actualEndSpan_operator_of_finite_quotient_models`
- `exists_elliptic_map_of_finite_graph_quotient_models`
- `exists_supersingular_product_isogenies_of_finite_graph_quotient_models`

All 328 earlier project proof modules and all 4,666 vendored proof modules are byte-identical. There are no new vendor files or compatibility ports. The project now contains 332 proof modules and 1,840 public theorem declarations. These counts are an inventory, not a percentage of the mathematical goal completed.

## Verification

The new final module and its full import closure build successfully: 11,133 Lake jobs, with retained caches reused. The final aggregate and all historical integration examples were not rebuilt. All 15 advertised new theorems resolve as theorems. The audit checks all 46 stored declarations in the four new modules, including generated declarations, their types and bodies, and transitive axioms. Only `propext`, `Classical.choice`, and `Quot.sound` occur.

Source integrity, pinned upstream bytes, and the admission/native-evaluation scan are checked separately. Reproduce with `bash verification/verify_checkpoint30.sh` after installing the pinned toolchain and dependencies. The optional checkpoint-30 build cache saves the compiled chain; it is a partial cache and contains no external dependencies or compiler.

The precise mathematical construction and outstanding hypothesis are documented in `provenance/checkpoint-30-recurrence.md`. Older checkpoint reports retain their historical scope.
