# Checkpoint 28 — checked product-isogeny constructions

**The draft modules are now compiled and audited. The unconditional product-isogeny theorem for an arbitrary zero-dV surface is still not proved, and Block 1 remains incomplete.**

## Product-isogeny result now checked

For an actual abelian variety A and an actual smooth connected closed subgroup E,
the formalization constructs a complementary abelian variety C and genuine group
morphisms E × C → A and A → E × C. Both are finite and surjective as scheme
morphisms. The entire scheme-theoretic kernel is controlled, including its
infinitesimal part; a statement only about geometric points is not substituted.

For a p-rank-zero abelian surface with an actual elliptic subgroup, both factors
are proved supersingular and the final theorem concludes the existing independent
`A.IsSupersingularOver p` predicate. The actual fibre product is identified with
the categorical product used in that definition. No geometric definitions were
weakened or replaced.

The exact assumption that remains is **existence of that first smooth connected
closed elliptic subgroup in an arbitrary zero-dV surface**. The new theorem is
conditional on it and must not be cited as the missing unconditional classifier.

Principal declarations:

- `ScalarFrobeniusTate.exists_product_isogeny_of_closed_subgroup`
- `ScalarFrobeniusTate.exists_supersingular_elliptic_product_isogeny_of_closed_subgroup`
- `ScalarFrobeniusTate.isSupersingularOver_of_closed_elliptic_subgroup`
- `AbelianVariety.exists_quasiInverse_of_kernel_killed`

All names are under `SupersingularCurves.Geometry`. Proof files and attribution
are mapped in `provenance/checkpoint-28-product-isogeny.md`.

## Other checked checkpoint additions

- Actual finite-field abelian-variety descent, including the group law, group recovery isomorphism, scalar Frobenius and actual morphism descent.
- Actual Tate modules and finite subgroup quotients with prescribed integral Tate image; symplectic graph, saturation, direct-summand, isotropy and reduction-cardinality lemmas.
- Actual Riemann pairing construction, cross-variety pullback, finite-kernel perfectness, rational extension, and iterated line-bundle roots modulo actual Picard-zero bundles.
- Actual product group schemes, Tate-product decompositions, and comparison of the binary fibre product with the independent categorical Fin-2 elliptic product.
- Given an actual smooth connected closed subgroup, construct a complement and prove actual product addition is a finite flat isogeny. The proof controls the entire scheme kernel, including infinitesimal structure.
- Faithfully flat descent of multiplication constructs an actual reverse isogeny; both composites equal multiplication by a nonzero integer.
- For a p-rank-zero surface with an actual smooth connected closed elliptic subgroup, construct supersingular elliptic factors and prove the existing IsSupersingularOver predicate. The subgroup existence assumption remains explicit.
- For the chosen supersingular elliptic model after field extension, a Frobenius-kernel endomorphism extending to actual p-torsion lifts to an actual global endomorphism.

## Remaining work

1. Construct the first actual elliptic subgroup of an arbitrary zero-dV surface. The Tate route still needs uniformly bounded very ample polarizations on actual lattice quotients, finite-model recurrence, normalized actual operators, and an actual nonzero elliptic-map/image construction.
2. Complete transfer between arbitrary elliptic factors and Oort integral subgroup-straightening/quotient induction to obtain the unpolarized product isomorphism from zero dV.
3. Apply that global classification to C=0 implies geometric superspeciality and C-squared=0 implies geometric supersingularity. Both converses remain open; checkpoint 26 already supplies an isogeny to a zero-dV surface in the square-zero case.
4. The wider sheet/IKO scope still needs the remaining abstract-curve/perfect-field scope, actual crystalline Newton comparison, and section-one automorphism, quotient, cyclic-cover and isomorphism-class results.

The concrete polarization obstruction is that the available finite-moduli theorem
needs a uniformly bounded very ample line bundle. A fixed power finite by sections
does not by itself meet that hypothesis. The available principal-polarization
very-ampleness result cannot be applied to a general nonprincipal root.

## Verification

- Full aggregate and all 1,080 new vendor targets built: 13,750 Lake jobs.
- 100 new project modules; 469 new public theorem declarations
  and 27 private supporting theorem declarations.
- 20,976 new stored declaration entries audited (1,272 project, 19,704 vendor),
  including stored types/bodies, generated/private entries, and transitive axioms.
  Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
- Both actual-curve integration examples pass: the characteristic-19 zero-dV
  Jacobian has an actual finite-field abelian model over 361 elements; the
  characteristic-3 isogenous zero-dV surface has one over 9 elements. Both include
  group recovery and scalar Frobenius. These examples do not prove classification.
- All 223 checkpoint-27 project proof files and 3,583 vendor Lean files are
  byte-identical. The independent isogeny, supersingular, superspecial and
  Jacobian definitions are unchanged.
- 4,986 project/aggregate/vendor Lean sources passed the
  admission/native-evaluation scan. Added sources are pinned to FLT commit
  `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`; six documented compatibility ports
  retain reversible source provenance.
- Total inventory: 323 project proof modules, 1,809 public theorem
  declarations, 82 private supporting declarations, and
  4,662 pinned vendor modules. These counts are not a
  percentage of the mathematical task completed.

Run `bash verification/verify_checkpoint28.sh` with the pinned Lean 4.34.0-rc2
and package lock. This verification reused compiled unchanged dependencies and
historical audits; it was not a clean rebuild of every dependency. Exact executed
results and log hashes are in `verification/checkpoint-28-run.json`.
