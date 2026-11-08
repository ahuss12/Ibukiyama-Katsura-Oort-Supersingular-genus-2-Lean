# Checkpoint 28: actual complementary-product isogenies

## Checked theorem and its exact input

`ScalarFrobeniusTate.exists_product_isogeny_of_closed_subgroup` starts with an
actual smooth connected closed subgroup of an abelian variety, including its
actual compatible group law. It constructs a complementary abelian variety,
the actual addition map from their product, and a reverse group morphism.
Both maps are proved finite and surjective as scheme morphisms.

For a p-rank-zero surface,
`ScalarFrobeniusTate.exists_supersingular_elliptic_product_isogeny_of_closed_subgroup`
proves that the resulting dimension-one factors are supersingular under the
unchanged geometric p-torsion definition. It retains the assumption that an
actual smooth connected closed elliptic subgroup has been constructed.

`ScalarFrobeniusTate.isSupersingularOver_of_closed_elliptic_subgroup` then
concludes the original `IsSupersingularOver` predicate, using an actual
group-scheme isomorphism from the binary fibre product to the independent
categorical Fin-2 elliptic product.

**These are not the missing unconditional product-classification theorem.**
No theorem in this checkpoint constructs the initial elliptic subgroup in an
arbitrary zero-dV surface. Consequently neither geometric Cartier converse
is marked complete.

## Construction

1. `AbelianClosedSubgroup.lean` packages the actual closed subgroup and its
   group law as an abelian variety and constructs the inclusion and the
   quasi-retraction as genuine group-scheme morphisms.
2. `ScalarFrobeniusProductComplementKernel.lean` adapts the pinned FLT proof
   of Poincare complement existence. It retains the proof's kernel condition:
   the complement is annihilated by the constructed quasi-retraction on
   every test scheme.
3. `AbelianVarietyProductAddition.lean` constructs addition from the actual
   fibre product, with its group-homomorphism proof.
4. `AbelianProductIsogeny.lean` uses the quasi-retraction to prove that a
   nonzero integer kills the whole scheme-theoretic addition kernel.
5. `AbelianIsogenyKilledKernel.lean` embeds that kernel as a closed subscheme
   of the finite multiplication kernel, then proves the addition map finite
   and flat. This controls infinitesimal structure as well as geometric points.
6. `AbelianIsogenyQuasiInverse.lean` descends multiplication through the
   faithfully flat quotient. The descended group morphism is a reverse
   isogeny, with both composites equal to multiplication by the same integer.
7. `ScalarFrobeniusProductIsogeny.lean` assembles these constructions.
   `ScalarFrobeniusSurfaceProductIsogeny.lean` shows the elliptic factors
   inherit trivial geometric p-torsion from the surface.
8. `AbelianVarietyProductCategorical.lean` constructs the actual group-scheme
   isomorphism with the categorical product used in the original definition.

## Attribution and verification

The complement proof is adapted from
`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative`,
at FLT commit `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`.
Its original local kernel proof is retained in the strengthened conclusion;
no vendor proof is edited for this adaptation. The exact upstream finite-flat
kernel criterion and multiplication-point comparison are recorded in the
foundation manifest. All checkpoint-27 project and vendor proof sources are
preserved byte for byte.

All nine project targets passed their targeted Lean builds. The complete
checkpoint build, advertised-theorem existence checks, and transitive axiom
audit are recorded in `verification/CHECKPOINT_28_REPORT.md` and its logs.

## Global obligation that remains

The Tate route still needs uniformly bounded very ample polarizations on the
actual lattice quotients, including the nonprincipal case. Finite-by-sections
alone does not meet the available finite-moduli theorem's hypothesis. The
recurrence and normalized actual-operator argument then has to produce a
nonzero elliptic-to-surface map, and its image must be constructed as the
required smooth connected closed elliptic subgroup. The complementary-product
finiteness and reverse-isogeny constructions above now supply the next stage.

Oort's integral splitting remains a further obligation for the product
isomorphism and the Cartier-zero superspecial converse.
