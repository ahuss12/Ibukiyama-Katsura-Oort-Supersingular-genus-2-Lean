# Scalar-Frobenius isogeny route: checkpoint 27

## Implemented scope

The following three project modules prove intermediate geometric results. They do **not** prove the scalar-Frobenius product-isogeny theorem or the missing Block 1 product-isomorphism theorem.

1. `SupersingularCurves/Geometry/ScalarFrobeniusIsogenyFiniteness.lean`
   - A finite-type affine scheme over a finite field has finitely many scheme points with that field as source.
   - A quasi-compact, locally finite-type scheme over a finite field has finitely many such points, by a finite affine cover.
   - The theorem counts actual scheme morphisms, including the maps needed by the fine-moduli application.

2. `SupersingularCurves/Geometry/ScalarFrobeniusIsogenyModuli.lean`
   - Finite-field points of the actual finite-type fine-moduli scheme produce finitely many actual framed polarized abelian varieties, up to the defined scheme/group/line-bundle isomorphism relation.
   - Every polarized model over a field admits a complete global frame of the prescribed section rank. This uses finite global sections, generation from an existing projective presentation, and invariance of the dimension of sections on geometric fibers.
   - Forgetting frames gives finitely many polarized models of fixed dimension and fixed geometric section rank.
   - `polarizedOfVeryAmple` constructs the trivial level structure for any actual abelian variety with a very ample line bundle of prescribed geometric section rank.
   - `exists_finite_abelian_representatives` accepts the actual scheme, structure morphism, relative group law, abelian scheme property bundle, dimension, and very ample invertible sheaf. It produces an actual scheme isomorphism to a member of a finite list, preserving the group law on every test scheme.
   - This is a bound for a specified **geometric H⁰ rank**. It does not yet construct bounded-rank polarizations on Tate's lattice quotients.

3. `SupersingularCurves/Geometry/ScalarFrobeniusIsogenySubgroup.lean`
   - `fixed_fraction` verifies the generic fixed-points descent hypothesis for the algebraic closure of a finite field.
   - Given a finite Hopf algebra over that field, its geometric-point group with compatible Galois action, and a stable subgroup N, `exists_hopf_quotient_of_stable` constructs an actual quotient Hopf algebra B.
   - The map Spec(B) → Spec(H) is a closed immersion. The structure morphism of Spec(B) is finite, flat and locally finitely presented. Its scheme-theoretic rank at every point of the finite ground field is exactly |N|.
   - Its geometric points are exactly the points in N, via an explicit factorization criterion.
   - This establishes a finite subgroup of the given affine group scheme. Assembly of the ambient Hopf algebra with an actual abelian variety's torsion kernel, and the all-test-scheme subgroup conditions for the actual abelian-variety quotient theorem, remain to be connected.

## Validation

- Finiteness module: clean Lean build; normal axiom audit only `propext`, `Classical.choice`, `Quot.sound`.
- Subgroup module, including finite/flat/finitely-presented structure and exact scheme rank: clean Lean build. Final expanded audit pending the combined audit.
- Moduli module: dependency build and final source check in progress. Its finite-representative argument has compiled separately against the actual fine-moduli bundle, and its trivial-level construction has compiled separately. Do not count the combined module as verified until the final build succeeds.

## Exact remaining global realization work

Start with an actual abelian surface A over a finite field for which a power of Frobenius is scalar, and an actual supersingular elliptic curve E with the matching scalar after a common finite extension. Neither this finite-field descent nor the existence/compatibility of E is assumed solved by these modules.

1. Form D = A × E² and actual finite étale torsion. For a Galois-stable lattice X containing ℓⁿTℓ(D), construct the subgroup ℓ⁻ⁿX/Tℓ(D), use the Hopf descent result, and then the existing actual finite-flat subgroup quotient theorem. Descend [ℓⁿ] through that quotient to an actual isogeny f:B→D. Prove that its Tate-module image is exactly X. This is the missing bridge from lattices to actual abelian varieties.
2. For the Lagrangian lattices Xₙ = (Tℓ(D)∩W) + ℓⁿTℓ(D), divide the pulled-back polarization by ℓⁿ. Prove that the resulting actual line bundles are ample, descend over the fixed finite field, and have a uniform geometric H⁰ rank after a fixed power. Only then does the implemented finite-representatives theorem apply to all Bₙ. An algebraically closed-field Riemann-form division modulo Pic⁰ does not by itself supply these assertions.
3. Use the finite list and compactness to obtain a nonzero endomorphism of Vℓ(D) with prescribed image W lying in the Qℓ-span of **actual** scheme endomorphisms of D (Tate's Proposition 1). This requires finite generation/closedness of the actual Hom lattice and the comparison between the isogenies and their Tate modules.
4. Either finish Tate's general scalar-Frobenius commutant argument, or use the smaller surface-specific graph argument below. Finally convert a suitable actual homomorphism into a finite-surjective E²→A isogeny, with the necessary kernel/dimension argument.

No theorem here assumes the desired product isogeny, replaces the actual variety with its Tate module, or promotes isogeny to isomorphism. The additional integral/local p-torsion step needed to turn a product isogeny into the superspecial product isomorphism is separate work owned by the main proof route.

## A possible surface-specific simplification

Full surjectivity of the Tate Hom comparison may not be necessary. Choose a Lagrangian graph W of an anti-symplectic Qℓ-isomorphism Vℓ(A)→Vℓ(E²). Proposition 1 supplies a nonzero u in the Qℓ-span of actual End(D) whose image is W. If every actual endomorphism of D were block diagonal, u would be block diagonal too; a block-diagonal map with image in such a graph must be zero. Consequently there is a nonzero actual off-diagonal homomorphism. Using polarizations if its direction is A→E² yields a nonzero actual E→A. An actual elliptic subvariety, a polarized complementary abelian subvariety, and the already available elliptic Tate comparison can then give E²→A.

This reduces the general semisimple-algebra/bicommutant step, but it does not remove steps 1–3 or the need to construct an actual complementary abelian subvariety. It is a mathematical proof plan, not an implemented theorem.

## Primary reference

John Tate, “Endomorphisms of Abelian Varieties over Finite Fields,” Inventiones mathematicae 2 (1966), 134–144. The bounded-polarization finiteness and invariant-Lagrangian construction are the relevant proof ingredients.

https://pazuki.perso.math.cnrs.fr/index_fichiers/Tate66.pdf

## Exact pinned roots used by the new modules

The new files import Mathlib and these exported roots from the existing Anthropic pin aa2d8b34692b16c70f699536de0d8e75b9a3e9ef:

- `Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isFineModuli_quasiProjective`
- `Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_sections_finite_projective_and_isSectionBasisOn_pullback_type0`
- `Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_isSectionBasis_of_finite_sections_of_forall_exists_isFrameOn`
- `Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_mem_isFrameOn`
- `Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_isSectionBasis_of_closedImmersionBySections`
- `Thm_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints`

The exact imports are frozen; no additional foundational roots are planned for this checkpoint.
