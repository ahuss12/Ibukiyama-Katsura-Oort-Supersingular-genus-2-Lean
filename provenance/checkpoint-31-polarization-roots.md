# Checkpoint 31: quotient roots, numerical bounds, and finite-model assembly

## Construction, not a boundedness assumption

`ScalarFrobeniusTate.exists_quotient_root_with_uniform_numerics` starts with
an actual abelian variety A/k of dimension g, an actual invertible sheaf M
finite by sections, its actual Tate Riemann pairing e, and an isotropic
direct summand U of rank g. The existing root theorem's hypotheses k
algebraically closed, characteristic not two, and ell invertible in k are
retained explicitly.

For every n, the theorem constructs an actual finite subgroup, its quotient,
the actual residual multiplication morphism, and actual invertible root R
and Pic0 error P. It proves the prescribed integral Tate image, the root
isomorphism, finite translation kernel, positive geometric H0, and a finite
projective presentation of R^3. For every positive r and every algebraically
closed field extension, h0(R^r) = r^g h0(M). In particular there is no n in
the final section count.

The proof has four numerical/geometric steps:

1. The existing reduced-subgroup cardinality and actual multiplication degree
   give degree(quotient factor) = (ell^n)^g for the half-rank summand.
2. Bilinearity and isotropy show divisibility by ell^n on U + ell^n T. The
   existing geometric pullback theorem and iterated Pic0 root construction
   give the actual sheaves R and P; root existence is not an assumption.
3. A root's translation stabilizer is contained in that of its power. Pic0
   twists preserve stabilizers. Finiteness and positive H0 therefore descend
   from the actual pulled-back finite-by-sections polarization.
4. The actual finite-flat Euler degree formula and cohomology vanishing give
   h0(f*M) = (ell^n)^g h0(M). The tensor-power/Pic0 calculation gives
   h0(f*M) = (ell^n)^g h0(R). Cancellation proves h0(R) = h0(M).

`AbelianIsogenyRootNumerics.exists_symmetric_bundle_with_uniform_rank` twists
R by an actual Pic0 bundle to make it symmetric and takes its cube. The
result is an actual symmetric invertible bundle, finite by sections, with
h0 exactly 3^g h0(M). Symmetrization introduces no n-dependent factor.

## Finite-field and moduli assembly

`AbelianVariety.exists_finiteField_polarized_model_with_rank` proves that the
previous prescribed polarized finite-field descent has exact section rank
(p^2)^g h0(L), at every geometric point of the finite base field. It retains
the actual group-scheme recovery isomorphism. Very ampleness of L remains an
explicit input.

`PolarizedFiniteModels` converts the actual polarized moduli representatives
to actual abelian varieties. A scheme isomorphism preserving multiplication
on all test schemes is upgraded to an isomorphism of internal group objects.
This supplies a finite list of actual geometric models after base change.
Consequently a zero-dV sequence with symmetric very ample bundles of one
fixed positive H0 rank has finitely many actual group-scheme models.

## Reused foundations and attribution

All earlier project proof sources and all pinned vendor sources are unchanged.
No vendor module, axiom, compatibility port, or definition is added or changed.

The translation/power stabilizer argument also occurs in the helper
`FBSNondeg.kernelPts_subset_kernelPts_tensorPow` in the pinned FLT solution
for `kernelPts_finite_and_geomFibreH0Finrank_pos_of_finiteBySections`.
The new implementation uses the already imported public pullback/tensor-power
isomorphisms. Remaining geometry uses the pinned public finite-kernel
cohomology, Pic0 invariance, root-positivity, symmetric-twist, and finite-cube
theorems, together with the earlier cross-variety Euler characteristic theorem.
The finite-model argument uses the earlier actual fine-moduli and polarized
Frobenius descent constructions.

The upstream commit remains
`anthropics/fermats-last-theorem@aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`.
The exact source closure, Git blob hashes and prior compatibility ports remain
in the vendor manifests. These are proof-composition and construction results,
not claims of mathematical novelty of the underlying classical facts.

## Remaining boundary

A finite projective map is not a closed immersion. The general nonprincipal
polarization theorem that a suitable uniform tensor power is very ample is
still missing. The available theorem requiring a trivial polarization kernel
does not apply merely because the kernel is finite.

The actual product graph, its product polarization and the chosen prime must
also be assembled into this quotient-root construction and then the finite-model
recurrence theorem. The unconditional zero-dV elliptic-map/product-isogeny
theorem remains open. The further Oort integral splitting needed for a product
isomorphism, the positive Cartier criteria, and Block 1 remain open.
