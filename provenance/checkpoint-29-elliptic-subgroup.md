# Checkpoint 29: elliptic subgroup construction

The new project proofs construct an actual closed elliptic subgroup from an
actual group-scheme morphism with nonzero induced rational Tate map, in either
direction between an elliptic curve and an abelian surface. They also connect
the existing actual-endomorphism graph extraction to the existing product-isogeny
construction. No original geometric definition or checkpoint-28 proof file was
modified.

## Proof route

1. `ProperCurveFiniteMap.lean` proves finiteness of a nonconstant morphism from a
   proper smooth integral curve to a separated scheme, and surjectivity of a
   nonconstant proper morphism from an irreducible scheme to a proper smooth
   integral curve.
2. `AbelianHomImage.lean` proves that the scheme-theoretic image of a morphism
   from a reduced scheme is reduced. For a finite actual abelian homomorphism,
   it constructs the image group law, connectedness, smoothness, a closed
   immersion, and equality with the source dimension.
3. `EllipticSubgroupFromMap.lean` proves that a nonzero rational Tate map rules
   out a topologically constant underlying scheme morphism. For a map from an
   actual elliptic curve, the image construction therefore produces a genuine
   smooth connected closed subgroup of dimension one.
4. `AbelianSurfaceEllipticKernel.lean` treats a map from a surface to an elliptic
   curve. It constructs the actual kernel and its reduced identity component.
   If that component had dimension zero, the kernel would be finite, making
   the surface finite and surjective over a curve, contrary to dimension
   preservation. Its image is a proper closed subset of the surface, so its
   dimension is less than two. Thus its dimension is exactly one.
5. `ScalarFrobeniusTateEllipticSubgroup.lean` applies these constructions in
   both directions of the existing actual cross-morphism extraction. For a
   p-rank-zero surface, it produces supersingular elliptic factors and genuine
   finite-surjective group morphisms in both directions with their product.
   It concludes the unchanged `A.IsSupersingularOver p` predicate.

Paths above are under `SupersingularCurves/Geometry/`.

The curve and image foundations allow arbitrary scheme universes where stated.
The Tate-map interfaces use `K : Type`, matching the existing Tate-module API.
The geometric field assumptions are explicit: the base is algebraically closed.

## Exact remaining hypothesis

The final graph theorem assumes a rational Tate-space isomorphism `e` and a
nonzero operator `u` in `actualEndSpan` whose image lies in its graph. The new
proofs do not assume an elliptic subgroup, a kernel dimension, or a splitting.
They do **not** prove that such an operator exists for every zero-dV surface.
This is still the missing global input.

The current Tate route needs uniformly bounded very ample polarizations on the
actual lattice quotients, finite-model recurrence, and normalized operators in
the span of actual endomorphisms. The available general polarization result
gives a fixed power finite by sections. The available fixed-power very-ampleness
result has a principal-polarization hypothesis; it cannot simply be applied to
the nonprincipal roots used here. Finite by sections alone does not satisfy the
finite-moduli theorem's very-ampleness hypothesis.

Oort's integral splitting, required for the superspecial product isomorphism,
also remains open. Consequently neither positive geometric Cartier converse
is claimed here.

## Reuse and attribution

Four additional vendor modules, comprising two theorem interfaces and their
proofs, are copied byte-for-byte from FLT commit
`aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`:

- `AlgebraicGeometry.Scheme.finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton`
- `AlgebraicGeometry.isClosed_singleton_or_isGenericPoint_and_exists_not_isGenericPoint_of_smoothOfRelativeDimension_one`

Exact module names, Git blob IDs, SHA-256 hashes, and imports are recorded in
`checkpoint-29-foundation-imports.json`. No new compatibility ports were needed.
The proper-image group law, smooth reduced group theorem, identity-component
construction, finite-kernel theorem, and strict dimension inequality already
belong to the retained pinned vendor closure. Existing copyright and license
notices are retained.

`mini-checkpoint-28.json` records the 323 prior project proof files and 4,662
prior vendor Lean files. Every one remains byte-identical. New proof hashes are
in `checkpoint-29-sources.json`.
