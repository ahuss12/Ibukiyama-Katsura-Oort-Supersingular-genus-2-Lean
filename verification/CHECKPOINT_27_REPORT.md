# Checkpoint 27 — actual section-ring reconstruction and torsion descent

**Block 1 is not finished. Neither C = 0 ⇒ superspecial nor C² = 0 ⇒ supersingular is yet proved with the independent elliptic-product definitions.**

The central new result constructs an actual scheme isomorphism A ≅ Proj(R), with R the full section ring of an invariant invertible sheaf constructed from dV_A = 0. This closes the geometric reconstruction gap: the finite equivariant projective map alone did not identify A with its image. The construction works from finite projective presentation by proving affine preimage covers and the local section-fraction isomorphisms. The coherent Frobenius action supplies an actual fixed graded algebra; its degreewise scalar-extension equivalences construct a scheme over the subfield with p² elements and a proved pullback square recovering A. This is genuine descent of the underlying scheme. The group law, identity and inverse have not yet been descended, so it is not yet a finite-field abelian-variety model.

## Verified additions

- Zero actual dV constructs an actual Frobenius-square semilinear scheme automorphism, invariant invertible sheaf with finite projective presentation, and [p] followed by the automorphism equals absolute Frobenius squared.
- Actual global sections are finite-dimensional; the actual semilinear pullback action supplies fixed section bases and an equivariant finite projective presentation.
- The fixed vectors form a vector space over the actual Frobenius-fixed field; canonical scalar extension is a linear equivalence with pure-tensor formula c tensor v maps to c times v. In finite dimension Lang constructs the fixed basis.
- An invertible sheaf with a finite projective presentation reconstructs the actual scheme as Proj of its full section ring; this applies to every actual zero-dV abelian variety. The reconstruction is over the original field.
- The coherent action on the full section ring is an actual bijective ring homomorphism, preserves degree and has Frobenius-square semilinearity; tensor coherence follows from the single invariant-bundle isomorphism.
- The actual Frobenius-fixed subfield is finite of order p^s; every coefficient-Frobenius-stable polynomial ideal is extended from its contraction to this subfield.
- From actual dV=0 alone, a scheme over the actual subfield with p-squared elements is constructed with a genuine pullback square recovering the original abelian variety underlying scheme. The equalizer grading and degreewise scalar-extension comparisons are constructed; its group law is not yet descended.
- Actual finite-field finite-type quasicompact scheme points are finite; specified polarized models have finitely many actual isomorphism representatives, using a constructed section frame.
- A Galois-stable geometric subgroup has an actual descended quotient Hopf algebra and finite flat closed subgroup scheme, with exact rank and geometric-point factorization criterion.
- Actual elliptic p-torsion maps finite flatly with degree p onto the V-kernel, with F-kernel as identity fibre; actual torsion and F-kernel Hopf realizations and Dieudonne map compatibilities are constructed.
- An actual elliptic group homomorphism vanishes on the entire p-torsion scheme iff it factors through [p] as an actual group homomorphism.

## Exact remaining boundary

The missing classification still needs an actual unpolarized group-scheme isomorphism

A ≅ E₁ × E₂

from dV_A = 0 for an abelian surface, with each elliptic factor independently supersingular. Checkpoint 26 already constructs an actual isogeny from every represented genus-two Jacobian with C² = 0 to a zero-dV surface. It does not construct its elliptic factors.

1. Finish the actual finite-field abelian-variety model, including descent of multiplication, identity, inverse, geometric properties and the scalar Frobenius relation. Original-field Proj reconstruction alone is not this result.
2. Produce an initial actual isogeny with a product of independently supersingular elliptic curves. Stable subgroup descent and bounded moduli finiteness do not yet supply the polarized lattice quotients, limit/Hom realization or complementary elliptic factor.
3. Prove the torsion-map extension/surjectivity and integral splitting that give an actual elliptic-product isomorphism from zero dV. The new divisibility theorem proves the restriction kernel only.
4. Connect that actual product classification to C=0 implies superspecial and C-squared=0 implies supersingular. Both remain open.
5. The wider sheet/IKO scope still needs abstract genus-two presentation, perfect-field scope, actual crystalline Newton attachment/comparison, and remaining section-one automorphism/quotient/isomorphism and cyclic-cover identifications.

The finite-field subgroup result treats specified Galois-stable geometric-point subgroups; it does not classify infinitesimal p-primary groups. The moduli finiteness theorem requires its specified very ample sheaf and bounded section-rank data; it does not construct the uniformly bounded polarized quotients needed in Tate's argument. Vanishing on E[p] iff divisibility by p determines the restriction kernel, not the image or lifting surjectivity in Oort's lemma. The precise obligations are retained under provenance.

## Verification and preservation

- Full aggregate plus all 1,610 new vendor modules built successfully: 12,570 Lake jobs.
- 28 new project proof modules; 160 new public theorem declarations and 14 private supporting theorem declarations.
- All 22,532 new stored declaration entries audited: 505 project and 22,027 vendor. This includes private/generated entries, stored types/bodies, and transitive axiom dependencies. Only propext, Classical.choice and Quot.sound are allowed; all advertised theorem names resolve as theorems.
- Two concrete integration checks passed on the actual y² = x⁵ − 1 models: the characteristic-19 Jacobian underlying scheme has a model over the 361-element subfield; in characteristic 3 the constructed isogenous zero-dV surface underlying scheme has a model over the 9-element subfield. Both use actual pullback squares.
- All 195 checkpoint-26 project proof modules and 1,973 vendor Lean files are byte-identical. The actual geometric definitions remain unchanged. 7 new documented compatibility ports repair upstream API names/indices without changing theorem statements; the original ten ports remain unchanged.
- 3,806 project/aggregate/vendor Lean source files passed the admission/native-evaluation marker scan and exact source/provenance checks.
- The project now has 223 proof modules, 1,340 public theorem declarations, 55 private supporting theorem declarations, and 3,582 pinned vendor modules. These are source-inventory counts, not a completion percentage.

Reproduce with `bash verification/verify_checkpoint27.sh` using the pinned Lean 4.34.0-rc2 and Mathlib revision in the package. Historical checks are retained for byte-identical sources; this was not a clean rebuild of every dependency. The previous external-formalization search found no ready-made product-classification theorem in the inspected repositories; imported foundations remain individually source-pinned.
