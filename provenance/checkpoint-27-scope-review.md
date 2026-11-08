# Checkpoint 27 source scope review

Read-only review on 2026-09-23 of `project/supersingular-curves-mini`, compared with `checkpoint-26-baseline.zip`. Sources were still being added during review. No compilation was run by this reviewer.

## Result

The new sources make substantive progress on descent, section-ring reconstruction, finite-field finiteness, and actual elliptic torsion. They do **not** yet prove the missing geometric classification theorem or either positive elliptic-product converse. None of the inspected new project theorem statements silently assumes the missing classifier, a product isogeny, or the desired product isomorphism.

All **2,205 baseline Lean files** were present and byte-identical at comparison time. This includes all **195 baseline project proof modules**, all 1,973 vendor Lean files including the vendor Lake configuration, and existing audit/verification/configuration Lean files. In particular, the independent geometric predicates in `Geometry/Superspecial.lean` are unchanged:

- Superspeciality requires an actual group-scheme isomorphism with an elliptic product, with each elliptic factor satisfying the independent geometric p-torsion definition.
- Supersingularity requires an actual finite surjective group-scheme morphism to such a product.

The aggregate `SupersingularCurves.lean` was also unchanged at this snapshot, so final import integration remains necessary.

## New project module inventory and exact scope

All filenames below are under `SupersingularCurves/Geometry/` and end in `.lean`. Twenty-two modules existed at the first comparison; `FrobeniusFiniteFieldDescentSectionAction` appeared during review, bringing the current inventory to **23**.

| New modules | Conclusions supplied by their sources |
| --- | --- |
| `FrobeniusFiniteFieldDescent` | From zero actual Verschiebung cotangent, constructs a Frobenius-square semilinear scheme automorphism, an invariant invertible sheaf with a finite projective presentation, and the actual relation `[p] ≫ τ = F_abs²`. |
| `FrobeniusFiniteFieldDescentLinear` | An injective Frobenius-semilinear map on a finite-dimensional vector space over an algebraically closed field has a fixed basis; its coordinate action is coefficient Frobenius. |
| `FrobeniusFiniteFieldDescentSections`, `FrobeniusFiniteFieldDescentFiniteSections`, `FrobeniusFiniteFieldDescentBasis` | Constructs the actual pullback action on sheaf sections, proves its bijectivity and semilinearity, proves finite-dimensionality from properness, and constructs a fixed section basis from the actual zero-dV variety. |
| `FrobeniusFiniteFieldDescentTensor` | Constructs invariant positive tensor powers, retaining invertibility and finite projective presentation. |
| `FrobeniusFiniteFieldDescentPresentation`, `FrobeniusFiniteFieldDescentEquivariance`, `FrobeniusFiniteFieldDescentProjective` | Constructs a full-basis finite projective map and proves actual scheme-map equivariance for coefficient Frobenius squared. The conclusion is **finite**, not a closed immersion. |
| `FrobeniusFiniteFieldDescentSectionMap`, `FrobeniusFiniteFieldDescentSectionFractions`, `FrobeniusFiniteFieldDescentSectionIso`, `FrobeniusFiniteFieldDescentSectionModel` | Constructs the canonical map to the full section ring's Proj, proves local fraction and isomorphism statements using finite-map affine preimages, and obtains an actual scheme isomorphism `A ≅ Proj R`. This recovers the original variety, but remains **over the original field**. |
| `FrobeniusFiniteFieldDescentSectionAction` | Constructs a coherent ring action on that actual full section ring from the single pullback isomorphism, with multiplication, unit, homogeneous-component formulas, and bijectivity. This file was active work during review. |
| `FrobeniusInvariantIdeal` | Constructs the finite Frobenius-fixed subfield, proves its cardinality, and proves that a coefficient-Frobenius-stable polynomial ideal is extended from its contraction to that subfield. It requires an actual stable polynomial presentation for application. |
| `FrobeniusFixedScalarExtension` | Constructs the fixed-vector space over the fixed field and its actual scalar-extension linear equivalence with the original finite-dimensional space; the pure-tensor formula is scalar multiplication. This is vector-space descent, not yet graded-algebra or scheme descent. |
| `ScalarFrobeniusIsogenyFiniteness` | Proves finiteness of actual finite-field points of quasicompact finite-type schemes. |
| `ScalarFrobeniusIsogenyModuli` | Finite actual isomorphism representatives for the specified polarized abelian-scheme data over a finite field, with fixed dimension, section rank, and invertible level. It constructs the complete frame instead of assuming one. The upstream data include a very ample invertible sheaf and a full rational level structure; arbitrary bounded-degree quotient polarizations have not been supplied by this result. |
| `ScalarFrobeniusIsogenySubgroup` | Constructs an actual quotient Hopf algebra, closed subgroup immersion, exact rank, and geometric-point factorization criterion for a Galois-stable subgroup over a finite field. This describes the subgroup specified by geometric points; it does not classify nonreduced p-primary subgroup schemes. |
| `EllipticTorsionRealization` | Constructs the actual finite flat degree-p map `E[p] → ker(V)`, identifies its identity fibre with `ker(F)`, proves the kernel subgroup laws, and constructs restrictions of genuine torsion/group-scheme maps. |
| `EllipticTorsionRealizationDieudonne`, `EllipticFrobeniusKernelHopf` | Constructs the actual torsion Hopf realization, rank p² in the elliptic case, the actual Frobenius-kernel Hopf presentation of rank p, natural maps on every test algebra, and induced Dieudonné maps commuting with F and V. |
| `EllipticTorsionRealizationDivisibility` | Proves that an actual elliptic group homomorphism vanishes on the **entire p-torsion scheme** exactly when it factors through multiplication by p as an actual group homomorphism. This proves the restriction kernel; it does not prove the missing lifting surjectivity. |

## Remaining mathematical gaps

1. **Actual finite-field model.** The section-ring isomorphism is over K. A coherent fixed graded algebra, its scalar-extension comparison, Proj base change, and descent of the actual group law/properties are still needed. A finite equivariant map or an invariant projective image alone does not supply the model. The section-ring reconstruction correctly avoids that earlier possible confusion.
2. **Initial actual elliptic-product isogeny.** Finiteness of moduli points and descent of stable geometric subgroups are ingredients for Tate's argument, not a Tate realization theorem. The polarized lattice quotient construction, bounded polarization control, and actual Hom/endomorphism realization needed to produce the product isogeny remain absent.
3. **Integral splitting.** Actual torsion realizations and divisibility by p do not prove Oort's lifting/extension surjectivity or the kernel-straightening/degree induction that upgrades the initial isogeny to a product isomorphism.
4. **Final geometric conclusions.** No inspected new module concludes `IsSuperspecialOver`, `IsSupersingularOver`, or constructs an `ellipticProduct` isomorphism/isogeny. Thus checkpoint 26's `C² = 0 →` isogeny to a zero-dV surface is still not the final supersingularity theorem, and `C = 0 →` superspeciality is still open. The broader abstract-curve/perfect-ground-field scope is not supplied by these additions either.

## Checks and handoff issues

- No `sorry`, `admit`, `axiom`, or `native_decide` token was found in the new project proof sources inspected. This lexical check is not a substitute for the final transitive axiom audit.
- At the initial object-file check, 20 of the first 22 modules had `.olean` timestamps newer than their source. `FrobeniusFixedScalarExtension` and `ScalarFrobeniusIsogenyModuli` did not yet have `.olean` files. `SectionAction` was added subsequently. These observations are not a compilation certificate; use the final build/audit evidence.
- The temporary root `TempFixedCheck.lean` contains a trace-enabled `#synth` experiment and should be excluded or removed before packaging.
- Some new verification files still use `checkpoint-28` filenames. Normalize their checkpoint labels or explicitly explain them before delivery.
- At the final inventory snapshot, `checkpoint-27-foundation-imports.json` listed **1,610** new vendor files and 25 roots. The source inventory is changing; final counts must be taken after all writers freeze.
- Source comments inspected correctly distinguish finite presentation, original-field section-ring reconstruction, finite-field descent, Tate realization, and integral splitting. The final report should preserve these distinctions and must keep Block 1 marked incomplete unless the genuinely missing conclusions are subsequently proved.

## Final integration update

After the snapshot review, genuine underlying finite-field scheme descent was completed. `FrobeniusFiniteFieldDescentScheme.lean` constructs the actual p²-element fixed subfield and an actual scheme pullback square recovering the original A from dV=0 alone. The grading, degreewise scalar-extension equivalences, irrelevant-ideal coverage and Proj base change are proved in the new fixed-grading/Proj modules. The group law, identity, inverse and scalar-Frobenius relation over that finite field remain open. Thus item 1 above is narrowed to abelian-group structure and related property descent; the underlying scheme model is no longer missing.

Temporary probes were removed from the project root, checkpoint-28 log names were normalized, and final imports/inventory/build/audit are recorded in the checkpoint-27 report. Seven new source compatibility ports are recorded separately, preserving all old proof/vendor bytes.
