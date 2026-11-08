
## Build

With elan/Lean available, run from this directory:

```sh
lake exe cache get
bash verification/verify.sh
```

Lean is pinned to 4.34.0-rc2 and Mathlib to `85e3a25e006c35636f0e53b0e9296caca2685bc0`. The complete package lock is in `lake-manifest.json`. A separate optional compiled build cache is documented in `verification/BUILD_CACHE.md`.

For the latest focused verification, run `bash verification/verify_checkpoint29.sh`. It builds the new geometric chain and its import closure, checks provenance, and audits all new declarations and their transitive axioms. The full aggregate and historical suites were not rerun for this checkpoint. Exact executed checks are recorded in the checkpoint-29 report.

## Source structure

Checkpoint 29 adds `ProperCurveFiniteMap`, `AbelianHomImage`, `EllipticSubgroupFromMap`, `AbelianSurfaceEllipticKernel`, and `ScalarFrobeniusTateEllipticSubgroup` under `SupersingularCurves/Geometry/`. These five modules contain 16 new public theorems. Their scope and the remaining global hypothesis are recorded in `verification/CHECKPOINT_29_REPORT.md`.

Checkpoint 28 adds the actual descent, Tate/Riemann, local lifting, and complementary-product constructions listed above. The complete inventory and precise open boundary are in `verification/CHECKPOINT_28_REPORT.md`. Older checkpoint descriptions below are historical.

Checkpoint 27 adds Frobenius descent and full-section-ring reconstruction modules, finite-field finiteness/subgroup constructions, and actual elliptic torsion and divisibility modules. The checked inventory and precise open boundary are recorded in `verification/CHECKPOINT_27_REPORT.md`.

Checkpoint 26 adds actual finite-group local algebra and invariant derivations, the subgroup order theorem, genuine quotient and residual isogeny constructions, rational-point/p-rank invariance, and actual twofold Frobenius/Picard/Verschiebung comparisons. Exact source and verification inventories are in `verification/CHECKPOINT_26_REPORT.md`.

Checkpoint 25 adds the identity-to-global differential argument, the actual Frobenius factor and residual group isomorphism, the reverse factor-to-cotangent-zero implication, and their full-space genus-two Cartier applications. It also adds the actual simultaneous Frobenius/Verschiebung kernel, the fibre cotangent exact sequence and dimension formula, and their genus-two Cartier applications, together with the uniform characteristic-three obstruction. Exact source inventory and executed checks are recorded in `verification/CHECKPOINT_25_REPORT.md`; proof-route limitations are recorded in `provenance/checkpoint-25-classification-route-review.md`.

Checkpoint 24 adds geometric proof modules for elliptic Verschiebung vanishing, finite kernel cotangents, actual Frobenius and multiplication degrees, algebraically closed base change, product transport, and the general superspecial-to-Cartier implication. It also proves differential-kernel and Frobenius-factorization lemmas for the converse route. Their exact scope, source inventory, and checks are recorded in `verification/CHECKPOINT_24_REPORT.md` and `provenance/checkpoint-24-sources.json`.

Checkpoint 23 added eight modules:

- `IKO/GenusTwoOrdinaryFixedVectors.lean` counts fixed vectors for every two-by-two Cartier matrix; `Hyperelliptic/GenusTwoOrdinary.lean` proves the actual Jacobian ordinary/determinant criterion for every presented separable quintic/sextic.
- `IKO/SemilinearInvertibility.lean`, `Geometry/CartierVerschiebungRank.lean`, and `Hyperelliptic/GenusTwoOrdinaryVerschiebung.lean` identify the ordinary locus with injectivity and bijectivity of global Cartier and the actual Verschiebung cotangent map, retaining the Frobenius-twisted target.
- `IKO/FifthPowerCongruences.lean` and `Hyperelliptic/FifthPowerClassification.lean` prove the uniform matrix, full-space Cartier, p-rank, and ordinary congruence results for the explicit model y² = x⁵ − 1.
- `Geometry/VerschiebungNaturality.lean` proves actual Frobenius/Verschiebung naturality, cotangent isomorphism invariance and product vanishing from factor vanishing over a fixed perfect field. It also proves equivalence between vanishing of the general group-scheme cotangent map and vanishing of the existing independent Jacobian cotangent map.

Checkpoint 22 modules: `Geometry/SupersingularGeometryTorsion.lean` derives finite point kernels from finite scheme morphisms and faithful group homomorphisms; `JacobianIsogenyTorsion.lean` derives actual Jacobian point divisibility from the Picard group and proves the geometric p-rank consequence; `SupersingularJacobian.lean` transfers the result to every representing Jacobian; `Hyperelliptic/GenusTwoSupersingular.lean` and `IKO/SupersingularObstructions.lean` supply the genus-two and family consequences.

`IKO/GenusTwoFixedVectors.lean` proves the general two-dimensional fixed-vector criterion by polynomial elimination; `Hyperelliptic/GenusTwoPRank.lean` turns it into the p-rank equivalence for any representing Jacobian of a separable quintic/sextic model.

New comparison modules: `Geometry/CartierResidueLocal.lean` and `CartierResidueAdjoint.lean` prove local/global adjointness; `CartierTransport.lean`, `GlobalCartier.lean`, and `GlobalCartierModels.lean` connect the unchanged Cartier implementations; `FrobeniusDifferentialTwist.lean`, `FrobeniusCechSemilinear.lean`, and `JacobianFrobeniusUntwist.lean` fix actual twist and scalar maps; `CartierVerschiebung.lean` and `IKO/VerschiebungCriteria.lean` prove the normalized comparison and actual cotangent vanishing criteria.

- `Elliptic/Supersingular.lean`: geometric definition, Hasse criterion, field-extension invariance.
- `Elliptic/Legendre.lean`: Legendre ellipticity, geometric criterion, Deuring polynomial separability, and a characteristic-three example.
- `IKO/Polynomials.lean`: both branch families and parameter polynomials, uniform coefficient reductions, and separability of family (a)'s branch polynomial.
- `IKO/Semilinear.lean`: inverse-twisted coordinate action and the correctly ordered twisted-square criterion.
- `IKO/CoefficientMatrix.lean`: raw coefficient matrices, uniform sparsity in family (a), exact small-prime family calculations, and a nonzero square-zero example.
- `IKO/QuadraticCoefficients.lean`: general binomial-sum formulas for coefficients symmetric around the middle of a quadratic power.
- `IKO/UniformMatrices.lean`: complete matrix formulas for both families in all four congruence cases.
- `IKO/MatrixCriteria.lean`: uniform matrix-vanishing, nonzero-determinant, and twisted-square criteria; coordinate-action and Frobenius specializations.
- `Differentials/Cartier.lean`, `Monomials.lean`, `Polynomial.lean`: reused and provenance-recorded Cartier existence/uniqueness, regularity preservation, semilinearity, and polynomial extraction.
- `Differentials/Hyperelliptic.lean`: the two actual Cartier coefficient formulas, with degree and denominator proofs.
- `IKO/CartierCompatibility.lean`: injectivity of the two-form coordinate map, actual Cartier compatibility, span stability, and zero/square-zero matrix criteria.
- `IKO/CartierFamilies.lean`: actual Cartier root criteria for both IKO families and the characteristic-three fifth-power distinction, under explicit function-field hypotheses.
- `Differentials/Regularity.lean`: integral-function differentials, the Bezout argument at finite places, the reciprocal-coordinate identities, and all-place regularity from two separable charts.
- `Hyperelliptic/FunctionField.lean`: generalization of the earlier Legendre field construction to a polynomial with a simple root; Eisenstein, degree two, separating coordinate, and dx ≠ 0.
- `IKO/RegularFamilies.lean`: family-B separability, both reciprocal equations and their separability, all-place regularity, and the two explicit field models.
- `IKO/RegularCoordinates.lean`: coordinates valued in actual regular differentials, proved image dimension two, and regular Cartier action and root criteria in the constructed fields.

- `Hyperelliptic/Ramification.lean`: Kummer indices, actual fibre sizes, root-set enumeration, tameness, and total ramification six for separable degree-five/six models.
- `Hyperelliptic/Genus.lean`: genus two by Riemann–Hurwitz and dimension two of the entire regular-differential space.
- `IKO/RegularBasis.lean`: bijective coordinate maps, linear equivalences, actual regular bases, full-space Cartier coordinates, and full-space root criteria.

- `PicardTorsion/Logarithm.lean`, `Cartier.lean`: provenance-recorded reuse of the actual divisor-class logarithmic injection, regularity, and Cartier fixedness.
- `PicardTorsion/Equivalence.lean`: surjectivity onto all regular Cartier-fixed forms, an additive equivalence, and torsion-triviality consequences.
- `IKO/FixedVectors.lean`: exact root counts and fixed-vector counts for diagonal and antidiagonal inverse-Frobenius actions.
- `IKO/TorsionCriteria.lean`: additive family equivalences, actual p-torsion cardinalities and finiteness, and polynomial/Cartier triviality criteria.

- `Geometry/AbelianVariety.lean`: actual commutative proper smooth connected group schemes, finite surjective isogenies, categorical products, points, and base change.
- `Geometry/Superspecial.lean`: geometric product-isomorphism and product-isogeny predicates, implications, invariance, and the dimension-one p-torsion consistency theorem.
- `Geometry/Jacobian.lean`: a Jacobian specified by the genuine Picard universal property, its tensor-induced group law, and curve predicates over an algebraically closed base. Existence for the explicit families is established in `JacobianConstruction.lean` and `IKO/Jacobians.lean`.
- `NewtonPolygon/Basic.lean`: lower convex coefficient hulls, normalized p-adic valuations, half-slope shapes, and coordinate-invariant characteristic-polynomial polygons.
- `NewtonPolygon/Examples.lean`: actual linear endomorphism, genus-two/five polynomial shapes, and a negative example. The genus-five polynomial example does not assert a theorem about a curve.

- `Geometry/CurveModels.lean`: actual smooth proper integral curve models, geometric base points, and equations in scheme function fields.
- `NewtonPolygon/WittValuation.lean`: the actual Witt DVR valuation and proof that v(p) = 1.
- `NewtonPolygon/Isocrystal.lean`: scalar Frobenius period, linear q-Frobenius, normalized Newton polygon, and invariance under isocrystal isomorphism.
- `NewtonPolygon/HalfSlope.lean`: standard semilinear block F(x,y) = (σ(y),pσ(x)), its prime-field characteristic polynomial, and its half-slope Newton polygon.

- `Geometry/JacobianPoints.lean`: actual multiplication-by-n kernels, geometric p-rank and ordinarity, and group/torsion equivalences.
- `Geometry/JacobianConstruction.lean`: Picard-representing Jacobian existence, correct dimension, and Abel–Jacobi with its base-point identity.
- `IKO/Jacobians.lean`: the two constructed Jacobians, geometric p-torsion counts, p-ranks, and ordinary loci.
- `Geometry/DifferentialTransport.lean`: canonical differential pullback equivalence across a function-field isomorphism.
- `Geometry/GlobalDifferentials.lean`: actual affine-cover global sections and their proved generic-restriction equivalence with regular forms.
- `IKO/GlobalForms.lean`: global bases, dimension two, Cartier matrices, and zero/square-zero root criteria.

- `IKO/Hypergeometric.lean`: the general differentiated-operator argument, the degree bound, and algebraic-closure descent for separability.
- `IKO/BinomialPolynomial.lean`: a uniform binomial family, coefficient recurrence, endpoint values, exact degree, and separability.
- `IKO/SimpleRoots.lean`: IKO Proposition 1.14 for g_p and h_p, admissible roots, and distinct geometric root counts.
- `IKO/HypergeometricEquations.lean`: all four differential equations corresponding to IKO (1.34).

- `Geometry/PointBaseChange.lean`: group homomorphism and injectivity for actual points under a field extension, by faithfully flat descent.
- `Geometry/SuperspecialTorsion.lean`: geometric product isomorphism implies trivial p-torsion and p-rank zero; positive-dimensional ordinary abelian varieties are not superspecial.
- `Geometry/JacobianIndependence.lean`: divisor-class/point equivalence for any representing Jacobian; p-rank and torsion cardinality independent of the base point and representation.
- `IKO/GeometricObstructions.lean`: necessary polynomial/Cartier criteria for geometric superspeciality of both actual curves; nonroot exclusions and the characteristic-three family-B exclusion.
- `IKO/SuperspecialParameters.lean`: finite actual geometric superspecial parameter loci and upper bounds from the proved root counts.

- `Hyperelliptic/Reciprocal.lean`: general reflected-polynomial identities, separability of the reciprocal chart, and all-place regularity.
- `Hyperelliptic/GenusTwoBasis.lean`: model construction from every separable quintic/sextic and the full regular-differential basis.
- `Hyperelliptic/GenusTwoCartier.lean`: full-space matrix coordinates and zero/twisted-square-zero criteria for every such equation.
- `Hyperelliptic/GenusTwoGlobalForms.lean`: full scheme-global basis, dimension, and Cartier matrix criteria.
- `Hyperelliptic/GenusTwoJacobian.lean`: actual Jacobian construction and the general square-zero Cartier ⇒ p-rank-zero implication for any representing Jacobian.
- `Hyperelliptic/CharacteristicThree.lean`: the actual genus-two example y² = x⁵ − 1, full-space Cartier distinction, and actual Jacobian p-rank zero.

- `Geometry/JacobianInfinitesimal.lean`: Poincare pullback gives a bijection between actual square-zero Jacobian points and first-order line-bundle deformation classes; compatibility with coefficient changes and pointed curve pullback is proved.
- `Geometry/JacobianCotangent.lean`: the actual local cotangent space at zero, its genus dimension, the local-ring comparison with infinitesimal points, and the unique cotangent differential of Picard pullback with its deformation-class compatibility. No Cartier–Verschiebung comparison is asserted.

Paths above are relative to `SupersingularCurves/`. `Audit.lean` checks transitive axioms for declarations from the project and the selected FLT modules, including declarations outside their expected public namespaces. It also checks supersingular and nonsupersingular examples over finite fields. `verification/BasisExamples.lean` checks whole-space results over algebraic closures of finite fields. `verification/TorsionExamples.lean` checks actual torsion counts in characteristics 3, 5, and 7, covering all four congruence cases and both cardinality branches. `verification/GeometricExamples.lean` checks actual Jacobian point counts, an ordinary case, and zero/nonzero global Cartier examples. `verification/SimpleRootExamples.lean` checks boundary characteristics, both congruence classes, a concrete root and its derivative, and the necessity of the general ODE degree hypothesis. `verification/SuperspecialExamples.lean` checks actual non-superspecial curves, p-rank at a root for an arbitrary representing Jacobian, and both parameter bounds. `verification/GeneralGenusTwoExamples.lean` checks the actual characteristic-three genus, global Cartier distinction and Jacobian p-rank, a sextic in characteristic five, and a sextic with a root at zero.

At checkpoint 24 the declaration inventory contained 134 project proof modules, 891 public theorem declarations, and 24 private supporting lemmas: 24 modules, 94 public theorems, and five private lemmas added since checkpoint 23. Its historical evidence remains in `verification/CHECKPOINT_24_REPORT.md`. The current inventory and executed checks are recorded in the checkpoint 29 report. Inventory counts are not completion percentages.

The Newton construction applies to valued polynomials, rational linear endomorphisms, and actual finite-field Witt-vector F-isocrystals. An isocrystal has not yet been attached to either IKO curve or Jacobian. The geometric curve predicates exist, and geometric superspeciality now implies the computed Cartier/root condition for both IKO families. The reverse implication and the supersingularity equivalence remain unproved.

The new modules `Geometry/CechCurvePullback.lean`, `CechGluingPullback.lean`, `CechCurveBaseChange.lean`, `CechCocycleNaturality.lean`, `CechDeformationNaturality.lean`, `FrobeniusCechPullback.lean`, and `FrobeniusCechComparison.lean` supply the actual cochain construction, geometric transition-function transport, cocycle naturality, and independent-V comparison. `verification/FrobeniusCechExamples.lean` instantiates them on an actual genus-two curve.

## Reuse and provenance

The vendored upstream source modules are selected from [Anthropic's FLT repository](https://github.com/anthropics/fermats-last-theorem/tree/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef), preserving license and attribution files. The exact source and compatibility-port counts are recorded in the manifests, with documented compatibility updates for Mathlib’s `List.TFAE.out` indexing; their mathematical statements are unchanged. The exact dependency closure, upstream Git blob hashes, and source hashes are recorded in `vendor/flt/upstream-manifest.json`; the ten ports are recorded in `vendor/flt/port-manifest.json`. Upstream proof files have been compiled with this project's pinned environment; their existence alone is not treated as verification.

The user's uploaded genus-five checkpoint supplied the compatible dependency pins and reference implementation. Its archive hash is in `provenance/checkpoint-12.json`. The three reused Cartier modules and their exact adaptations are documented in `provenance/cartier-reuse.json`; the eight unchanged checkpoint-2 proof modules and all 14 unchanged checkpoint-3 proof modules are recorded in their respective provenance files. The generalization from `LegendreField.lean` is documented in `provenance/function-field-generalization.json`. All 18 unchanged checkpoint-4 proof modules are recorded in `provenance/checkpoint-4.json`. The additional pinned foundations and the six generalized ramification/genus declarations are recorded in `provenance/basis-foundations.json` and `provenance/ramification-generalization.json`. All 21 unchanged checkpoint-5 proof modules are recorded in `provenance/checkpoint-5.json`. The two Picard adaptations are recorded in `provenance/picard-reuse.json`; the 16 additional pinned upstream modules are recorded in `provenance/picard-foundations.json`. All 26 unchanged checkpoint-6 proof modules are recorded in `provenance/checkpoint-6.json`. The 23 added Picard/group-scheme foundation modules are recorded in `provenance/geometry-foundations.json`; the additional documented compatibility port only adjusts `List.TFAE.out` indices. All 31 checkpoint-7 proof modules are recorded in `provenance/checkpoint-7.json`. The seven added, unchanged upstream model-construction modules are recorded in `provenance/checkpoint-8-vendor-additions.json`. All 35 checkpoint-8 proof modules are recorded in `provenance/checkpoint-8.json`. Checkpoint 9 adds 1008 Jacobian-foundation and 14 differential-foundation modules at the same pinned upstream commit; these additions are recorded in the two checkpoint-9 provenance files. All 41 checkpoint-9 proof modules are recorded in `provenance/checkpoint-9.json`. The generalization of the vendored Deuring-polynomial proof layout is recorded in `provenance/hypergeometric-generalization.json`, with the exact upstream source and eight corresponding declarations. The new sources live in a separate directory and namespace. No genus-five theorem is claimed here.

For this hosted session, exact-version external package caches were reused. The source archive omits caches and binaries. Earlier hosted checkpoints required an executable-path compatibility shim; its C source is included for transparency. That shim redirects the compiler's own `/proc/<pid>/exe` lookup to `/proc/self/exe` and changes no Lean proof checking. It is not needed for a normal local installation.

Checkpoint 20 proof attribution and retained hashes are recorded in `provenance/cech-curve-naturality.json`, `cech-pullback-vendor-additions.json`, and `mini-checkpoint-19.json`. The eight added upstream modules are exact pinned source copies.

## Mathematical references

- [Ibukiyama–Katsura–Oort, *Supersingular curves of genus two and class numbers*, §1](https://www.numdam.org/item/CM_1986__57_2_127_0.pdf).
- [Achter–Howe, *Hasse–Witt and Cartier–Manin matrices: A warning and a request*](https://arxiv.org/html/1710.10726v5), for semilinear conventions.
- [Booher–Pries, *Producing supersingular curves of genus five*](https://arxiv.org/html/2410.20262v2), especially the related constructions in §5.

- [Achter–Pries, *Superspecial rank of supersingular abelian varieties and Jacobians*](https://arxiv.org/abs/1403.0023), for the geometric isomorphism/isogeny distinction.

- [Lurie, *Isocrystals*, Lecture 26](https://www.math.ias.edu/~lurie/205notes/Lecture26-Isocrystals.pdf), for the Witt-field semilinear definition and standard slope blocks.

- [Pries, *A short guide to p-torsion of abelian varieties in characteristic p*](https://www.math.colostate.edu/~pries/Preprints/00DecPreprints/08groupschemeconm1007.pdf), for geometric p-rank and ordinarity.

Checkpoint-11 reuse and scope are recorded in `provenance/geometric-obstructions.json`. All checkpoint-10 proof bytes are recorded and checked in `provenance/checkpoint-10.json`. No classification theorem is introduced as an assumption.

Checkpoint-12 reuse and scope are recorded in `provenance/general-genus-two.json`. All 50 checkpoint-11 proof modules are preserved in `provenance/checkpoint-11.json`. The older `provenance/checkpoint-12.json` records the originally uploaded genus-five checkpoint and is unchanged. The generic results concern presented quintic/sextic models; the presentation theorem for arbitrary genus-two curves is still pending.


Checkpoint-14 source attribution and the 35 added pinned dependencies are recorded in `provenance/frobenius-verschiebung.json`. The single added compatibility port adjusts only a `List.TFAE.out` index. The new modules are `Geometry/Frobenius.lean`, `Geometry/VerschiebungPrimeField.lean`, and `Geometry/JacobianVerschiebungPrimeField.lean`, under `SupersingularCurves/`. The prime-field construction is not the missing Cartier comparison.


Checkpoint-15 additions: `Geometry/FrobeniusTwistGroup.lean`, `Geometry/Verschiebung.lean`, `Geometry/PointedCotangent.lean`, `Geometry/JacobianVerschiebung.lean`, and `Geometry/PicardFrobeniusTwist.lean`. Proof attribution and the 28 unchanged pinned dependency additions are recorded in `provenance/perfect-field-verschiebung.json`. No new compatibility ports were needed.


Checkpoint-16 additions: `Geometry/FrobeniusLineBundle.lean` and `Geometry/FrobeniusPicardComparison.lean`. The new comparison supersedes the open-map-comparison status recorded in earlier checkpoint module introductions. Proof attribution and six exact pinned dependency additions are in `provenance/frobenius-picard-comparison.json`. No new compatibility ports were needed.


Checkpoint-17 additions: `Geometry/PicardCech.lean`, `Geometry/PicardCotangentCech.lean`, and `Geometry/FrobeniusPicardCohomology.lean`. The new comparison uses the normalized-cocycle construction, rather than only a dimension equality. Attribution is recorded in `provenance/picard-cech-comparison.json`; no new vendored dependencies or compatibility ports were added.


Checkpoint-18 additions: `Geometry/SchemeCechCohomology.lean`, `Geometry/CechRepartition.lean`, and `Geometry/JacobianRepartition.lean`. Run `bash verification/verify_checkpoint18.sh` for the retained-source plus new-proof verification route, or `bash verification/verify.sh` for the full audit of every project/vendor declaration. The report distinguishes which route was executed.

Checkpoint-19 additions: `Geometry/ResidueFoundation.lean`, `Geometry/ResiduePairing.lean`, `Geometry/SchemeResidueDuality.lean`, and `Geometry/JacobianResidue.lean`. Attribution and the 17 exact pinned dependency additions are in `provenance/residue-duality-comparison.json`. The actual-curve application assumes no unproved residue theorem or duality comparison. Run `bash verification/verify_checkpoint19.sh` for the current focused verification route, including every declaration in the four new project modules and all 17 new vendor modules. `verification/ResidueExamples.lean` instantiates the comparison on the genuine genus-two curve over the algebraic closure of F3.

Checkpoint 24 source provenance is in `provenance/checkpoint-24-sources.json` and `checkpoint-24-degree-imports.json`. Its bounded reverse-classification source inspection is retained in `provenance/checkpoint-24-classification-source-inspection.md` with pinned source hashes and extracted declarations.
