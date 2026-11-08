# Checkpoint 27: actual finite-field scheme descent

Project: `/workspace/scratch/8cf314e8ad34/project/supersingular-curves-mini`.
All checkpoint-27 modules described below are frozen. No further proof or vendor edits are needed to retain this result.

## Final proved theorem

In `Geometry/FrobeniusFiniteFieldDescentScheme.lean`:

```lean
A.exists_finiteField_scheme_model_of_verschiebungCotangent_eq_zero p hV
```

Here `K` is algebraically closed of characteristic prime `p`, `A : AbelianVariety K g`, and
`hV : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0`.
The conclusion is:

```lean
Finite (FrobeniusDescent.fixedField K p 2) ∧
Nat.card (FrobeniusDescent.fixedField K p 2) = p ^ 2 ∧
∃ (X₀ : Scheme) (c₀ : X₀ ⟶ Spec (CommRingCat.of (fixedField K p 2)))
  (d : A.group.X.left ⟶ X₀),
  IsPullback d A.group.X.hom c₀
    (Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K)))
```

This constructs a genuine underlying scheme model over the actual subfield with `p²` elements. No model, invariant bundle, graded action, fixed basis, or descent datum is assumed by the final theorem. It does **not** construct a descended group scheme or an elliptic-product decomposition.

Validation: selected Lake build passed **10,708 jobs**; both final declarations use only `propext`, `Classical.choice`, `Quot.sound`. Logs: `verification/checkpoint-27-finite-field-scheme-{build,axioms}.log`. Independent read-only review by `sections_descent27` found no hidden model/descent assumption or unwanted K-linearity.

## Actual dependency/API chain

1. `A.exists_frobeniusSquare_automorphism_invariant_bundle p hV` in `FrobeniusFiniteFieldDescent.lean` constructs an actual scheme automorphism `τ`, invertible sheaf `M`, invariant sheaf isomorphism, and finite projective presentation. It proves `τ.hom ≫ c = c ≫ baseMap p K ≫ baseMap p K` and `[p] ≫ τ.hom = absolute p c ≫ absolute p c`.
2. `FrobeniusFiniteFieldDescentSectionProj.exists_sectionRing_model_of_finiteBySections` in `...DescentSectionIso.lean` constructs the genuine full section ring and an actual `X ≅ Proj 𝓡`. Its proof works from finite projective presentation, with affine preimages and section-fraction localization; no unproved high-power closed embedding is needed. The AV wrapper is `A.exists_frobeniusSquare_sectionRing_model`.
3. `FrobeniusFiniteFieldDescent.sectionRingAction` in `...DescentSectionAction.lean` constructs the coherent ring homomorphism from actual pullback on tensor-power sections. APIs `sectionRingAction_mem`, `sectionRingAction_injective`, and `sectionRingAction_frobeniusSquare_smul` give degree preservation, injectivity, and actual p²-semilinearity. `sectionRingDegreeLinearEquiv` and `finite_sections_of_isProper` prove each homogeneous component is finite dimensional.
4. `FrobeniusDescent.fixedField K p s` is the actual Frobenius fixed subfield. `fixedField_finite` and `fixedField_natCard` prove finiteness and exact cardinality. `exists_fixedScalarExtension` in `FrobeniusFixedScalarExtension.lean` proves canonical scalar extension from fixed vectors; the pure-tensor formula is actual scalar multiplication. Supplied-fixed-basis versions support arbitrary basis index types.
5. `GradedFixedSubalgebra.gradedAlgebra 𝓡 θ hθ` in `GradedFixedSubalgebra.lean` constructs the grading on the literal equalizer `θ.equalizer (AlgHom.id k R)`. Only k-linearity is required; no K-linearity of the semilinear action. `decompose_coe` identifies its components with the ambient ones.
6. `FrobeniusDescent.fixedComponent_isBaseChange` in `...DescentFixedComponents.lean` proves degreewise scalar extension for the actual fixed-component inclusion. `fixedCoefficientAction` supplies actual fixed-field linearity. `...DescentFixedGrading.lean` combines these into `exists_fixedField_proj_model`.
7. `FrobeniusFiniteFieldDescentSectionProj.isPullback_projMap_of_piece_baseChange` in `...DescentProjBaseChange.lean` constructs the actual Proj base-change square. Its irrelevant-ideal coverage is proved from degreewise `IsBaseChange`; no global tensor-ring isomorphism is required. Final `exists_fixedField_scheme_model` transports the square through the actual section-ring isomorphism.

## Exact remaining descent obligations

The currently exported final witness only records the underlying scheme and pullback square. A future proof should retain the explicit fixed-graded construction, rather than treating an arbitrary existential scheme witness as automatically equipped with descended operations.

* Establish compatibility of the canonical section-ring isomorphism and resulting projection `d` with the actual semilinear scheme automorphism `τ`, in particular the invariant identity `τ.hom ≫ d = d`. The ring action was constructed from τ, but this scheme-level identity has not been proved/exported for the final model.
* Prove or expose that τ respects the genuine group multiplication, identity, and inverse over its Frobenius-square base action. Descend these actual morphisms to `X₀ ×_{k₀} X₀ → X₀`, `Spec k₀ → X₀`, and `X₀ → X₀`; establish their scalar-extension comparisons. Descent must be proved, not supplied as a hypothesis.
* Descend the group axioms through faithful field extension, then prove the required smoothness, properness, relative dimension, and geometric connectedness to package an actual `AbelianVariety k₀ g`.
* Identify its q-Frobenius (`q = p²`) with multiplication by `p`, using the already proved geometric relation `[p] ≫ τ = F_abs²` plus the compatibility of d and τ. No scalar-Frobenius identity on a descended abelian variety is presently proved.
* The arithmetic realization of an elliptic-product isogeny and integral product splitting remain further classification obligations. Underlying scheme descent alone does not discharge them.

## Useful already-inspected APIs/sources

* Pinned `GradedOAlgebra.isPullback_projMap_of_isBaseChange` takes a graded algebra map and degreewise `IsBaseChange`; the new Proj bridge discharges its irrelevant-ideal condition.
* `GradedRingHom.map_directSumDecompose` works for graded ring homomorphisms without K-linearity and is the key to fixed-subalgebra grading.
* `IsBaseChange.of_equiv` identifies scalar extension by a genuine linear equivalence with its `1 ⊗ x` formula. `IsBaseChange.inductionOn` proves ideal coverage.
* `IsPullback.of_horiz_isIso` and `IsPullback.paste_horiz` transport the Proj square through the genuine section-ring isomorphism.
* `FrobeniusFiniteFieldDescent.toProj_frobeniusSquare_equivariant_of_fixed_sections` in `...DescentEquivariance.lean` proves equivariance for a finite projective presentation from fixed sections. This concerns that presentation, not yet the full-section-ring isomorphism used for descent.
* `GroupScheme.isMonHom_of_pointMap` in `FrobeniusFactorGroup.lean` packages all-test-scheme group compatibility when actual multiplication and identity comparisons are proved.
* Full pinned proof bodies are available in `/workspace/scratch/8cf314e8ad34/classification-source-inspection/P2M/Sol/`; all statements/definitions are under `classification-source-inspection/full-statements27`. Current remote HEAD was verified equal to pin `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`.

## Vendor restoration question

Neither this agent nor its `sections_descent27` child restored or edited vendor files. No final module uses the four pruned generic `exists_algHom_apply_eq_pullback_of_isPullback` / `baseScalar_smul` theorem-and-proof files. All our selected builds and direct axiom audits have completed. Root may remove the unused files after checking other agents' builds.

## Bounded follow-up lookup: shorter route through the descended zero

This updates the group-operation obligations above: separate descent of multiplication and inverse may be avoidable. A local-only search of the complete pinned theorem/definition filenames and relevant statement contents was followed by reading the concrete Galois-morphism, fixed-point, faithful-flat, and abelian-law candidates and their pertinent proof bodies. No external search or project edits were performed. No generic *single coefficient-Frobenius invariant arbitrary scheme morphism* descent theorem was identified in this bounded lookup; this is not a whole-repository absence assertion.

**A usable point-descent theorem already exists, without any algebraicity assumption:**

`AlgebraicGeometry.Scheme.exists_specMap_fixedField_comp_eq_of_forall_comp_eq`

For arbitrary fields F⊆L, a subgroup `H : Subgroup (L ≃ₐ[F] L)`, a point `x : Spec L ⟶ X`, and invariance under H, it constructs `y : Spec (IntermediateField.fixedField H) ⟶ X` with `Spec(algebraMap) ≫ y = x`. Its complete pinned proof chooses an affine neighbourhood of the image, applies the Spec adjunction, proves the coordinate-ring image is fixed, and restricts its codomain to the fixed subfield. It requires neither `IsGalois F L` nor finite-dimensionality nor algebraicity. For this project take H generated by Frobenius² on perfect K, prove its fixed field equals the actual `fixedField K p 2`, and apply it to the image of the genuine zero section under d. Needed first: `τ.hom ≫ d = d` and compatibility of τ with the genuine zero section.

**An already-built abelian rigidity theorem then constructs the entire descended law:**

`GoodReductionJacobian.RelativeGroupLaw.exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat`

Inputs: arbitrary faithfully flat S→S′, the actual scheme pullback, an abelian-scheme property bundle and actual relative group law on the scalar extension, and only a zero section e over S whose pullback agrees with the old zero. Output: an actual `RelativeGroupLaw S f` with identity e. Its inspected proof derives equality of the two laws over S′⊗S S′ by `eq_of_one_eq_of_abelianSchemePropertyBundle`, then invokes genuine faithfully flat law descent. It does not assume multiplication, inverse, or a law on the descended scheme.

`RelativeGroupLaw.mul_comp_eq_mul_of_isPullback_of_one_comp_eq` supplies multiplication compatibility from equality of identities and the abelian property bundle. **Universe caveat:** this particular companion statement is currently `Type` / `Scheme.{0}`, while the preceding law-existence theorem is universe-polymorphic. The stronger law-descent helper `exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat` is used inside the polymorphic proof and retains multiplication compatibility; strengthening the new wrapper to retain that output may avoid a universe restriction without modifying frozen upstream files.

**Generic faithful-flat morphism descent also exists, but requires its actual cocycle:**

`AlgebraicGeometry.existsUnique_comp_eq_of_isPullback_of_faithfullyFlat`

It gives unique descent of a scheme morphism once the two pullbacks over S′⊗S S′ agree. Mathlib's `AlgebraicGeometry/Sites/Fpqc.lean` also provides `EffectiveEpi` for quasi-compact, surjective, flat scheme morphisms. Neither theorem by itself turns invariance under one Frobenius automorphism into the tensor-overlap equality; that was the precise missing general morphism-descent bridge. The descended-zero/abelian-rigidity route avoids requiring this bridge separately for group operations.

The two candidate theorems `exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq` and its `_of_finiteDimensional` variant are not directly applicable to arbitrary K: they assume `IsGalois k K` (hence algebraicity through `Normal`) and invariance under every k-automorphism; the latter also assumes finite dimension. The first proof explicitly reduces to a finite Galois intermediate field. Do not silently install algebraicity of K over the finite fixed subfield.

Concrete next proof milestone: retain the constructed τ/model data and prove τ/projection and τ/zero compatibilities; use the arbitrary-extension fixed-point theorem to descend zero; apply the genuine law-existence root and establish base-change compatibility. The subsequent scalar-Frobenius identity and elliptic-product realization remain unproved.
