# Checkpoint 20: Frobenius cochains and Jacobian Verschiebung

20 September 2026 · Lean 4.34.0-rc2

**The Frobenius/cochain compatibility step is complete.** The normalized deformation cocycle now commutes with actual curve pullback. Under that comparison, the tangent action of the independently constructed Jacobian Verschiebung equals the actual relative-Frobenius map on Čech H¹. Its dual pairing identity is proved, with the Frobenius twist retained.

This does **not** yet prove Cartier = V. Residue/Cartier adjointness and the general geometric superspecial/supersingular criteria remain open.

## The theorem now proved

For a genuine representing Jacobian J of a curve model C over a perfect field K of characteristic p, and the specified two-affine cover, write β for the Poincare-normalized tangent/Čech comparison. The new theorem is

\[
\beta_C(\ell\circ V^*)=F_{C/K}^{*}(\beta_{C^{(p)}}(\ell)).
\]

Here V is the previously constructed scheme morphism J⁽ᵖ⁾ → J, and V* is its actual cotangent differential. The right side is now the cohomology map induced by the actual relative Frobenius C → C⁽ᵖ⁾ on structure-sheaf sections. Neither operator is defined by this equality.

The general coefficient-module theorem is `Jacobian.verschiebungCotangent_cochain`. The H¹ version is `Jacobian.tangentCechEquiv_verschiebung_cochain`. The dual statement, for every class q on the twisted curve, is

\[
\langle x,F_{C/K}^{*}q\rangle_C
=\langle V^*x,q\rangle_{C^{(p)}}.
\]

It is proved as `Jacobian.cotangentDualCechEquiv_frobenius_cochain`.

## What closes the gap

1. **Actual cochains.** `CechCurvePullback` constructs pullback from the scheme morphism's maps on sections, proves it commutes with the Čech differential, and descends it to H¹. The formula on overlap representatives determines the map uniquely.
2. **Actual invertible sheaves.** `CechGluingPullback` constructs frames on pulled-back line bundles normalized on the actual pulled-back local sections. Their transition unit is the original unit acted on by the actual overlap map.
3. **Base-change charts.** `CechCurveBaseChange` proves that curve pullback corresponds to identity on the coefficient algebra tensored with the curve map, under the specified affine tensor-product chart isomorphisms. The same formula holds for transition units.
4. **Normalized deformation classes.** `CechCocycleNaturality` proves compatibility of reduction, first-order coefficients, and quotient classes. `CechDeformationNaturality` then proves naturality for every actual deformation and every deformation class, for arbitrary square-zero coefficient modules.
5. **Relative Frobenius and V.** `FrobeniusCechPullback` proves the actual twisted cohomology map and its p-power formulas on projected sections. `FrobeniusCechComparison` combines these results with the earlier independent-V/Picard comparison.

The scalar distinction is essential: curve pullback acts as identity on the square-zero coefficient algebra tensored with pullback on the curve factor. It does not raise the whole first-order transition unit to the p-th power. For relative Frobenius the displayed section formula is b·sᵖ, with b unchanged and the source on the actual twisted curve.

## Match to the sheet and IKO §1

| Requested part | Status after checkpoint 20 |
|---|---|
| Elliptic supersingularity and Legendre family | Retained definitions, odd-characteristic Hasse criterion, field-extension invariance, polynomial criterion and examples. |
| Superspecial versus supersingular | Independent geometric product-isomorphism and product-isogeny definitions retained; superspecial ⇒ supersingular proved. The general Cartier converses remain open. |
| Matrix on dx/y and x dx/y | Retained full regular/global bases and actual Cartier matrix, zero and twisted-square-zero formulas for every presented separable quintic/sextic model. |
| Jacobian cotangent/global-form comparison | Retained residue-normalized comparison over algebraically closed fields, with hypotheses supplied from the actual curve. |
| **Frobenius/cochain compatibility in §1.1** | **Completed:** actual deformation cocycle commutes with curve pullback; independent V tangent action equals actual relative-Frobenius H¹ pullback; dual pairing identity proved. |
| Cartier compared with Jacobian V | Partial: residue/Cartier adjointness and the resulting transport through the cotangent/global-form comparison remain. |
| IKO Lemma 1.1(i) and (ii) | General geometric supersingular and superspecial equivalences remain open. Matrix and p-rank results do not alone construct the required isogeny or isomorphism. |
| IKO families/parameter polynomials | Retained actual models/Jacobians, matrices, p-rank and root criteria, ordinary loci, and Proposition 1.14 via its main differential-equation argument. Further geometric and class/quotient statements remain. |
| Newton polygon | Retained valued-polynomial and finite-field Witt-isocrystal definitions, invariance and examples. Attachment to the actual curves/Jacobians and the geometric comparison remain open. |

`SECTION1_COVERAGE.md` retains the complete proposition-by-proposition ledger. This checkpoint completes an operator-comparison step; it does not complete all of IKO §1 or prove a separately specified Oort conjecture.

## Verification and preservation

**All current checks passed.** The full project build succeeded (10,377 jobs). All five concrete integration examples compiled. The source audit checked 156 source/provenance hashes and exact dependency closure; the scan of 1,613 project/vendor Lean sources found no admitted proofs, added axioms or native-evaluation markers.

The transitive proof audit inspected **230 declaration entries**: 65 in the seven new project modules and 165 in the eight added vendor modules. Their only axiom dependencies are `propext`, `Classical.choice` and `Quot.sound`. Both stored types/bodies and resolved declarations were inspected. Execution details and log hashes are recorded in `verification/checkpoint-20-run.json`, completed 2026-09-20T00:58:24.550552+00:00.

The five concrete integration examples use the actual genus-two curve y² = x⁵ − 1 over the algebraic closure of F₃. They instantiate the twisted H¹ map, the p-power representative formula, the independent-V tangent comparison, the dual pairing identity, and the arbitrary-coefficient theorem with V = K × K.

All 78 previous proof modules and all 1,519 previous vendor modules are byte-identical to checkpoint 19. The eight added vendor modules exactly match the pinned upstream source. The project now contains 85 proof modules, 622 public theorem declarations, and ten private supporting lemmas. This checkpoint adds 38 public declarations and one private lemma in seven modules. These are inventory counts, not completion percentages or claims of mathematical novelty.

The earlier full audit and nine earlier integration suites remain historical evidence for unchanged sources; they were not rerun. The current full build reuses existing checked artifacts for unchanged modules. It is not a clean recompilation of every dependency.

To reproduce the current focused verification:

```sh
lake exe cache get
bash verification/verify_checkpoint20.sh
```

The comprehensive route remains `bash verification/verify.sh`.

## Provenance and remaining work

The pulled-frame construction uses the pinned affine pullback equivalence and adapts the existing frame-normalization argument from changes of coefficients to curve morphisms. The normalized cocycle and its independence of frames are reused from the pinned construction. New proofs establish curve-morphism naturality and its application to independently constructed V. Attribution and hashes are in `provenance/cech-curve-naturality.json`, `cech-pullback-vendor-additions.json`, and `mini-checkpoint-19.json`.

Pins remain Lean `leanprover/lean4:v4.34.0-rc2`, Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`, and FLT `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`. The proof checker is unmodified. The source ZIP includes dependency sources, licenses, build pins, provenance, the coverage ledger, reports and verification logs; compiled caches are omitted.

**Next:** prove residue/Cartier adjointness for this actual Frobenius map, then use the specified cotangent/global-form comparisons to finish the Cartier–Verschiebung identity. The geometric Cartier-zero ⇔ superspecial and Cartier-square-zero ⇔ supersingular classifications are still separate substantial goals.
