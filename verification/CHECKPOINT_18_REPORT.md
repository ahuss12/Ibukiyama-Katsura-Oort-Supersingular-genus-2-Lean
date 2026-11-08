# Checkpoint 18: explicit Cech/repartition comparison

19 September 2026 · Lean 4.34.0-rc2

**The map from actual structure-sheaf Cech H¹ to function-field repartition H¹ is now proved and characterized on representatives. Its dual is composed with the actual Jacobian cotangent comparison. The regular-differential/Cartier comparison and both geometric classification criteria remain unfinished.**

## The result added in this checkpoint

Let C be a smooth proper integral curve over K, with a specified two-affine cover U₀, U₁. The new code constructs the map

\[
H^1_{\mathcal U}(C,\mathcal O_C)\longrightarrow
H^1_{\mathrm{rep}}(K(C),0).
\]

It is prescribed on every overlap section f: restrict f to the actual function field at the generic point, extend that function by zero on the places belonging to U₀, and take its class modulo integral and principal repartitions. Thus the map is fixed by the geometric construction, rather than selected from an existence or dimension statement.

The proof has two stages:

1. Expose the existing affine generic-germ equivalences as a specified Cech cochain equivalence. Prove that generic restriction commutes with the actual Cech differential and its sign. Pass to cokernels and prove the formula on representatives and uniqueness of the induced map.
2. Compose with the actual off-chart extension map to repartitions. Prove that neither affine chart is the entire curve, that both charts are nonempty, that their place sets cover all places, and that each misses a place. Use the existing Riemann--Roch/approximation theorem to prove bijectivity.

The general bijectivity theorem assumes a perfect base field and `ConstantsAreBase`. In the actual-curve application over an algebraically closed field, the code proves this constants hypothesis from a degree-one place. It also supplies the function-field finite-type, one-variable, and finite-dimensionality hypotheses used in the approximation theorem. These are not left as unexplained classification assumptions.

## Application to the actual Jacobian

For a given genuine representing Jacobian J over an algebraically closed field, compose the new map with checkpoint 17's specified Poincare-cocycle comparison. This gives

\[
T_0(J)\simeq_K H^1_{\mathrm{rep}}(K(C),0),
\qquad
\operatorname{Cot}_0(J)\simeq_K H^1_{\mathrm{rep}}(K(C),0)^\vee.
\]

The cotangent is still the actual maximal ideal modulo its square at the identity. Evaluation on a tangent vector gives the corresponding cotangent functional. This evaluation property uniquely determines the dual comparison. A separate theorem evaluates it on the explicit off-chart extension of every actual overlap section.

The independently constructed Verschiebung also satisfies the transported evaluation formula on repartition classes of actual curve-Frobenius-pulled-back Poincare deformations. The genuine twisted cotangent is retained in the statement.

**This does not yet identify that deformation class with a separately defined Frobenius map on cochains, or identify the dual repartition space with regular differentials through residues. Consequently it does not prove Cartier = V*.**

All comparisons here are relative to a specified affine cover and use the actual scheme function field. Compatibility under changing/refining the cover and transport to another presented function field are not new results of this checkpoint.

## Where the project stands

| Part of the requested project | Current position |
|---|---|
| Elliptic supersingularity and Legendre examples | Retained: actual Weierstrass curves, geometric p-torsion definition, odd-characteristic Hasse criterion, base-extension invariance, Legendre polynomial and examples. Further scheme/Weierstrass comparisons are separate. |
| Genus-two Cartier calculations | Retained: actual regular/global differential bases and Cartier matrices for presented separable quintic/sextic models, with zero/square-zero matrix criteria. Presentation of every abstract genus-two curve remains open. |
| Superspecial and supersingular definitions | Retained: actual product-isomorphism/product-isogeny predicates, with superspecial implies supersingular. Their general Cartier characterizations remain open. |
| Actual Jacobian and Verschiebung | Retained: representing Jacobians, independent V over perfect fields, actual twists/cotangents, and curve-Frobenius Picard pullback = V. |
| Cotangent/cohomology connection | Checkpoint 17 proved cotangent/dual Cech H¹; checkpoint 18 now proves the specified comparison to dual repartition H¹. |
| Regular-differential/Cartier connection | Open: the residue-defined comparison and Frobenius/Cartier compatibility. |
| IKO §1 | Matrix formulas, the two family computations, and the main differential-equation separability argument are retained. General geometric Lemma 1.1 equivalences and further quotient/isomorphism/automorphism classifications remain open. See the full proposition ledger in `SECTION1_COVERAGE.md`. |
| Newton polygon | Retained coefficient-hull and finite-field Witt-isocrystal definitions/examples. Attachment to the actual curve/Jacobian and equivalence to geometric supersingularity remain open. |

No separately specified Oort conjecture has been formalized. Neither the complete professor's sheet nor the complete IKO section is certified finished.

## Major proofs still needed

These are mathematical milestones, not estimates of equal amounts of work:

1. **Residue duality with the specified maps.** Identify dual repartition H¹ with regular differentials using the actual residue functional, supplying its coordinate/residue and residue-theorem hypotheses. Compose with the existing generic-restriction map from global forms.
2. **Frobenius/Cartier compatibility.** Identify the pulled-back deformation cocycle with the actual cochain Frobenius action and prove its residue adjointness to Cartier, with the correct scalar twist. This must connect to the independently constructed V rather than define V to be Cartier.
3. **Superspecial classification.** Prove that Cartier zero for a general genus-two curve is equivalent to its actual Jacobian being isomorphic to a product of supersingular elliptic curves.
4. **Supersingular classification.** Prove that Cartier square zero is equivalent to its actual Jacobian being isogenous to such a product. The existing p-rank and matrix results do not establish this classification.
5. **Additional scope on the sheet/IKO.** Finish any intended abstract-curve presentation, geometric Newton-polygon, and remaining IKO classification statements. The existing coverage ledger records these separately.

The project is taking longer because the short geometric statements require substantial connecting theory in Lean. Much of the recent work builds those connections. The number of supporting declarations is not a defensible completion percentage, and the two requested geometric criteria are not merely packaging work. Earlier expectations that the full project was nearly finished were too optimistic.

## Verification

**All current checks passed.** The three new proof modules compiled and the full project build succeeded (10,341 jobs). The actual-curve integration suite passed. The source audit verified 133 source/provenance hashes, the exact import closure, and preservation of all 71 prior proof modules and all vendor modules. A comment-stripped scan of 1,577 project/vendor Lean sources found no admitted-proof, added-axiom, or native-evaluation markers.

The new-module origin audit checked **56 declarations and their transitive axiom dependencies**, allowing only `propext`, `Classical.choice`, and `Quot.sound`. The unchanged earlier source retains checkpoint 17’s full audit of 1,631 project and 26,817 imported FLT declarations. This is not a claim that the complete historical audit was rerun. Execution details and log hashes are in `verification/checkpoint-18-run.json`, completed 2026-09-19T23:36:29.088095+00:00.

The new integration suite uses the existing genuine genus-two curve y² = x⁵ − 1 over the algebraic closure of F₃. It proves that the actual repartition H¹ space has dimension two and instantiates the independent-V deformation evaluation theorem on that curve.

The default comprehensive verification script remains available and now includes this new suite. For this checkpoint we execute a focused verification route: full project build, source/provenance verification, source scan, the new actual-curve suite, and a transitive axiom audit of **every declaration originating in the three new modules**. Checkpoint 17's full origin audit and seven suites are retained as historical evidence for their byte-identical sources. They are not claimed to have been re-executed in checkpoint 18.

Run the same focused route with:

```sh
lake exe cache get
bash verification/verify_checkpoint18.sh
```

Run a fresh comprehensive audit with:

```sh
bash verification/verify.sh
```

There are 74 proof modules and 565 public theorem declarations. The three new modules add 20 supporting/result theorem declarations; these counts do not measure novelty or closeness to completion. All 71 earlier proof modules and all 1,502 vendored modules are unchanged. No upstream modules or compatibility ports were added.

## Sources and attribution

- `Geometry/SchemeCechCohomology.lean` exposes and characterizes the specific generic-restriction construction already present inside the pinned upstream existence proof.
- `Geometry/CechRepartition.lean` discharges the geometric hypotheses of the existing approximation theorem and characterizes the actual quotient map.
- `Geometry/JacobianRepartition.lean` composes these specified maps with the actual cotangent/Poincare comparison and proves evaluation, uniqueness and the indicated V application.

The generic-restriction construction, approximation theorem and geometric cover arguments reuse or adapt existing checked FLT proofs. Detailed attribution is in `provenance/cech-repartition-comparison.json`. This work is not presented as a new proof of those upstream foundational theorems.

Pins remain Lean `leanprover/lean4:v4.34.0-rc2`, Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`, and FLT `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`. The Lean proof checker is unmodified. Licenses and notices are included.

The source ZIP includes the report, detailed coverage, new and retained verification evidence, and dependency sources. No new full compiled-cache archive is needed for this checkpoint: the existing checkpoint-17 cache can be reused, followed by `lake build` for the new modules and aggregate import. The included build-cache manifest/record describe that checkpoint-17 baseline.
