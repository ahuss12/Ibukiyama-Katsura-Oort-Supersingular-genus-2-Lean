# Checkpoint 17: actual cotangents, dual Čech cohomology, and Frobenius deformation cocycles

19 September 2026 · Lean 4.34.0-rc2

**The cotangent-to-dual-Čech-H¹ comparison is now proved for a specified two-affine cover. The comparison with regular/global differentials and Cartier remains unfinished, as do the general geometric superspecial/supersingular criteria.** All 68 proof modules from checkpoint 16 are preserved unchanged.

## What is newly proved

Fix an actual pointed scheme over a field K, a genuine Picard representation, and a two-affine cover 𝒱. Write H¹_𝒱 for the cokernel of the actual structure-sheaf Čech differential and Cot₀(J) for the maximal ideal modulo its square in the actual local ring at the identity.

For every square-zero coefficient module W, Lean constructs a linear equivalence

\[
\operatorname{Hom}_K(\operatorname{Cot}_0(J),W)
\;\simeq_K\; H^1_{\mathcal V}(C,\mathcal O_C)\otimes_K W.
\]

A cotangent functional gives an actual square-zero point by its local-ring map. That point pulls back the actual universal Poincare bundle. The linear part of a normalized transition unit then gives its Čech class. The comparison is independent of the normalized transition unit representing the same deformation, and is natural in W. Naturality on product coefficient modules proves additivity; scalar naturality proves K-linearity.

Specializing W to K gives the tangent/H¹_𝒱 comparison. For a representing scheme locally of finite type over K, the code proves finite dimensionality of the actual cotangent: its local ring is Noetherian, its cotangent is finite over the residue field, and the rational identity point identifies that residue field with K. Evaluation into the double dual gives

\[
\operatorname{Cot}_0(J)
\;\simeq_K\; H^1_{\mathcal V}(C,\mathcal O_C)^\vee.
\]

The equivalence has an explicit evaluation formula and a proved uniqueness property. Its normalization is fixed by the actual Poincare deformation and transition cocycle, rather than selected from a dimension equality. Canonicity here is relative to the specified cover; independence under changing or refining the cover is not proved in this checkpoint.

Compatibility with pointed curve pullback is proved **at the level of actual line-bundle deformation cocycles**, using Picard representability and actual sheaf pullback isomorphisms. This compatibility is a conclusion, not a hypothesis.

## Application to the independent Verschiebung

The comparisons are instantiated for the genuine Jacobian and its actual Frobenius twist over a perfect characteristic-p field. The twisted cover is obtained by actual base change; the source and target twists are retained.

Checkpoint 16 proved that curve-Frobenius Picard pullback equals V_J, with V constructed independently by descent. The new theorem `Jacobian.verschiebungCotangent_cech` proves, for every coefficient module W, that composing a cotangent functional with V_J* corresponds to the normalized Čech class of the actual curve-Frobenius pullback of its Poincare deformation on the twisted curve.

For scalar-valued functionals, let α_J denote the tangent/Čech comparison and δ_𝒱 the Čech class of a deformation. The proved formula is

\[
\alpha_J(\lambda\circ V_J^*)
=\delta_{\mathcal V}(F_C^*L_\lambda),
\qquad
\lambda:\operatorname{Cot}_0(J^{(p)})\to K.
\]

The dual evaluation identity is proved too: pairing a cotangent vector x with this pulled-back deformation gives λ(V_J* x).

**This is not yet the Cartier identity.** The right side is constructed from an actual pulled-back line bundle. Its identification with a separately defined map on Čech cochains, the comparison with function-field/repartition cohomology, and the residue-pairing compatibility with Cartier remain to be proved.

## Status of the requested work

| Component | Status after checkpoint 17 |
|---|---|
| Independent Jacobian V and actual cotangent differential | Retained, proved over perfect fields with the actual twist. |
| Curve-Frobenius Picard pullback = independent V | Retained from checkpoint 16. |
| Cotangent/dual-Čech-H¹ comparison | **Newly proved**, with normalization, uniqueness, and actual deformation-pullback compatibility. |
| Apply this comparison to V and the Frobenius twist | **Newly proved** for actual Frobenius-pulled-back deformation cocycles. |
| Cotangent/global-regular-differential comparison | **Open.** Canonical residue/cohomology comparisons remain. |
| Actual Cartier = Jacobian V cotangent action | **Open.** The correct scalar twist and residue compatibility remain essential. |
| General genus-two Cartier zero iff geometric superspeciality | **Open.** The actual product-isomorphism classification is still required. |
| General genus-two Cartier square zero iff geometric supersingularity | **Open.** The actual product-isogeny classification and converse are still required. |

## Match to the professor's sheet and IKO §1

| Sheet / paper component | Verified scope | Remaining scope |
|---|---|---|
| Elliptic curves and supersingular definition | Actual Weierstrass curves, geometric p-torsion definition, odd-characteristic Hasse criterion and base-extension invariance. | Further characterizations and the separate scheme/Weierstrass comparison. |
| Legendre family | Ellipticity, Deuring/Hasse criterion, separability and examples. | Retained unchanged. |
| Superspecial and supersingular curves | Independent geometric predicates using actual product isomorphisms/isogenies; superspecial implies supersingular. | General Cartier equivalences and geometric converses. |
| Boxed Newton polygon | Coefficient-hull and finite-field Witt-isocrystal definitions, invariance and half-slope examples. | The isocrystal of the actual curve/Jacobian and the geometric comparison. |
| Boxed §1 matrix; equations (1.1)–(1.5) | Actual regular/global bases and Cartier matrices for presented separable quintic/sextic models. Now also cotangent/dual-Čech-H¹ comparison and V's action on Frobenius-pulled-back deformations. | Regular-form/Cartier identification and presentation of every abstract genus-two curve. |
| IKO Lemma 1.1 | Matrix/operator criteria and the retained implication to actual Jacobian p-rank zero; stronger p-rank equivalences for the two families. | General geometric superspeciality/supersingularity equivalences. |
| IKO families and parameter polynomials | Actual models/Jacobians, Cartier formulas, p-torsion counts, p-ranks, ordinary loci, necessary superspecial conditions and parameter bounds. | Geometric converses, quotients, isomorphism and automorphism classifications. |
| IKO Proposition 1.14 | Main differential-equation separability proof, all four equations (1.34), endpoints, degrees and root counts. | Retained unchanged; the gamma-function presentation uses an algebraic coefficient recurrence. |

`SECTION1_COVERAGE.md` retains the complete proposition-by-proposition ledger. This checkpoint does not complete the whole section or the intended geometric conclusions. No separate precise “Oort conjecture” has been fixed or proved.

## Source and attribution

- `Geometry/PicardCech.lean`: normalized-cocycle map on actual deformation classes, equivalence, coefficient naturality and representative formula.
- `Geometry/PicardCotangentCech.lean`: actual cotangent/cohomology comparisons, finite dimensionality, evaluation, uniqueness, and deformation-pullback compatibility.
- `Geometry/FrobeniusPicardCohomology.lean`: actual Jacobian/twist instances and the independent V action on Frobenius-pulled-back deformation cocycles.

There are **71 proof modules and 545 public theorem declarations**, plus the retained nine private supporting lemmas. This checkpoint adds 20 public supporting/result declarations in three modules. Counts do not measure mathematical novelty or percentage completion.

The normalized cocycle construction and classification were already in the pinned FLT dependency closure. This checkpoint exposes that specific map, generalizes the existing scalar-valued naturality-to-linearity proof to every coefficient module, constructs and characterizes the actual dual comparison, and proves its indicated pullback/V applications. Local-ring and Poincare helpers are also reused. Exact attribution is in `provenance/picard-cech-comparison.json`.

**No upstream modules or compatibility ports were added.** All 1,502 vendor modules and 68 previous project proof modules are byte-identical to checkpoint 16. The vendor total remains 1,495 exact upstream files and seven previously documented compatibility ports.

## Verification

**All verification gates passed.** All three new proof modules compiled, the full project build succeeded, and all seven example suites passed, including the new actual-curve cohomology integration suite. The final build reused unchanged checked artifacts for retained modules; it was not a clean rebuild of every dependency. The provenance audit checked 125 current source hashes, upstream Git blobs, exact import closure, and preservation of all prior proof modules. A comment-stripped scan of **1,574 project/vendor Lean sources** found no admitted-proof, added-axiom or native-evaluation markers. The scanner is included and runs from the verification script.

The origin-based transitive axiom audit passed for **1,631 project declarations and 26,817 imported FLT declarations**, allowing only `propext`, `Classical.choice`, and `Quot.sound`. This includes the actual cotangent/dual-Cech-H1 equivalence, its normalization and uniqueness, and the V action formula on actual Frobenius-pulled-back deformation cocycles. It does not certify the explicitly unproved Cartier identity or geometric classifications.

Execution details and log hashes are in `verification/checkpoint-17-run.json` (completed 2026-09-19T23:02:27.250324+00:00).

The new `verification/CohomologyExamples.lean` suite uses the existing genuine genus-two curve y² = x⁵ − 1 over the algebraic closure of F₃. It verifies Čech-H¹ dimension two, instantiates the actual twisted cotangent equivalence, and checks the V/deformation interface for a product coefficient module. It assumes neither a geometric classification nor Cartier/V equality.

Pins: Lean `leanprover/lean4:v4.34.0-rc2`, Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`, FLT `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`. The proof checker is unmodified. Original licenses/notices are included.

From the extracted source directory:

```sh
lake exe cache get
bash verification/verify.sh
```

The ZIP includes proof and dependency sources, seven example suites, coverage, provenance and verification logs. The separate optional Linux compiled cache excludes the compiler and external dependency caches; see `verification/BUILD_CACHE.md`.
