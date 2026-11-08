# Checkpoint 13: infinitesimal Picard and cotangent comparison

19 September 2026 · Lean 4.34.0-rc2

**The two requested geometric tasks are not complete.** This checkpoint adds a proved infinitesimal comparison for the independently representing Jacobian. It does not prove Cartier = Jacobian Verschiebung, Cartier zero iff geometric superspeciality, or Cartier square zero iff geometric supersingularity.

## Exact progress on the requested tasks

| Requested result | Status after this checkpoint |
|---|---|
| General genus-two Cartier zero iff geometric superspeciality | **Open.** The independent product-isomorphism definition is retained. The general equivalence has not been added as a theorem or assumption. |
| General genus-two Cartier square zero iff geometric supersingularity | **Open.** Existing square-zero Cartier implies actual Jacobian p-rank zero; the required geometric isogeny classification and converse remain missing. |
| Cartier compared with independently constructed Jacobian Verschiebung/cotangent data | **Partial.** Actual local cotangent spaces and the differential of Picard pullback now have a proved infinitesimal interpretation. The Frobenius/Verschiebung and Cartier identifications remain missing. |

## New Lean results

The two new modules are `Geometry/JacobianInfinitesimal.lean` and `Geometry/JacobianCotangent.lean`, under `SupersingularCurves/`.

1. **Infinitesimal Picard comparison.** For any existing representing Jacobian J and coefficient module V, actual maps from Spec(K ⊕ V) to J reducing to zero are in bijection with first-order line-bundle deformation classes on the curve. The forward map is pullback of J's actual Poincare bundle; the inverse follows from representability.
2. **Naturality.** This comparison commutes with coefficient-module maps and pointed morphisms of curves. The latter is a theorem about the actual Picard pullback morphism between representing schemes.
3. **Actual cotangent space.** `J.Cotangent` is the maximal ideal modulo its square in the stalk at J's zero section. Its dimension equals the function-field genus under the stated algebraically closed curve hypotheses.
4. **Local-ring comparison.** Linear maps from that cotangent space to V are identified with actual infinitesimal points using the stalk-to-square-zero-ring construction. This comparison uses more than equality of dimensions.
5. **Geometric cotangent differential.** For a pointed curve morphism f, `pullbackCotangent` is constructed from the induced Picard morphism and the universal cotangent-valued infinitesimal point. Its action on all coefficient modules, compatibility with Poincare deformation classes, and uniqueness are proved.

The main new endpoint is `Jacobian.cotangentDeformationEquiv_pullback`; `Jacobian.pullbackCotangent_unique` supplies uniqueness. Neither contains a Cartier-comparison hypothesis. The new construction works for existing Jacobians over general fields and does not require characteristic p. The separate dimension theorem has explicit algebraically closed/function-field hypotheses.

## What is still needed

The following is a proof roadmap, **not a list of Lean theorems already proved**:

- Specialize the Picard pullback construction to relative Frobenius of the curve. Prove compatibility of representing Jacobians with the Frobenius twist and identify the resulting group-scheme morphism with Jacobian Verschiebung, including its defining multiplication-by-p factorization.
- Identify the actual cotangent space with curve-global regular differentials through the geometric Picard/cohomology and duality constructions. Prove compatibility with the Frobenius action and the existing Cartier operator, with the correct scalar twist. The new deformation comparison is a prerequisite, not this operator identity.
- Prove the geometric classification needed to pass from Cartier kernels to products of supersingular elliptic curves: maximal a-number must imply the required actual product isomorphism; in dimension two, p-rank zero must imply the required actual product isogeny. The converse implications also need their geometric proofs. A route through principally polarized classifications also needs the Jacobian's canonical principal polarization in the formal construction.

IKO states the desired genus-two criteria as Lemma 1.1 and refers to Manin, Nygaard, and Yui for proofs. Thus those geometric steps are dependencies of the IKO formalization, not supplied by the matrix calculation itself. See [IKO, §1.1, printed page 129](https://www.numdam.org/item/CM_1986__57_2_127_0.pdf).

For the operator comparison, [Oda, §5, especially Theorem 5.10 and Corollary 5.11](https://www.numdam.org/item/ASENS_1969_4_2_1_63_0.pdf), supplies a classical de Rham/Dieudonne comparison framework. It has **not** been imported into Lean as an assumed fact. For the distinction between product isomorphism, product isogeny, and torsion-group-scheme conditions, see [Achter–Pries, Theorem 1.1 and §3.1](https://arxiv.org/pdf/1403.0023).

## Verification

**All gates passed.** The project was freshly recompiled: 58 proof modules plus the aggregate import, for 59 compilation units. All six retained example suites passed. The source/provenance audit passed for 102 checked source files and the pinned vendor closure. A separate scan of 1,492 project/vendor Lean files found no admitted-proof, extra-axiom, or native-evaluation markers.

The origin-based transitive axiom audit passed for **1,317 project declarations and 24,884 imported FLT declarations**, allowing only `propext`, `Classical.choice`, and `Quot.sound`. These gates certify the stated supporting results; they do not certify either unproved geometric target.

Run details and exact log hashes are in `verification/checkpoint-13-run.json` (completed 2026-09-19T19:13:41.472518+00:00).

All 56 previous proof modules are unchanged. The project now has 58 proof modules, 440 public theorem declarations, and nine private supporting lemmas. The 12 added public theorem declarations are supporting infinitesimal/cotangent results, not 12 new geometric classification results.

No new vendor modules or compatibility patches were introduced. The 1433 vendored FLT modules remain pinned at `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`; Mathlib remains pinned at `85e3a25e006c35636f0e53b0e9296caca2685bc0`. The restored compiler is the official pinned release, using the already documented executable-path compatibility shim. No parser, kernel, or proof-checking behavior was altered.

## Provenance and reproducibility

The new modules reuse the pinned `P2mTJ` Poincare-deformation helpers and `P2mTJ1` local cotangent construction, plus the existing Picard curve-pullback definitions. Original upstream licenses and notices are retained. `provenance/infinitesimal-picard.json` records these sources; `provenance/mini-checkpoint-12.json` records the unchanged previous proof modules. This last filename deliberately differs from `provenance/checkpoint-12.json`, which concerns the earlier uploaded genus-five archive.

The foundation search inspected relevant project/vendor proof bodies and searched 29,511 indexed upstream solution filenames. The recursive upstream index response was truncated, so the audit is not a claim that every upstream proof body was inspected. Its scope and limitations are recorded in `verification/geometric-foundation-audit.json`.

Build from the extracted source directory:

```sh
lake exe cache get
bash verification/verify.sh
```

The source archive includes the new code, all retained sources, verification logs, source hashes, and updated sheet/IKO coverage. Compiler binaries and external dependency caches are excluded. The separate checkpoint-13 build cache includes the new modules and selected FLT artifacts; external Mathlib/package caches and compiler binaries are excluded.
