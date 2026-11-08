# Checkpoint 14: relative Frobenius and independent prime-field Verschiebung

19 September 2026 · Lean 4.34.0-rc2

**The two requested geometric results remain incomplete.** This checkpoint constructs actual Frobenius and prime-field Verschiebung morphisms, with a cotangent realization. It does not prove either general genus-two geometric Cartier equivalence or the Cartier–Verschiebung identity.

## Status of the two requests

| Requested result | Current status |
|---|---|
| Cartier zero iff geometric superspeciality in genus two | **Open.** The product-isomorphism definition is retained. No general equivalence has been proved or assumed. |
| Cartier square zero iff geometric supersingularity in genus two | **Open.** The previously proved implication to actual Jacobian p-rank zero remains available; the geometric isogeny classification and the converse remain missing. |
| Cartier compared with independently constructed Jacobian Verschiebung/cotangent data | **Partial.** V and its cotangent action are now constructed independently for any given representing Jacobian over the prime field. Equality with Cartier is not proved, including in that case. The V construction over arbitrary perfect fields also remains open. |

## What the new code proves

The new modules are under `SupersingularCurves/Geometry/`.

- **`Frobenius.lean`:** constructs the actual relative Frobenius morphism to the scheme-theoretic Frobenius twist. Its action agrees with p-th powers on every affine test scheme. For a smooth scheme over a perfect field it is finite, flat, locally of finite presentation, and surjective. A rational base point gives a pointed relative Frobenius. Pullback along it induces a morphism between independently representing Picard schemes, with the actual Poincare line-bundle classification property on every test scheme.
- **`VerschiebungPrimeField.lean`:** for a smooth commutative group scheme over `ZMod p`, proves that multiplication by p coequalizes the fibres of the actual Frobenius F. Effective-epimorphism descent constructs a unique actual scheme morphism V. Both **F V = [p]** and **V F = [p]** are proved, along with preservation of the base, identity section, and group multiplication on every test scheme. The group-law proof descends equality along the faithfully flat product F × F. No Cartier operator enters the construction.
- **`JacobianVerschiebungPrimeField.lean`:** applies this construction to any given independently representing Jacobian over `ZMod p`, with the group law derived from tensor product of line bundles. It constructs V's action on actual infinitesimal points and the actual cotangent space at zero. The cotangent action is proved to give that scheme action for every square-zero coefficient module.

The Jacobian result is a theorem about a supplied genuine Picard representation. This checkpoint does **not** prove that the existing IKO family Jacobians descend to the prime field or construct such a descent. Their existing geometric calculations remain over their previously stated base fields.

## What still separates this from completion

1. Extend the independently constructed V to arbitrary perfect fields with the correct Frobenius twist. The prime-field proof uses that base Frobenius is the identity.
2. Identify the Jacobian of the Frobenius-twisted curve with the Frobenius twist of its independently representing Jacobian. Prove that the actual Picard pullback by curve Frobenius is this V. The new Picard pullback is not labeled V by definition.
3. Construct the geometric cotangent/global-differential comparison and prove that V's action becomes the already constructed Cartier operator. Equality of dimensions alone does not supply this comparison.
4. Prove the geometric classification steps: maximal a-number must yield the required product isomorphism; in dimension two, p-rank zero must yield the required product isogeny, with the corresponding converse implications. These results are not consequences of the matrix calculations alone.

IKO states its genus-two criteria as Lemma 1.1 and cites Manin, Nygaard, and Yui for the geometric input. That input is still a formalization dependency. See [IKO §1.1, printed page 129](https://www.numdam.org/item/CM_1986__57_2_127_0.pdf). The de Rham/Dieudonne comparison in [Oda, §5, especially Theorem 5.10 and Corollary 5.11](https://www.numdam.org/item/ASENS_1969_4_2_1_63_0.pdf) describes a classical route for the operator comparison; it has not been assumed as a Lean theorem here.

`SECTION1_COVERAGE.md` remains the item-by-item mapping to the professor's sheet and the whole of IKO §1. The matrix calculations, family polynomials, separability results, actual curve/Jacobian constructions, p-torsion computations, and Newton-polygon definitions from earlier checkpoints are retained. The two missing geometric equivalences are still marked open there.

## Verification

**All gates passed.** All three new proof modules compiled, the full project build passed, and all six retained example suites passed. The final build used unchanged checked artifacts for retained modules; it is not described as a clean rebuild of every dependency. The source/provenance audit passed for 107 checked source files and the exact pinned vendor closure. A scan of 1,530 project/vendor Lean sources found no admitted-proof, extra-axiom, or native-evaluation markers.

The origin-based transitive axiom audit passed for **1,386 project declarations and 25,819 imported FLT declarations**, allowing only `propext`, `Classical.choice`, and `Quot.sound`. This includes the new descent, group-law and cotangent proofs. It does not certify the unproved Cartier identity or either geometric classification criterion.

Exact run details and log hashes are in `verification/checkpoint-14-run.json` (completed 2026-09-19T20:02:47.532629+00:00).

All 58 checkpoint-13 proof modules are byte-for-byte unchanged. This checkpoint adds three proof modules and 32 public supporting theorem declarations, for 61 modules and 472 public declarations, plus nine private supporting lemmas. These are declaration counts, not independent discoveries or completed classification theorems.

The project imports 35 additional source modules from the same pinned FLT commit, bringing the vendor total to 1468. Of these, 1461 are unchanged upstream bytes and seven have documented compatibility ports. The one new port changes a `List.TFAE.out` index to the current one-based convention and leaves the mathematical statement unchanged. The 1433 previously retained vendor sources are unchanged.

## Provenance and reproducibility

Lean remains pinned to `leanprover/lean4:v4.34.0-rc2`, Mathlib to `85e3a25e006c35636f0e53b0e9296caca2685bc0`, and FLT to `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`. No proof-checking behavior has been altered. Original licenses and notices are retained.

`provenance/frobenius-verschiebung.json` records new sources, imported proofs, and the inspected descent proof route. `provenance/mini-checkpoint-13.json` preserves hashes of all prior proof modules. The vendor manifest records the exact import closure, SHA-256 hashes and upstream Git blob hashes; missing entries from the earlier truncated upstream index were checked against the pinned GitHub contents API.

From the extracted source directory:

```sh
lake exe cache get
bash verification/verify.sh
```

The source archive includes the code, retained vendored sources, reports, coverage ledger, provenance, and verification logs. The optional compiled cache excludes compiler binaries and external Mathlib/package caches; its instructions are in `verification/BUILD_CACHE.md`.
