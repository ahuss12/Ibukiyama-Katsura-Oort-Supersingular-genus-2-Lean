# Checkpoint 23 — ordinary criterion and geometric naturality

The next proof steps are implemented and verified. **Block 1 is still incomplete:** the reverse supersingular classification and the general superspecial equivalence have not been proved.

## New mathematical results

For every separable quintic or sextic over an algebraically closed field of odd prime characteristic, and for any actual representing Jacobian and base point, Lean now proves:

**Jacobian ordinary ⇔ geometric p-rank two ⇔ coefficient determinant nonzero ⇔ global Cartier bijective ⇔ actual Verschiebung cotangent map bijective.**

The proof counts actual geometric p-torsion through the existing Picard correspondence and logarithmic Cartier equivalence. A new arbitrary two-by-two fixed-vector theorem uses polynomial elimination and separability to prove that the count is p² exactly when the determinant is nonzero. Ordinarity retains its independently defined p-rank meaning. This completes IKO Lemma 1.1(iii) for these presented models; the theorem presenting every abstract genus-two curve in this form remains open.

For the actual genus-two model y² = x⁵ − 1, all odd primes p ≠ 5 are now covered:

| p mod 5 | Cartier on all global forms | Actual Jacobian |
|---|---|---|
| 1 | Bijective | Ordinary, p-rank two |
| 2 or 3 | Nonzero, square zero | p-rank zero |
| 4 | Zero | p-rank zero |

These are uniform proofs, not extrapolations from small primes. They establish the operator, p-rank and ordinary congruence calculations for the explicit model. They do not establish its identification with automorphism class (6), or the geometric supersingular/superspecial conclusions of IKO Proposition 1.13.

The new naturality module proves actual Verschiebung naturality under morphisms between smooth commutative group schemes over a fixed perfect field, its cotangent naturality square, vanishing transport through genuine isomorphisms, and vanishing on actual finite products when each factor vanishes. It also proves compatibility with the existing Jacobian Verschiebung cotangent map. These constructions retain the actual Frobenius twist and the independent geometric definitions.

## Remaining geometric classification

| Required direction | Current status |
|---|---|
| Geometrically supersingular ⇒ Cartier square zero | Already proved for every presented separable quintic/sextic under the stated hypotheses. |
| Cartier square zero ⇒ geometrically supersingular | Missing the actual product-isogeny classification. |
| Geometrically superspecial ⇒ Cartier zero | Proved for both IKO families. Generally, fixed-base product/isomorphism transport is now proved, but supersingular elliptic-factor vanishing and algebraic-closure base-change/descent remain. |
| Cartier zero ⇒ geometrically superspecial | Missing the actual product-isomorphism classification. |

Product smoothness and commutativity hypotheses in the generic product-vanishing theorem must be instantiated in the eventual geometric application. No missing classification conclusion has been introduced as an axiom or hypothesis.

Other unfinished work is unchanged: the abstract genus-two presentation, scheme-projection interpretation of the cohomological scalar untwist, attachment of an actual crystalline/Dieudonné object to the Jacobians and the Newton comparison, remaining IKO §1 automorphism/quotient/isomorphism classifications, and the sheet's cyclic-cover identifications. The Newton infrastructure already exists, but the geometric attachment is a substantial remaining proof.

## Verification

All current checks passed on pinned Lean 4.34.0-rc2 and Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`:

- Full aggregate build: 10,475 Lake jobs; all eight new proof modules compiled.
- Transitive axiom audit: all 172 declaration entries from the eight new modules, including private/generated entries and stored types/bodies. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
- Seven concrete integration examples: invertible and singular non-diagonal matrices; Cartier distinctions in characteristics 3 and 7; Cartier vanishing in characteristic 19; actual ordinarity and Verschiebung cotangent bijectivity in characteristic 11.
- All 102 previous proof modules and 1,601 previous vendor Lean files are byte-identical. No vendor additions or new compatibility ports.
- 203 current source hashes checked; 1,711 project/vendor Lean sources scanned without proof-admission or native-evaluation markers.

The inventory is now **110 proof modules, 797 public theorem declarations and 19 private supporting lemmas**: additions of eight modules, 71 public theorems and six private lemmas. Counts measure inventory, not completion percentages.

The exact pinned runtime and package revisions were restored, and official compiled Mathlib cache artifacts were reused alongside unchanged checked project/vendor artifacts. This is not a clean rebuild of every retained dependency. Historical example suites and audits were retained for byte-identical sources rather than rerun.

Reproduce the focused verification with `bash verification/verify_checkpoint23.sh`. Exact results, runtime provenance and log hashes are in `verification/checkpoint-23-run.json`; the full sheet/section ledger is `SECTION1_COVERAGE.md`.
