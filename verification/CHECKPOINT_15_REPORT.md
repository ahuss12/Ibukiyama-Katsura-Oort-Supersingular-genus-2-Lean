# Checkpoint 15: Verschiebung over perfect fields and the actual Picard twist

19 September 2026 · Lean 4.34.0-rc2

**The perfect-field Verschiebung construction is now proved. The two requested geometric tasks remain incomplete.** This checkpoint also proves that the actual Frobenius twist of a representing Jacobian represents the twisted curve's Picard functor, with the compatible Poincare bundle and tensor-product group law. It constructs the true cotangent differential with the twist explicit.

## Status of the requested results

| Requested result | Status after this checkpoint |
|---|---|
| General genus-two Cartier zero iff geometric superspeciality | **Open.** Superspeciality retains the independent geometric product-isomorphism definition. The general equivalence is neither proved nor assumed. |
| General genus-two Cartier square zero iff geometric supersingularity | **Open.** The proved implication to actual Jacobian p-rank zero remains available. The geometric product-isogeny classification and converse remain missing. |
| Compare Cartier with the independently constructed Jacobian Verschiebung | **Partial, with two construction gaps closed.** V and its true cotangent action now exist over every perfect field of characteristic p. Its actual source is also proved to represent the twisted curve. Equality with curve-Frobenius Picard pullback and equality with Cartier remain unproved. |

## New verified mathematics

Let K be a perfect field of characteristic p, with p prime. For a smooth commutative group scheme X over K, the code constructs the actual fibre product X^(p) along the field Frobenius and its base-changed group law. Relative Frobenius F: X → X^(p) preserves this group law.

Multiplication by p coequalizes the fibres of F. Because F is finite faithfully flat, effective descent constructs a unique actual scheme morphism V: X^(p) → X. Lean proves both compositions:

- X → X^(p) → X is multiplication by p on X.
- X^(p) → X → X^(p) is multiplication by p on X^(p).

V respects the structure map, identity section, and multiplication on every test scheme. The multiplication proof descends equality along the faithfully flat product F × F. The coequalization lemma itself works over any field of characteristic p; perfection and smoothness enter the verified descent route.

For any given genuine representing Jacobian J, its group law comes from tensor product of actual line bundles. Applying the construction gives an independent V and the actual K-linear cotangent map

**V*: Cot(J) → Cot(J^(p)).**

Both cotangent spaces are maximal ideals modulo their squares in the actual local rings at zero. The differential is characterized by its action on every square-zero test scheme. The general pointed-scheme construction also satisfies identity, composition and uniqueness theorems. No Cartier operator or arbitrary dimension-based identification enters these definitions.

Finally, the relative Picard base-change theorem is applied with field Frobenius as the algebra map. It proves that the actual scheme J^(p) represents the twisted curve's algebraically trivial line bundles. The Poincare bundle is the base change of the original one, and its induced tensor-product group law equals the law already used in the V construction. Consequently actual curve-Frobenius Picard pullback and independently constructed V have the same source and target. Their cotangent differentials are constructed separately; **equality of those morphisms or differentials has not been proved**.

## New source modules

All paths are under `SupersingularCurves/Geometry/`.

| Module | Content |
|---|---|
| `FrobeniusTwistGroup.lean` | Actual fibre-product point equivalence; twisted group law and commutativity; relative Frobenius compatibility with identity, multiplication and n-multiplication. |
| `Verschiebung.lean` | General characteristic-p coequalization; perfect-field descent of V; both p-multiplication identities; uniqueness, base/identity/group compatibility; pointwise identities. |
| `PointedCotangent.lean` | Actual local cotangent spaces; natural square-zero point equivalence; contravariant differential, action, uniqueness, identity and composition. |
| `JacobianVerschiebung.lean` | Independent representing-Jacobian V over arbitrary perfect fields and arbitrary scheme universe; actual twisted cotangent differential. |
| `PicardFrobeniusTwist.lean` | Actual Picard representation on the twist, Poincare and group-law compatibility; curve-Frobenius Picard pullback on the same schemes as V, with its separately defined differential. |

All 61 checkpoint-14 proof modules are byte-for-byte unchanged. Five modules and 42 public supporting theorem declarations are added: **66 proof modules and 514 public declarations** in total, plus nine retained private supporting lemmas. These counts include supporting lemmas and specializations; they are not counts of independent new mathematical discoveries.

## What remains before the two requested tasks are complete

1. **Identify the two actual scheme maps.** Prove that curve-Frobenius Picard pullback equals independently descended V. The base-change/Picard source identification needed to state this on the same schemes is now available. The necessary line-bundle Frobenius/p-th tensor-power comparison remains missing.
2. **Prove the Cartier comparison.** Construct the canonical comparison between Jacobian cotangents and the curve's global regular differentials, with the correct scalar twist, and prove that V* becomes the already constructed Cartier operator. Equality of dimensions does not establish this.
3. **Prove the geometric classifications and converses.** Cartier zero must imply the required product isomorphism for superspeciality. In dimension two, the p-rank-zero information must yield the required product isogeny for supersingularity, with the appropriate reverse implications. Neither result follows just by renaming a matrix condition.

The broader sheet also still requires attaching a crystalline isocrystal/Newton polygon to the actual curves or Jacobians and proving its geometric comparison. The assertion that every abstract genus-two curve admits the current hyperelliptic presentation, and several automorphism, quotient and parameter-isomorphism results in IKO §1, remain open. `SECTION1_COVERAGE.md` gives the complete item-by-item ledger.

The existing Legendre results, IKO family polynomial/matrix calculations, global Cartier bases, geometric p-torsion and p-rank results, superspecial obstructions, and Newton-polygon/isocrystal definitions are retained. This checkpoint does not complete IKO Lemma 1.1 or the entire section. The geometric criteria are the results stated in [IKO §1.1, printed page 129](https://www.numdam.org/item/CM_1986__57_2_127_0.pdf).

## Proof attribution and verification

The coequalization proof is the general `RelVersch.comp_schemeNsmul_eq` lemma in the pinned upstream file `S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq.lean`. Despite that filename, the lemma used here has no fake-elliptic, quaternionic, level, genus, or algebraic-closedness assumption. Its full proof and import closure are retained unchanged. Picard representability and group-law base change reuse the corresponding pinned `RelPicard` theorems. Their specializations here use the actual field Frobenius.

There are 28 newly imported dependency modules from the same FLT commit, bringing the total to 1,496. Of these, 1,489 retain exact upstream bytes; the seven previously documented compatibility ports are unchanged. **No new compatibility port is introduced.** All 1,468 checkpoint-14 vendor sources are preserved. `provenance/perfect-field-verschiebung.json` records the exact additions, attribution and scope; `provenance/mini-checkpoint-14.json` records the prior proof hashes.

**All verification gates passed.** All five new proof modules compiled, the full project build succeeded, and all six retained example suites passed. The final build reused unchanged checked artifacts for retained modules; it was not a clean recompilation of every dependency. The provenance audit checked 114 current source hashes, upstream Git blobs, exact import closure, and all recorded prior-source preservation. A comment-stripped scan of 1,563 project/vendor Lean sources found no admitted-proof, added-axiom or native-evaluation markers.

The origin-based transitive axiom audit passed for **1,505 project declarations and 26,811 imported FLT declarations**, allowing only `propext`, `Classical.choice`, and `Quot.sound`. This verifies the supplied code, including the new descent and Picard-twist proofs; it does not certify any of the explicitly unproved comparisons or geometric classifications.

Exact execution details and log hashes are in `verification/checkpoint-15-run.json` (completed 2026-09-19T21:08:55.509656+00:00).

Lean is pinned to `leanprover/lean4:v4.34.0-rc2`, Mathlib to `85e3a25e006c35636f0e53b0e9296caca2685bc0`, and FLT to `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`. The proof checker is unmodified. Original upstream notices and licenses are preserved.

From the extracted source project:

```sh
lake exe cache get
bash verification/verify.sh
```

The source archive includes all proof sources, selected upstream sources, the coverage ledger, this report, provenance, and verification logs. The separate optional compiled cache excludes compiler binaries and external package caches; see `verification/BUILD_CACHE.md`.
