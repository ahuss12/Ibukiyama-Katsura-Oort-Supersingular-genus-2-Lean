# Checkpoint 24 — geometric superspeciality implies Cartier vanishing

**The requested full Block 1 is not finished.** This checkpoint proves the general geometric-to-Cartier superspecial implication. Both reverse product-classification theorems remain unproved.

## Proved in Lean

Over an algebraically closed field, an abelian variety that is geometrically isomorphic to a product of supersingular elliptic curves has zero actual Verschiebung cotangent map, in every dimension. For any representing Jacobian and base point of a presented separable quintic/sextic in odd characteristic, this gives **geometric superspeciality ⇒ Cartier zero on all regular/global differentials ⇒ coefficient matrix zero**. Superspeciality keeps its independent product-isomorphism definition.

The proof derives elliptic Verschiebung vanishing from the original geometric p-torsion definition. It constructs and analyzes the actual finite kernel: a nonzero differential in dimension one would force this kernel to be a single reduced point, contradicting degree p. Product smoothness/commutativity and transport from algebraic closure to an already algebraically closed ground field are supplied. The actual Jacobian operator is compared with this group-scheme operator; its existing Cartier comparison then applies.

The supporting degree theorems concern actual scheme morphisms: multiplication by nonzero n is finite, flat and surjective with degree n^(2g), and relative Frobenius and Verschiebung each have degree p^g. No restriction excluding n=p is introduced.

For the actual model y² = x⁵ − 1, all odd p ≠ 5 retain their uniform operator/p-rank criteria:

| p modulo 5 | Full-space Cartier | Actual geometric conclusions |
|---|---|---|
| 1 | Bijective | Ordinary |
| 2 or 3 | Nonzero, square zero | P-rank zero; now proved not superspecial |
| 4 | Zero | P-rank zero; positive geometric superspeciality still unproved |

Positive geometric supersingularity in residue classes 2, 3, 4 remains unproved, as does identification of all IKO Class-(6) curves with this explicit model. Proposition 1.13 remains partial.

## Work toward the converses

Over a perfect characteristic-p field, Lean now proves that the kernel of the universal differential in any normal domain is exactly the set of pth powers. This yields a unique affine Frobenius factorization. Stalk roots glue to section roots, and a global sheaf construction gives an actual unique morphism from the relative Frobenius twist. Smooth normal stalks supply the roots when the universal differential of every pulled-back germ vanishes.

These global results retain that differential hypothesis. The passage from zero identity cotangent map of actual Verschiebung to those stalk differential equations remains unproved. Even completing that passage would not itself construct an elliptic-product isomorphism.

| Required geometric direction | Status |
|---|---|
| Supersingular ⇒ Cartier square zero | Previously proved for the presented genus-two models. |
| Cartier square zero ⇒ supersingular | Unproved: needs an actual elliptic-product isogeny. |
| Superspecial ⇒ Cartier zero | Now proved generally for the presented genus-two models. |
| Cartier zero ⇒ superspecial | Unproved: needs an actual elliptic-product isomorphism. |

The classical product-isomorphism result needed on the reverse route is Oort's maximal-a-number theorem. Yu's [exposition, §4, Theorem 22 and its proof](https://arxiv.org/html/2603.11506v1#S4) derives it through integral p-divisible-group information and a global isomorphism theorem. Those conclusions are not consequences merely of the Frobenius degree identities. The source inspection is bounded evidence about available statements, not a proof that no formalization exists elsewhere. No classification conclusion has been introduced as an axiom or caller-supplied hypothesis.

The abstract genus-two presentation, full descent to arbitrary perfect fields, scheme-projection interpretation of the cohomological scalar untwist, actual crystalline Newton attachment and comparison, remaining IKO §1 classifications, and the sheet's cyclic-cover identifications also remain open. The full ledger is `SECTION1_COVERAGE.md`.

## Verification

All current checks passed on pinned Lean 4.34.0-rc2 and Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`:

- Full aggregate build: 10,834 Lake jobs; all 24 new project modules compiled.
- Transitive axiom audit: 5,086 declaration entries from all 24 new project modules and 335 new vendor modules, including private/generated entries and stored types/bodies. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
- Six concrete integration examples: geometric non-superspeciality in characteristics 3 and 7; square-zero Cartier together with actual non-superspeciality in characteristic 3; degrees 9, 9, and 81 for actual genus-two Frobenius, Verschiebung, and multiplication by 3.
- All 110 previous proof modules and 1,601 previous vendor Lean files are byte-identical.
- 335 pinned upstream modules added; 2 new compatibility ports documented. Current vendor total: 1935, of which 1925 have exact upstream bytes and 10 have documented ports.
- 236 current source hashes checked; 2,070 project/vendor Lean sources scanned without proof-admission or native-evaluation markers.

Inventory: **134 project proof modules, 891 public theorem declarations, 24 private supporting lemmas**. Additions: 24 modules, 94 public theorems, 5 private lemmas. Counts measure inventory, not completion percentages.

Unchanged checked project/vendor artifacts and the official pinned Mathlib cache were reused; this is not a clean rebuild of every retained dependency. Historical suites and audits were retained for byte-identical sources rather than rerun. Runtime restoration provenance is retained from checkpoint 23.

Reproduce the focused checks with `bash verification/verify_checkpoint24.sh`. Exact evidence and log hashes are in `verification/checkpoint-24-run.json`; source provenance is in `provenance/checkpoint-24-sources.json` and `provenance/checkpoint-24-degree-imports.json`.
