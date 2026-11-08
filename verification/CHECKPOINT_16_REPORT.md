# Checkpoint 16: actual Frobenius Picard pullback equals Verschiebung

19 September 2026 · Lean 4.34.0-rc2

**This checkpoint closes the missing equality of the two actual Jacobian maps. It does not complete the Cartier comparison or the general genus-two geometric criteria.** All 66 proof modules from checkpoint 15 are preserved unchanged.

## What is newly proved

For an actual invertible sheaf L on any scheme X with p = 0 in its structure sheaf, p prime, the code constructs an isomorphism

\[
F_X^*L \;\cong\; L^{\otimes p}.
\]

The isomorphism sends a pulled-back local section s to its p-th tensor power. Additivity is proved in local frames using the characteristic-p power identity and then by sheaf separation. The map is constructed with the actual Frobenius scalar action through pullback/pushforward adjunction. The tensor power of a frame is a frame, which proves local surjectivity and hence invertibility of the map. No trivialization of the entire line bundle is assumed. The proof also permits characteristic two and nonreduced schemes.

The second module applies this result to the actual universal Poincare bundle. Relative Frobenius on both the curve and its representing Picard scheme, followed by projection from their twists, is proved to be absolute Frobenius on their fibre product. Thus the composite Picard map classifies the p-th tensor power. Uniqueness in the Picard universal property proves

\[
J \xrightarrow{F_J} J^{(p)} \xrightarrow{F_C^*} J
\quad = \quad [p]_J.
\]

This factorization holds over any characteristic-p field when the actual pointed curve and representing Picard scheme are given. Over a perfect field, the independently descended Verschiebung from checkpoint 15 is characterized by this same factorization. Therefore Lean proves equality of actual scheme morphisms

\[
F_C^* = V_J : J^{(p)} \longrightarrow J.
\]

The two independently constructed local-ring cotangent differentials are consequently equal as K-linear maps

\[
\operatorname{Cot}_0(J) \longrightarrow \operatorname{Cot}_0(J^{(p)}).
\]

The source and target twists are retained. V has not been redefined using curve Frobenius or Cartier, and no desired comparison is a hypothesis.

## Status of the requested work

| Requested item | Current status |
|---|---|
| Identify curve-Frobenius Picard pullback with independently constructed Jacobian V | **Proved in this checkpoint**, for a given genuine representing Jacobian over a perfect characteristic-p field. |
| Equality of the separately constructed cotangent actions of those maps | **Proved in this checkpoint.** |
| Identify this cotangent action with the curve's Cartier operator | **Still open.** The canonical comparison with global curve differentials, its correct scalar twist, and compatibility with Cartier remain to be proved. |
| General genus-two Cartier zero iff geometric superspeciality | **Still open.** The converse must produce an actual product isomorphism; it is not supplied by the matrix calculation or the new map equality alone. |
| General genus-two Cartier square zero iff geometric supersingularity | **Still open.** The existing implication to geometric p-rank zero is retained; the geometric product-isogeny classification and converse remain missing. |

## Match to the sheet and IKO §1

| Sheet / IKO item | What is available | Remaining scope |
|---|---|---|
| Elliptic curves over finite/perfect fields; supersingular definition | Actual Weierstrass curves, geometric p-torsion definition, odd-characteristic Hasse criterion and base-extension invariance. | Further elliptic characterizations and comparison of the separate implementations. |
| Legendre family | Ellipticity, Deuring/Hasse criterion, separability and examples. | Retained unchanged. |
| Superspecial and supersingular curves | Independent geometric predicates using Jacobian product isomorphisms and isogenies; superspecial implies supersingular. Family superspeciality imposes the calculated Cartier/root condition. | General Cartier equivalences and converse geometric constructions. |
| Boxed Newton polygon | Definitions for coefficient hulls and finite-field Witt F-isocrystals, isomorphism invariance and a true half-slope example. | Attach the actual curve/Jacobian isocrystal and prove the geometric comparison. |
| Boxed §1 matrix on dx/y and x dx/y; IKO (1.1)–(1.5) | Full global/regular bases and actual Cartier matrices for every presented separable quintic/sextic model. The actual Picard Frobenius/V identity and equality of cotangent actions are now proved. | Compare these cotangent actions with curve Cartier; present every abstract genus-two curve by the current equations. |
| IKO Lemma 1.1 | General matrix/operator zero and square-zero equivalences, square-zero implies actual Jacobian p-rank zero; stronger p-rank equivalences for the two explicit families. | General geometric superspeciality/supersingularity equivalences. |
| IKO families and parameter polynomials | Actual curves/Jacobians, Cartier formulas, p-torsion counts, p-ranks, ordinary loci, necessary superspecial conditions and parameter bounds. | Geometric converses, elliptic quotients and isomorphism/automorphism classifications. |
| IKO Proposition 1.14 | Separability by the main differential-equation argument; all four equations (1.34), endpoint exclusions, degrees and distinct root counts. | Retained unchanged. The gamma-function presentation is replaced by an algebraic coefficient recurrence. |

`SECTION1_COVERAGE.md` contains the complete proposition-by-proposition ledger, including the remaining material in IKO §1. No separate “Oort conjecture” beyond the chosen paper's precise results has been fixed or proved. This checkpoint is not completion of IKO §1 or a proof that the entire planned preprint is ready.

## New source and attribution

Both new modules are under `SupersingularCurves/Geometry/`:

- `FrobeniusLineBundle.lean`: the actual sheaf Frobenius/tensor-power isomorphism and local-section formula.
- `FrobeniusPicardComparison.lean`: simultaneous product Frobenius, Poincare-bundle comparison, actual Picard factorization, equality with independent V, and equality of cotangent differentials.

There are now **68 proof modules and 525 public theorem declarations**, plus the retained nine private supporting lemmas. This checkpoint adds 11 public theorem declarations and the actual isomorphism constructions in two modules. Declaration counts include supporting results; they do not count independent mathematical discoveries.

The proofs reuse six newly imported, unchanged modules from the same pinned FLT revision: the scalar formula for powers of tensor sections, preservation of frames under tensor powers, and the Picard tensor-power formula, together with their proof modules. Previously imported results provide local frames, invertibility from local surjectivity, Picard representability/base change, and independently descended V. The new local characteristic-p argument and Poincare comparison are written in this project.

All **1,496 checkpoint-15 vendor modules** are unchanged. The new total is **1,502**, comprising 1,495 exact upstream files and the same seven previously documented compatibility ports. There are no new compatibility ports. Provenance is recorded in `provenance/frobenius-picard-comparison.json` and `provenance/mini-checkpoint-15.json`.

## Verification

**All verification gates passed.** Both new proof modules compiled, the full project build succeeded, and all six retained example suites passed. The final build reused unchanged checked artifacts for retained modules; it was not a clean rebuild of every dependency. The provenance audit checked 119 current source hashes, upstream Git blobs, exact import closure, and preservation of all prior proof modules. A comment-stripped scan of **1,571 project/vendor Lean sources** found no admitted-proof, added-axiom or native-evaluation markers. The scanner is included and runs from the verification script.

The origin-based transitive axiom audit passed for **1,569 project declarations and 26,817 imported FLT declarations**, allowing only `propext`, `Classical.choice`, and `Quot.sound`. This includes the actual line-bundle isomorphism, Poincare comparison, map equality and cotangent equality. It does not certify the explicitly unproved Cartier identity or geometric classifications.

Execution details and log hashes are in `verification/checkpoint-16-run.json` (completed 2026-09-19T22:05:30.332452+00:00).

The pinned versions remain Lean `leanprover/lean4:v4.34.0-rc2`, Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`, and FLT `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`. The proof checker is unmodified. Original licenses and notices are included.

From the extracted source directory:

```sh
lake exe cache get
bash verification/verify.sh
```

The ZIP contains proof sources, the selected dependency sources, the coverage ledger, provenance and verification logs. The optional compiled cache excludes the compiler and external dependency caches; see `verification/BUILD_CACHE.md`.
