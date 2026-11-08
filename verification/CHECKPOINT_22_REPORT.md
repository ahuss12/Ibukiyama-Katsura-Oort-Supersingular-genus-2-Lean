# Checkpoint 22 — geometric isogeny consequences

**Block 1 is not finished.** The new result is the genuine geometric-to-Cartier direction of the supersingularity criterion. The reverse classification and the general superspecial criterion remain unproved.

## Mathematical result

For an actual representing Jacobian over an algebraically closed field of characteristic p, with function field finite over K(x) for a transcendental x, multiplication by p is surjective on its actual point group. The proof transfers the pinned characteristic-p divisibility theorem for the actual degree-zero Picard group through the existing independently constructed `J.picardPoints` correspondence. The correspondence supplies the conclusion for the given Jacobian and base point.

A finite morphism of actual group schemes whose source is locally of finite type has a finite kernel on geometric points; actual abelian varieties satisfy this hypothesis. If its target has trivial p-torsion and its source is p-divisible, the source p-primary subgroup is both finite and p-divisible, so its p-torsion is trivial. An actual geometric isogeny is composed with the injective point map to the algebraic closure; its finite point kernel pulls back to a finite kernel on the original Jacobian points. This proves:

- With the finite-over-K(x) witness, geometric supersingularity of a representing Jacobian implies trivial p-torsion, without a genus restriction; the base field here is algebraically closed.
- Over an algebraically closed field, it implies the independently defined p-rank-zero condition.
- For any presented separable quintic/sextic over an algebraically closed field of odd characteristic, geometric supersingularity implies Cartier square zero on all regular and scheme-global forms, and the correctly ordered twisted matrix equation M^(p)M = 0.
- Both IKO families have the necessary geometric supersingular parameter-root condition. Their special matrices then give Cartier zero. In characteristic three, no admissible family-B curve is geometrically supersingular.

The generic helper uses the standard witness that the function field is finite over K(x) for a transcendental x. Every final quintic/sextic and IKO-family theorem supplies this witness from its existing quadratic-field construction. The curve-level implication covers every representing Jacobian and every base point through the existing Picard point correspondence. The characteristic-p divisibility import applies to n=p; it does not assume that n is invertible in K.

## Exact remaining block

| Required genus-two direction | Status |
|---|---|
| Geometrically supersingular ⇒ Cartier square zero | Proved for all presented separable quintic/sextic models under the stated hypotheses. |
| Cartier square zero ⇒ geometrically supersingular | Unproved: no actual product isogeny is constructed from p-rank zero. |
| Geometrically superspecial ⇒ Cartier zero | Proved for the two IKO families; unproved generally. |
| Cartier zero ⇒ geometrically superspecial | Unproved: no actual product isomorphism is constructed. |

The superspecial bridge needs a geometric identification involving the actual Verschiebung differential and Oort's product theorem. The supersingular converse needs classification attached to the actual abelian variety. A contemporary primary account states Oort's a-number/product result as Theorem 22 and the slope/isogeny result as Proposition 26; its proofs depend on substantial Dieudonné and arithmetic geometry. These are mathematical sources, not assumed Lean theorems. [Chia-Fu Yu, §4](https://arxiv.org/html/2603.11506v1#S4)

The general hyperelliptic presentation theorem for every abstract genus-two curve also remains outside the proved model scope. The characteristic-three curve y²=x⁵−1 still has proved p-rank zero and nonzero square-zero Cartier, but its geometric supersingular/non-superspecial classification is not claimed.

## Dependency evidence

The earlier upstream recursive filename index was truncated. This turn recovered nontruncated Definitions, Theorems, and P2M directory trees and inspected 43 relevant definitions and 161 theorem statements by content. No usable actual genus-two product-classification theorem was identified. The precise search scope, tree identities, inspected source hashes, and limitations are recorded in `provenance/geometric-classification-source-inspection.json`; this is not a claim of exhaustive absence from every source body.

The characteristic-p Picard divisibility theorem and its missing import closure were obtained from the existing pinned upstream commit. Old proof modules, geometric definitions, and old vendored Lean sources are preserved byte for byte.

## Verification

All current checks passed on Lean 4.34.0-rc2, with the existing pinned Mathlib revision:

- Full aggregate build: 10,467 Lake jobs; all five new project modules compiled during this continuation.
- Selected upstream dependency build: 73 added modules; 72 exact copies and one documented List.TFAE.out indexing compatibility port. All 1,527 previous vendor modules remain unchanged.
- Transitive axiom audit: 573 declaration entries across all five new project modules and all 73 added vendor modules, including private/generated entries and stored types and bodies. Only propext, Classical.choice, and Quot.sound occur.
- One concrete integration example proves that family B at parameter 2 over the algebraic closure of F3 is not geometrically supersingular.
- Source integrity: all 97 previous proof modules and 1,528 previous vendor Lean files (including the vendor build file) preserved; 190 current source hashes checked; 1,703 Lean proof/vendor sources scanned with no proof-admission or native-evaluation markers.

The current project has 102 proof modules, 726 public theorem declarations and 13 private supporting lemmas. These are inventory counts, not completion percentages. Existing checked dependency artifacts were reused; this is not a clean recompilation of every retained source. Historical integration suites and audits were retained for byte-identical old sources rather than rerun.

Exact results and log hashes are in `verification/checkpoint-22-run.json`. Reproduce the focused checks with `bash verification/verify_checkpoint22.sh`.
