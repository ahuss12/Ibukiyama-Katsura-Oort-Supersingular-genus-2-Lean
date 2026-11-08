# Remaining work after checkpoint 26

Block 1 is not complete. Superspecial and supersingular retain their independent geometric elliptic-product isomorphism and isogeny definitions.

The following constructions are now proved for the relevant actual abelian varieties and represented separable genus-two quintic/sextic models:

1. Zero actual dV is equivalent to an actual factorization through relative Frobenius with a residual group isomorphism A^(p²) ≅ A. This is equivalent to full-space Cartier zero for the represented curves.
2. The actual subgroup H = ker(F on A^(p)) ∩ ker(V_A) is a genuine group scheme. If C² = 0 and C ≠ 0, its scheme order is p. Actual invariant derivations and a local power basis prove the order statement.
3. The actual quotient Q = A^(p)/H is an abelian variety of the same dimension, with finite flat surjective quotient group morphism and the exact kernel H.
4. Actual F and V descend through Q. On the nonzero-Cartier p-rank-zero surface branch the quotient and both residual group isogenies have degree p. Their scheme factorization identities and the quotient's own twisted F/V diagram are proved.
5. The quotient and A have isomorphic rational-point groups, so all torsion groups and p-ranks agree.
6. Cartier squared zero implies zero actual differential for V^(p) followed by V, retaining both actual Frobenius twists. Actual Cech pullback and Picard comparisons supply the bridge.
7. The actual quotient has dV = 0 from nonzero square-zero Cartier, with all degree, kernel, rank and twist hypotheses proved. Combining both Cartier branches gives an actual isogeny from the original Jacobian to an actual abelian surface with zero dV from C² = 0 alone.
8. Any actual finite flat one-point group of order p has one-dimensional identity cotangent space. If dV = 0, the actual simultaneous subgroup instead equals the V-kernel and has order p^g.

The indispensable remaining classification theorem constructs an actual product of supersingular elliptic curves from dV = 0. The double Frobenius twist isomorphism, the quotient, and its local cotangent data do not themselves provide that product. A finite-field route also needs actual polarized descent and isogeny/endomorphism realization; the earlier bounded review is in `provenance/checkpoint-25-classification-route-review.md`.

| Required direction | Status |
|---|---|
| Geometric superspeciality ⇒ Cartier zero | Proved for every represented separable quintic/sextic in odd characteristic over an algebraically closed field. |
| Cartier zero ⇒ geometric superspeciality | Product-isomorphism construction still missing. |
| Geometric supersingularity ⇒ Cartier square zero | Proved for every such represented model. |
| Cartier square zero ⇒ geometric supersingularity | Product-isogeny construction still missing. |

The matrix square uses the Frobenius-twisted product corresponding to semilinear Cartier composition. General presentation of abstract genus-two curves and descent of the full results to arbitrary perfect fields remain separate work.

Outside this block, the actual crystalline/Dieudonne attachment and Newton comparison, the scheme-projection interpretation of the cohomological untwist, remaining IKO §1 automorphism/quotient/isomorphism and class-(4)/(5) results, and the sheet's cyclic-cover identifications remain unfinished. The Newton work currently defines and studies genuine isocrystal polygons but does not attach them to these actual Jacobians.

Read `SECTION1_COVERAGE.md` for the full ledger and `verification/CHECKPOINT_26_REPORT.md` for exact executed verification. Run `bash verification/verify_checkpoint26.sh` for focused checks. No geometric classification conclusion has been assumed as an axiom or caller-supplied hypothesis.
