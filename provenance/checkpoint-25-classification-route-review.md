# Superspecial converse: two concrete proof routes reviewed

The pending target is an actual group-scheme isomorphism from the independently
constructed genus-two Jacobian to a product of supersingular elliptic curves,
assuming its actual Cartier operator vanishes. Frobenius factorization and a
residual degree-one isomorphism alone do not construct an elliptic factor.

## General arithmetic route

Primary source: Chia-Fu Yu, *Introduction to Dieudonné modules and supersingular
abelian varieties revisited*, §4, https://arxiv.org/html/2603.11506v1.
Theorem 22 gives the desired product decomposition from maximal a-number. Its
proof uses the following bridges: identify the actual p-divisible group with the
standard superspecial one; obtain a finite-field model through the rigidity of
the maximal-a-number moduli locus (Lemmas 24–25); realize an actual isogeny using
Tate's theorem; classify integral realizations using the adelic description and
strong approximation (Lemma 27 and Proposition 29). These are further geometric
and arithmetic proofs, not consequences of equality of Frobenius and
Verschiebung degrees. No application of this unformalized theorem was added.

## Constructive surface route

Primary source: Mickaël Montessinos, *Equivalent computational problems for
superspecial abelian surfaces*, §5, https://arxiv.org/html/2601.18050v1.
Lemma 5.1 starts with an actual (2,2)-isogeny from a product. Suitable elliptic
homomorphisms define triangular product automorphisms moving its kernel to a
product kernel. Elliptic quotients then yield a product, and equality of degrees
makes the induced map an isomorphism. The construction requires an initial
product isogeny, appropriate odd-degree elliptic isogenies, and realization of
specified two-torsion maps by elliptic endomorphisms. The complete algorithm
starts from an IKO polarization matrix and an isogeny chain from a fixed
supersingular elliptic square. These inputs have not been constructed from
Cartier vanishing. Its computational hypotheses were not inserted into the Lean
target. This gives a concrete alternative route, not a completed converse.

## Verified boundary case

`SupersingularCurves/Hyperelliptic/CharacteristicThreeObstruction.lean` proves
that every separable quintic or sextic in characteristic three has nonzero
Cartier matrix. For quintics, the matrix contains the nonzero leading
coefficient. For sextics, a zero matrix forces derivative zero, contradicting
separability and positive degree. Existing Cartier identification and the
geometric forward implication then prove nonzero regular/global Cartier and
non-superspeciality for every representing Jacobian. This is a boundary-case
obstruction, not a substitute for the requested general converse.
