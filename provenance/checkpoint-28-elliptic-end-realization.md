# Actual elliptic endomorphism realization: scope and remaining p-saturation

## Current checkpoint boundary

The later `EllipticTorsionLiftingEndLocalLifting.lean` now compiles: for the
chosen supersingular elliptic model after field extension, a Frobenius-kernel
endomorphism which extends to actual p-torsion is lifted to an actual global
endomorphism. The supporting restriction and base-change action modules also
compile. This does not supply arbitrary-factor transfer or Oort's quotient
induction. The historical development notes below describe earlier stages;
current verification is recorded in `verification/CHECKPOINT_28_REPORT.md`.

## Historical development notes

## Implemented statements (validation tracked separately)

`EllipticTorsionLiftingEndRealization.exists_faithful_action` constructs, from the canonical Weierstrass group/evaluation data, a faithful action of rational elliptic endomorphisms by actual scheme maps. It preserves the group law on every test scheme, zero, identity, addition, composition, and multiplication by each natural number.

`exists_rankFour_scheme_lattice` combines that action with the pinned rank-four rational-endomorphism theorem for a supersingular elliptic curve over an algebraically closed field algebraic over F_p. It constructs an injective additive family indexed by Z^4 of genuine scheme maps preserving all test-scheme group laws.

`WeierstrassGroupModel.groupEndOfMul` bundles such a map as an actual internal group morphism of the separately constructed projective Weierstrass abelian variety. `exists_faithful_rankFour_group_lattice` realizes the preceding Z^4 family in the actual `Grp (Over (Spec K))` endomorphism type, retaining injectivity and the actual scheme addition identity.

The Weierstrass group model and its chart-compatible evaluation are constructed in `ClassificationSurfaceEllipticExistence`, not assumed realizations or arbitrary point groups. No rank statement about the entire actual-scheme endomorphism group is asserted here.

## Exact missing arithmetic input to the p^4 torsion count

The actual full-torsion restriction kernel from checkpoint 27 consists of actual scheme homomorphisms divisible by [p]. To deduce that the rational rank-four lattice has p^4 distinct restrictions, one still needs:

If the actual scheme realization of rational alpha vanishes on the entire E[p] scheme, then alpha is in p times the rational endomorphism lattice.

Injectivity of the global realization alone does not prove this: the divided actual group map must either be shown to lie in the rational lattice, or the divisibility of alpha must be deduced directly.

A focused alternative to reverse rationality uses the existing quaternion maximal-order theorem
`QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_two_le_padicValRat_nrd`:
at the ramified prime p, reduced norm valuation at least two implies membership in p times the maximal order. Actual factorization through [p] makes the actual isogeny degree divisible by p^2. The remaining comparison is degree(realization(alpha)) = reduced norm(alpha). A possible proof compares the actual quadratic degree polynomial with the rational/quaternion polynomial using sizes of point kernels of etale shifts.

Another possible route is the integer quadratic characteristic polynomial of the divided actual elliptic endomorphism. It would make the trace and norm of alpha divisible by p and p^2, permitting direct use of
`WeierstrassCurve.exists_eq_char_smul_of_sq_sub_smul_add_smul_eq_zero_rationalEndSubring`.

A statement-level scan of every pinned theorem mentioning `IsRationallyRepresented` and schemes found only the rational-to-scheme construction; no converse actual-scheme-to-rational-representation theorem was found.

These developments do not prove Oort Lemma 5, do not construct an initial elliptic-product isogeny into an arbitrary zero-dV surface, and do not establish Block 1 geometric classification.

## Definite quaternion residue route (checkpoint28 extension)

`EllipticTorsionLiftingEndResidue.lean` is now production-compiled (8801 jobs),
with `leftIdeal_trichotomy` and `UnramTheta.exists_irreducible_element` audited
using only `propext`, `Classical.choice`, and `Quot.sound`.

This supplies an actual element of any maximal definite quaternion order
ramified at p whose integral reduced characteristic polynomial is irreducible
modulo p. The finite quotient argument is adapted from pinned FLT's analogous
indefinite-order proof; its actual local division input here is the pinned
proved definite-order norm-valuation divisibility theorem. The copied argument
was generalized to the definite case in a new project source, not installed as
a vendor compatibility port.

The companion `EllipticTorsionLiftingEndScalarImage.lean` has production-compiled
and passed the standard-three-axiom audit. It identifies the image of any characteristic-p scalar ring action of the
supersingular rational endomorphism order with the p²-Frobenius-fixed scalars.
This route supplies the required derivative image without needing to identify
all actual scheme End with the rational endomorphism order or prove that its
rank-four lattice is p-saturated.

The geometric scalar ring action itself uses the actual cotangent differential
and has now been constructed and production-compiled. Even after the image theorem, arbitrary
local torsion morphisms still need the F/V scalar constraint and the faithful
cotangent comparison. Algebraicity over Fp is presently required of the source
field for the pinned rational-endomorphism quaternion-order identification;
the target scalar field may be any characteristic-p field. The complete scalar action has now been pulled back to arbitrary extension
fields and differentiated there, as detailed below. Supersingularity of the
chosen actual model after arbitrary extension remains a separate comparison
needed by the classification assembly. The initial global elliptic product isogeny into an
arbitrary zero-dV surface also remains separate.

The adapted finite-order proof sources are the pinned
`S_QuaternionAlgebra_IsMaximalOrder_leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq.lean`
and
`S_QuaternionAlgebra_IsMaximalOrder_exists_mem_trd_eq_nrd_eq_forall_sq_sub_mul_add_ne_zero_of_isIndefiniteRamifiedExactlyAt.lean`.
Their local ramification input was replaced by the proved definite norm
criterion, including the positive-definite norm-zero case. No claim that the
indefinite theorem itself applies to a definite algebra is used.

## Field-extension action strategy

The source `EllipticTorsionLiftingEndBaseChangeAction.lean` pulls back the
entire actual rational-endomorphism action to the chosen field extension,
proves its zero/identity/addition/composition laws using the monoidal pullback
functor, and differentiates that **target** action. This bypasses a comparison
between the source and target differentials: the arithmetic exact-image
result applies to any scalar ring map from the fixed source order to the
target field. The source model may therefore be chosen over Fpbar, while the
target field is arbitrary. These action/fullness modules have production-compiled successfully (11048
jobs, exit 0), and all eight declarations in the combined audit use only
`propext`, `Classical.choice`, and `Quot.sound`. Logs:
`end-cotangent-image28-build.log`, `end-full-scalar28-audit.log`.

The final theorem
`WeierstrassGroupModel.exists_baseChanged_endomorphism_of_frobenius_scalar`
constructs, for each scalar c in an arbitrary extension field with c^(p²)=c,
a genuine group endomorphism of the actual basechanged elliptic abelian
variety whose pointed cotangent differential is c times the identity.
It assumes neither a supplied lifting nor surjectivity of a scalar action.
The source curve is algebraically closed and algebraic over Fp, as required
by the pinned quaternion-order theorem; the target field need not be
algebraic over Fp.

This closes the global scalar-image half of the Frobenius-kernel restriction
lifting argument. The local F/V upper bound, actual Hopf restriction of the
constructed endomorphism, and faithful cotangent comparison must still be
assembled before claiming a local restriction lifting theorem. The initial
global product-isogeny input for an arbitrary dV=0 surface remains separate.
