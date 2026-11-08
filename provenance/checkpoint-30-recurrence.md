# Checkpoint 30: actual isogeny recurrence and integral compactness

The four new project modules are original proofs against the pinned Mathlib
and retained project interfaces. No vendor proofs, definitions of geometric
supersingularity, or historical project proof modules were changed.

## What the new proof constructs

Fix an actual abelian variety X over an algebraically closed field, a prime
ell different from the characteristic, and a nonzero rational subspace W of
its actual rational Tate module. Let U be the inverse image of W in the
actual integral Tate module. The existing prescribed-lattice theorem supplies
actual finite-subgroup quotients D_n and maps f_n : D_n -> X whose integral
Tate images are U + ell^n T(X).

Assume the D_n range over finitely many actual group-scheme isomorphism
classes. Infinite pigeonhole and an increasing enumeration give one actual
domain B along indices a(n). Transport f_n along these isomorphisms. One
quotient and its multiplication factor give q : X -> B and f_0 : B -> X
with f_0 followed by q equal to multiplication by a nonzero integer m.

Compose q with each f_n to obtain actual integral endomorphisms F_n of X.
Choose a nonzero integral w in W by clearing denominators. Since w is in
every prescribed image, choose z_n in T(B) with f_n(z_n)=w, and set
y_n=f_0(z_n). Then F_n(y_n)=m*w, a fixed nonzero rational Tate vector.

Integral matrices, integral y_n, and integral column errors form a compact
product of p-adic integer spaces. Take a convergent subsequence. Powers
ell^a(n) tend to zero; the limit therefore has image in W. Evaluation at the
convergent y_n shows that the limit is nonzero. The scalar span of actual
endomorphisms is a finite-dimensional rational subspace and is closed, so
the limit remains in `actualEndSpan`. No unproved finite-generation result
for an integral Hom group and no supplied operator-norm bounds are used.

For X=A times E^2 and W the graph of a rational Tate equivalence, the retained
graph extraction produces an actual nonzero elliptic map. The checkpoint-29
subgroup construction and checkpoint-28 complement theorem then produce
supersingular elliptic-product isogenies in both directions when A has
p-rank zero.

## Exact remaining input

`PrescribedLatticeQuotients.HasFiniteModels` is an explicit hypothesis, not
a theorem from zero dV. It says that one finite set of actual abelian
varieties represents all quotient domains by actual group-scheme
isomorphisms. It is not a list of formal labels or assumed elliptic factors.

The current proposed route to this input needs uniformly bounded projective
embeddings for the nonprincipal quotient-root polarizations, together with
the numerical bounds and finite-field descent/moduli assembly. The imported
closed-immersion theorem with `KernelTrivial` applies to a principal
polarization. Finite polarization kernel does not imply that hypothesis.
The general finite-by-sections theorem supplies a finite projective map;
it does not alone supply a projective closed immersion of bounded degree.

The general very-ampleness theorem for powers of ample bundles on abelian
varieties was not formalized here. The pinned source investigation did not
produce a usable general replacement for the principal-polarization
interface. None of these gaps is discharged by changing definitions or by
an assumption named as a classification result.

Zero-dV preservation across these prime-to-characteristic quotient maps
was already proved in `VerschiebungPrimeToCharacteristicIsogeny.lean`.
An initially duplicated proof was removed; it is not counted as new work.

The global zero-dV elliptic-map theorem, full product-isogeny classification,
Oort integral splitting, both positive Cartier converses, and Block 1 remain
open in the project.
