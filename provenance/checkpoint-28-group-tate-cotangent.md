# Checkpoint 28: group descent, genuine Tate modules, and cotangent comparisons

This records the work assigned to collaboration agent `group_descent28`. The Lean
files retain the project author header. The implementations use the existing
project definitions and pinned upstream proofs; this agent did not edit the
checkpoint-27 sources or the vendored proof archive. Other agents' contributions
are identified below. This is a record of checked intermediate results, not a
claim that the final geometric product classifier has been proved.

## Frozen, built modules

All paths below are relative to `SupersingularCurves/Geometry/`.

### 1. Effective descent of the actual abelian variety

- `FrobeniusFiniteFieldGroupDescentPoint.lean`
- `FrobeniusFiniteFieldGroupDescentLaw.lean`
- `FrobeniusFiniteFieldGroupDescent.lean`

These construct the descended identity section and actual group law over the
literal fixed field of Frobenius squared. Smoothness of the prescribed relative
dimension, properness, and geometric connectedness descend from the actual
pullback. The descended absolute Frobenius squared is multiplication by `p`.

The final theorem is
`AbelianVariety.exists_finiteField_abelian_model_of_verschiebungCotangent_eq_zero`.
Its input is an actual abelian variety with zero actual Verschiebung cotangent
map. Its conclusion includes an actual model over the fixed field, the field's
cardinality `p^2`, an actual pullback square, identity and multiplication
comparisons, and scalar Frobenius. A caller does not supply the final model,
identity section, group law, or equivariance.

This uses `descent_equivariance28`'s independently checked actual equivariant
scheme model. That agent subsequently packaged the categorical group
isomorphism in `FrobeniusFiniteFieldDescentGroupIso.lean`; the latter is not
attributed to this agent.

Verification: the group-descent target completed **10,881 jobs**. Twelve selected
definitions/theorems were audited; each reported only
`propext`, `Classical.choice`, and `Quot.sound`.

Logs in `/workspace/scratch/8cf314e8ad34/`:

- `group-descent28-final-build.log`
- `group-descent28-axioms.log`

### 2. Actual integral and rational Tate constructions

- `AbelianTateModule.lean`
- `AbelianTateGalois.lean`
- `AbelianTateFunctor.lean`
- `AbelianTateGaloisFunctor.lean`
- `AbelianTateScalarFrobenius.lean`

The underlying points are actual scheme points with their actual group law.
The prime-to-characteristic torsion cardinality is derived from the geometric
multiplication theorem. The integral Tate module is finite free of rank `2*g`,
and its rational extension has dimension `2*g`. Actual group morphisms induce
the integral/rational maps, with identity, composition, and multiplication-by-an-
integer formulas. Actual geometric points give the Galois actions, and genuine
group maps intertwine those actions.

An actual quotient with its actual multiplication quasi-inverse induces a
rational Tate equivalence. The quotient and quasi-inverse construction used here
is `tate_isogeny28`'s `ScalarFrobeniusTateQuotientDescent.lean`.

For an actual scalar-Frobenius model over the literal fixed field, its true
Frobenius-square automorphism acts by `p` on geometric points and on both Tate
representations. These are not supplied abstract representations.

Scope: the upstream `TateModule` definition is in universe zero, so these Tate
APIs use fields in `Type`. No separate topological continuity theorem for the
Galois representation has been asserted.

Verification: the four functor/Galois targets completed **10,464 jobs**. Thirteen
selected declarations were audited with only the three standard axioms above.
The scalar-Frobenius file is included in the additional batch below.

Logs:

- `abelian-tate28-build.log`
- `abelian-tate-galois28-build.log`
- `abelian-tate-final28-build.log`
- `abelian-tate28-axioms.log`

### 3. Scalar Frobenius gives actual homomorphism invariance

- `FrobeniusFiniteFieldScalarHom.lean`
- `FrobeniusFiniteFieldScalarHomDescent.lean`

The actual coefficient automorphism on a scalar-extension scheme is constructed
by the pullback universal property. It satisfies `[p] tau = F^2`. Every genuine
geometric group homomorphism between two such models has Frobenius-invariant
projection. The final `changeBase_projection_invariant` is exactly the
coefficient-change equality consumed by root's
`FrobeniusFiniteFieldHomDescent.exists_fixedField_hom`.

The generic naturality/cancellation argument and Hom-scheme descent are root's
contributions, not this agent's. These files supply their actual scalar-model
inputs.

Verification: the combined targets, including `AbelianTateScalarFrobenius`,
completed **11,379 jobs**. Ten selected declarations across this batch were
audited with only the three standard axioms.

Logs:

- `scalar-hom-tate28-build.log`
- `scalar-hom-tate28-axioms.log`

### 4. Actual differentiation respects group addition

- `PointedCotangentGroupAdd.lean`
- `PointedCotangentGroupAddRing.lean`
- `PointedCotangentGroupAddElliptic.lean`

Naturality on product coefficient modules proves that actual multiplication of
square-zero group points corresponds to addition of functionals on the genuine
local cotangent space. In particular, `differential_law_mul` proves the addition
formula for actual scheme maps, and `differential_law_one` proves the zero-map
formula.

An actual ring action by pointed group endomorphisms can consequently be
differentiated. On a one-dimensional cotangent space the resulting scalar map
is a genuine ring homomorphism; the order reversal of contravariant
differentiation is handled by commutativity of the scalar field.

`WeierstrassGroupModel.exists_actual_cotangentScalarRingHom` constructs the
actual scheme action of the genuine rational elliptic endomorphism ring and its
scalar cotangent ring homomorphism. It retains injectivity of the scheme action,
the exact action on Weierstrass points, multiplication preservation on every test
scheme, and the exact actual differential formula. It uses
`oort_end_rank28`'s checked `EllipticTorsionLiftingEndRealization` construction.

Verification: final target completed **9,727 jobs**. Ten selected declarations
were audited with only the three standard axioms.

Logs:

- `cotangent-elliptic28-build.log`
- `cotangent-add-ring28-axioms.log`

### 5. Actual Hopf-coordinate/local cotangent scalar comparison

- `PointedCotangentHopfAffine.lean`
- `PointedCotangentHopfScalar.lean`
- `PointedCotangentHopfRestriction.lean`

The affine augmentation construction classifies actual square-zero points by
functionals on the coordinate augmentation quotient. Spec-map faithfulness and
the universal square-zero points prove
`hopf_differential_spec_eq_smul_iff`: the genuine local differential of an actual
Hopf Spec map is `lambda * id` exactly when its coordinate cotangent map is that
scalar. This comparison does not assume locality or a dimension coincidence.

Scalar conjugacy is transported through genuine pointed scheme isomorphisms,
giving the actual Frobenius-kernel specialization
`FrobeniusKernelHopf.differential_eq_smul_iff_coordinate`.

Finally, `coordinate_eq_smul_of_ambient_differential` transports an ambient
elliptic endomorphism's scalar to its actual restricted Hopf map using the actual
commuting squares. The subgroup inclusion is a monomorphism, so its cotangent
map is surjective; no supplied cotangent isomorphism is needed.

Verification: final target completed **10,504 jobs**. The three files are frozen.
The eight selected declarations in the prepared audit have now been checked:
all depend only on `propext`, `Classical.choice`, and `Quot.sound`. The audit
was run sequentially after root reopened the compiler memory gate.

Files/logs:

- `cotangent-hopf-final28-build.log`
- prepared audit: `/workspace/scratch/8cf314e8ad34/cotangent-hopf28-audit.lean`
- completed audit log: `/workspace/scratch/8cf314e8ad34/cotangent-hopf28-axioms.log`

## Actual multiplication differential

`PointedCotangentGroupAddNsmul.lean` proves `schemeNsmul_point` and
`differential_schemeNsmul`: the genuine scheme multiplication map fixes the
identity and its actual local cotangent differential is `(n : K) * id`. The
proof is induction using the checked actual addition and constant-map
theorems. It supports prime-to-characteristic isogeny transport without a
supplied linear action.

Verification: target completed **9,214 jobs**. Build log:
`cotangent-nsmul28-build.log`. Both declarations were separately audited and
use only `propext`, `Classical.choice`, and `Quot.sound`; completed log
`cotangent-nsmul28-axioms.log`.

## Symplectic graph and lattice continuation

`ScalarFrobeniusTateSymplectic.lean` now compiles, together with the rational
anti-isometry, saturated integral graph lattice, direct-summand, isotropy,
and reduction cardinality modules. The actual Riemann pairing and iterated
root modules also compile. These supersede the earlier uncompiled handoff.

## Remaining classification boundary

The global construction of an elliptic subgroup of an arbitrary zero-dV
surface remains open. The actual complementary-product finiteness theorem
and reverse isogeny now compile; their precise subgroup assumption is
recorded in `checkpoint-28-product-isogeny.md`. The local endomorphism lifting
for the chosen elliptic model is checked, but arbitrary-factor transfer and
Oort's integral product-splitting induction remain. See the checkpoint report
for the complete build and axiom-audit results.
