# Checkpoint 28: actual Tate and Riemann pairing bridges

## Current verification status

All four pairing bridges below now pass their Lake builds. The rational
extension and iterated line-bundle root modules also compile. The complete
checkpoint audit is recorded separately in `verification/CHECKPOINT_28_REPORT.md`.
These results do not complete the global classification.

The separate
`SupersingularCurves/Geometry/ClassificationSurfaceEllipticExistence.lean`
has passed its targeted Lake build and an axiom audit of nine principal
declarations. That audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. It constructs an independently supersingular elliptic abelian
variety over every algebraically closed field of positive prime
characteristic, including characteristic two. It does not construct a map
from that elliptic curve into a prescribed surface.

## Files and mathematical scope

| File in `SupersingularCurves/Geometry/` | Content | Check status |
| --- | --- | --- |
| `AbelianTateRiemannPoints.lean` | An additive equivalence between actual categorical group-scheme points and the relative group law's `AlgPoints`, followed by the induced integral Tate module linear equivalence. | Lake build passed. |
| `AbelianTateRiemannForm.lean` | Constructs compatible roots of unity and an alternating Riemann pairing on the actual integral Tate module from an invertible line bundle; proves uniqueness and transfers the geometric criterion for perfectness. | Lake build passed. |
| `AbelianTateRiemannPullback.lean` | Cross-variety naturality of the geometric level pairing, then naturality along the actual Tate map of a genuine group-scheme morphism. | Lake build passed. |
| `AbelianTateRiemannFiniteKernel.lean` | Uses the finite translation kernel of a finite-by-sections line bundle to obtain a finite bound; every auxiliary prime larger than this bound and different from the characteristic gives a constructed perfect alternating Riemann pairing. | Lake build passed. |

The pairing is not supplied as an input to the existence theorems. In the
strongest existence statement, the inputs are an actual abelian variety, an
actual invertible line bundle finite by sections, and a sufficiently large
auxiliary prime different from the characteristic. The existence statement
constructs both the normalization by roots of unity and the pairing.

The two Tate presentations are related by a proved equivalence; neither
the point group nor the Tate module is replaced by a freely chosen vector
space or representation.

## Source attribution

The source corpus is the pinned FLT proof/statement corpus at commit
`aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`. Exact public theorem statements
are cached under `classification-source-inspection/full-statements27`, and
the corresponding proof bodies are restored under `vendor/flt/P2M/Sol`.
The parent integration process owns the source manifests. This task has
not edited vendor proofs or shared manifests.

The construction and geometric criteria use these exact upstream roots:

- `AlgebraicGeometry.RiemannForm.exists_isRiemannForm`
- `AlgebraicGeometry.RiemannForm.isRiemannForm_unique`
- `AlgebraicGeometry.RiemannForm.isRiemannForm_swap_eq_neg_and_self_eq_zero`
- `AlgebraicGeometry.RiemannForm.perfect_of_forall_torsion_kernelPts_eq_zero`
- `IsAlgClosed.exists_isPrimitiveRoot_pow_and_pow_succ_eq`
- `AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq`
- `AlgebraicGeometry.Polarisation.kernelPts_finite_and_geomFibreH0Finrank_pos_of_finiteBySections`
- `AlgebraicGeometry.Polarisation.mem_kernelPts_iff_nonempty_pullback_translate_iso`
- `AlgebraicGeometry.RiemannForm.exists_addSubgroup_mem_iff_nonempty_pullback_translation_iso`
- `AlgebraicGeometry.RiemannForm.translation_eq_translate_toUnitPt_and_translate_eq_translation_ofUnitPt`

The public root
`AlgebraicGeometry.RiemannForm.isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback`
states an adjointness result for an endomorphism of one variety. The new
cross-variety proof instead uses its more general checked internal lemmas
from the proof namespace
`P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback`:

- `RFFunct29.Geom.hxA`
- `RFFunct29.Geom.nsmul_comm`
- `RFFunct29.Geom.translation_comm`
- `RFFunct29.Mod.sq`
- `RFFunct29.Mod.isConstScalar_pullback`
- `RFFunct29.Mod.isConstScalar_conj`
- `LevelAdjoint29.sig_pullback_hom`
- `LevelAdjoint29.isConstScalar_sig_conj`

These internal lemmas express actual pullback functor coherence and
translation/multiplication commutation across two schemes. They allow the
new proof to construct the required pullback line isomorphism and transport
its scalar commutator. No cross-variety naturality assumption is introduced.

The independently staged
`RiemannForm.thetaGroup.exists_monoidHom_pullback_pt_eq_and_isScalarElt`
is a valid alternative source of cross-variety theta-group naturality, but
the current proof does not require it.

## Verification details

The original foundation build had a resource failure (exit 137). The retry
completed successfully with one Lean thread. All pairing targets, including
cross-variety pullback, finite-kernel perfectness, rational extension, and
`ScalarFrobeniusTateRiemannRoot.lean`, now compile. The checkpoint-wide build
and transitive axiom audit supersede the earlier handoff's pending checks.
See `verification/CHECKPOINT_28_REPORT.md` for the executed results.

## Remaining geometric uniform-polarization requirement

Verification of these files does not finish the global surface classification. The following application still has to be proved
on the actual quotient abelian varieties:

1. The rational anti-isometry, saturated graph lattice, direct-summand
   property, isotropy, and reduction cardinality lemmas now compile. Their
   application to the actual quotient family must still be assembled.
2. For each actual quotient and its residual isogeny, identify the Tate
   image with the prescribed lattice plus the power of the maximal ideal.
   Apply the geometric pullback formula to obtain divisibility of the
   Riemann pairing by the required power of the auxiliary prime.
3. Apply the now-compiled iterated line-bundle root theorem to
   obtain an actual line bundle whose tensor power differs from the
   pulled-back polarization by an actual Picard-zero line bundle.
4. Prove positivity/finite-by-sections of that root and a bound on its
   polarization degree or Euler characteristic independent of the
   quotient index. The expected cancellation compares the residual
   isogeny degree with tensor-power growth; it must be justified by
   genuine scheme degree and line-bundle formulas.
5. Descend these prescribed polarizations to the common finite field with
   a fixed tensor exponent, then apply the finite polarized-moduli
   statement to the resulting actual models.

A concrete source route for the positivity part of step 4 is available:
`Polarisation.geomFibreH0Finrank_pos_of_iso_tensorPow_tensor_of_inPicZero_of_kernelPts_finite`
transfers positivity of geometric sections through the tensor-root/Picard-zero
isomorphism, assuming the root's translation kernel is finite. The already
restored
`Polarisation.finiteBySections_of_iso_tensorPow_three_of_finite_kernelPts_of_finrank_pos`
then makes the fixed cube of that root finite by sections. A further uniform
very ampleness theorem is required for the available finite-moduli argument;
finite-by-sections alone does not supply a closed projective immersion. Applying these
sources to the actual quotients, proving the required kernel finiteness,
and establishing the uniform numerical bound are still pending.

The global extraction of an actual nonzero elliptic-to-surface morphism or
product isogeny, and the subsequent passage to an actual product
isomorphism, remain separate obligations. A pairing or a local Tate or
p-divisible-group isomorphism is not asserted to supply that global
isomorphism by itself.
