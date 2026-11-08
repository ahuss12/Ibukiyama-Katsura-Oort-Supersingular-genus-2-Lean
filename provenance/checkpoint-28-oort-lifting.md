# Checkpoint 28: actual finite torsion and local restriction lifting

## Current checkpoint boundary

The later `EllipticTorsionLiftingEndLocalLifting.lean` now compiles: for the
chosen supersingular elliptic model after field extension, a Frobenius-kernel
endomorphism which extends to actual p-torsion is lifted to an actual global
endomorphism. The supporting restriction and base-change action modules also
compile. This does not supply arbitrary-factor transfer or Oort's quotient
induction. The historical development notes below describe earlier stages;
current verification is recorded in `verification/CHECKPOINT_28_REPORT.md`.

## Historical development notes

This note records the local Oort branch. It does **not** assert that the integral
elliptic-product classification or Block 1 is complete. All constructions use the
existing independently defined abelian variety, group law, Frobenius,
Verschiebung, and actual scheme kernels.

## Verified constructions

The following new modules have compiled. Paths below are relative to
`SupersingularCurves/Geometry/`.

1. `EllipticTorsionLiftingVerschiebung`: canonical inverse-Frobenius-semilinear
   finite Hopf Verschiebung over a perfect characteristic-p field. Its dual
   Frobenius pairing, uniqueness, ring/coproduct structure, FV=VF=[p], and
   naturality for every finite Hopf morphism are proved.
2. `EllipticTorsionLiftingLevels`: actual A[nm]→A[n] projection, actual A[m]
   identity fibre, finite flat surjectivity and fibre degree.
3. `EllipticTorsionLiftingImage`: constructs the actual coordinate-image
   equivalence for A[p²]→A[p] and multiplication by p.
4. `EllipticTorsionLiftingComparison`: a general two-level algebra comparison
   lemma, with its image-identification hypothesis explicit.
5. `EllipticTorsionLiftingSchemeComparison`: uniqueness of two compatible V
   systems by actual finite-flat/closed-immersion cancellation at p² and p.
6. `EllipticTorsionLiftingAmbient`: constructs the actual semilinear ambient V
   and its compatible restriction to all actual torsion levels.
7. `EllipticTorsionLiftingPresentation`: constructs actual finite Hopf
   presentations Spec(H)≅A[n] and their natural multiplicative point comparison
   on every test algebra.
8. `EllipticTorsionLiftingCanonical`: realizes canonical finite Hopf V on those
   actual torsion schemes and proves the actual VF multiplication identity.
9. `EllipticTorsionLiftingProjection`: the transition Hopf map is constructed
   from the actual multiplication projection and its full test-algebra action.
10. `EllipticTorsionLiftingAmbientComparison`: proves actual ambient V restricted
    to A[p] equals canonical finite V. The A[p²] presentation and comparison
    are constructed internally. No V-identification input is assumed.
11. `EllipticTorsionLiftingNaturality`: arbitrary finite p-torsion Hopf morphisms
    commute with actual ambient V without requiring an ambient lift.
12. `EllipticTorsionLiftingHeightOne`: for the actual elliptic ker(F) coordinate
    algebra, proves a^p=algebraMap(counit(a)^p), hence pth-power-zero augmentation.
13. `EllipticTorsionLiftingCotangent`: factors a genuine Hopf map through its
    actual Hopf image. Zero cotangent action into a height-one group forces the
    image augmentation I=I²; nilpotence then gives I=0. Thus the original map
    is unit-counit. Also proves actual ker(F) coordinate cotangent dimension 1.
14. `EllipticTorsionLiftingFaithfulness`: two finite Hopf maps from a height-one
    finite group are equal when their cotangent actions are equal. Constructs
    an injective actual ker(F)-endomorphism scalar function. No alpha-p model
    or supplied faithful derivative representation is used.
15. `EllipticTorsionLiftingResidual`: constructs the actual residual scheme
    automorphism T from dV=0, proves its inverse-Frobenius² field action and
    identity-section formula, and proves ambientV=absoluteF≫T.
16. `EllipticTorsionLiftingScalarBound`: an augmented semilinear coordinate
    automorphism commuting with an actual ker(F) endomorphism fixes its proved
    cotangent scalar. Its geometric automorphism/commutation hypotheses remain
    explicit. The nonzero cotangent direction is constructed from rank 1.
17. `EllipticTorsionLiftingResidualKernel`: every actual pointed semilinear
    scheme automorphism restricts to an actual automorphism of the entire
    nonreduced Frobenius kernel. Applies this to the constructed residual T,
    with its actual inclusion, identity-section, and field-map formulas.

The canonical ambient comparison resolves items 1 and 2 of
`checkpoint-27-oort-obligations.md`. Faithfulness resolves the height-one
cotangent-faithfulness subproblem in item 3.

## Verification

Targeted successful logs under `/workspace/scratch/8cf314e8ad34/` include:

- `elliptic-torsion-lifting-verschiebung28-build5.log` (8,771 jobs)
- `elliptic-torsion-lifting-levels28-build3.log` (10,401 jobs)
- `elliptic-torsion-lifting-image28-build2.log` (10,402 jobs)
- `elliptic-torsion-lifting-ambient28-build2.log` (10,605 jobs)
- `elliptic-torsion-lifting-ambientcomparison28-build.log` (10,655 jobs)
- `elliptic-torsion-lifting-naturality28-build.log` (10,656 jobs)
- `elliptic-torsion-lifting-heightone28-build3.log` (10,438 jobs)
- `elliptic-torsion-lifting-scalarbound28-build.log`: contains the successful
  Faithfulness target build; the subsequent ScalarBound target needed fixes.
- `elliptic-torsion-lifting-local28-build.log`: contains the successful
  Residual target build; subsequent new targets needed fixes.
- `elliptic-torsion-lifting-scalarbound28-serial.log` (10,501 jobs, complete).
- `elliptic-torsion-lifting-residualkernel28-serial.log` (10,668 jobs, complete).

The following audit logs contain only `propext`, `Classical.choice`, and
`Quot.sound` for the inspected declarations:

- `elliptic-torsion-lifting-verschiebung28-axioms.log` (7 declarations)
- `elliptic-torsion-lifting-levels28-axioms.log` (9 declarations)
- `elliptic-torsion-lifting-ambient28-axioms.log` (13 declarations)
- `elliptic-torsion-lifting-faithfulness28-axioms.log` (5 declarations)

## In progress; not yet a completed local lifting theorem

`EllipticTorsionLiftingResidualCoordinates` is written and awaiting its final
serial check after the shared host memory limit stopped concurrent compilers.
Its intended output is: the actually constructed residual automorphism makes
any commuting ker(F) scalar satisfy
λ^(p²)=λ. The commutation premise remains explicit until the next construction.

The next concrete geometric construction is:

1. Build an actual isomorphism ker(V)≅ker(F) from V=absoluteF≫T using the twist
   projection and inverse projection, including their field maps.
2. Compose it with the existing actual finite-flat epi E[p]→ker(V), yielding
   q:E[p]→ker(F) whose ambient composite is actual absolute Frobenius.
3. For an arbitrary finite torsion map f and its restriction r, Frobenius
   naturality gives f q=q r. Ambient V naturality gives f q T=q T r. Cancelling
   q and the actual closed immersion proves r T=T r, so λ^(p²)=λ.
4. Combine that scalar bound with the independently constructed actual global
   endomorphisms realizing all Fp² scalars, and with the actual coordinate/local
   cotangent restriction comparison. This is the local restriction-lifting
   theorem; it is not asserted as proved in this note.

The separate End branch owns `EllipticTorsionLiftingEndRealization`,
`EllipticTorsionLiftingEndGroup`, and `EllipticTorsionLiftingEndResidue*`. Its
faithful integral rank-four family alone is **not** a p-saturation theorem.
The stronger current route uses the image of a maximal quaternion order under
the actual derivative ring map, avoiding the unproved degree/norm comparison.

Even a completed local lifting theorem leaves the actual integral
kernel-straightening/extension-splitting argument and its induction to construct
an E₁×E₂ group-scheme isomorphism. The other branch separately constructs the
initial product isogeny. Neither is replaced here by a supplied classification
or local-fullness hypothesis.
