/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticVerschiebungFibre
import SupersingularCurves.Geometry.FiniteCotangentPoint
import SupersingularCurves.Geometry.AbelianMultiplicationDegree

/-!
# Supersingular elliptic curves have zero Verschiebung differential

The independently defined absence of geometric p-torsion gives a unique
rational point of the actual Verschiebung kernel. Were the differential
nonzero, smooth relative dimension one would make it surjective, forcing the
actual kernel cotangent space to vanish. The finite one-point kernel would
then be Spec K and have degree one. This contradicts the independently proved
degree p of Verschiebung.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p] [IsAlgClosed K]

/-- A supersingular elliptic curve, defined by its actual geometric p-torsion,
has zero cotangent map for its actual Verschiebung morphism. -/
theorem IsSupersingularElliptic.verschiebungCotangent_eq_zero
    {E : AbelianVariety K 1} (hE : E.IsSupersingularElliptic p) :
    GroupScheme.verschiebungCotangent p E.group
      (GroupScheme.law_commutative E.group) = 0 := by
  by_contra hnonzero
  let : IsFinite (ellipticVerschiebung p E) := E.verschiebung_isFinite p
  let : Flat (ellipticVerschiebung p E) := E.verschiebung_flat p
  let : IsFinite (verschiebungKernelToBase p E) := by
    change IsFinite (pullback.snd (ellipticVerschiebung p E) (GroupScheme.zero E.group).1)
    infer_instance
  let : IsIso (verschiebungKernelToBase p E) :=
    PointedCotangent.isIso_of_unique_point_of_cotangent_subsingleton
      (verschiebungKernelToBase p E) (verschiebungKernelZero p E)
      (hE.verschiebungKernel_unique_point p E)
      (E.verschiebungKernel_cotangent_subsingleton_of_nonzero p hnonzero)
  have hone := congrFun (Scheme.Hom.finrank_eq_one_of_isIso
    (verschiebungKernelToBase p E)) (IsLocalRing.closedPoint K)
  have hp : (verschiebungKernelToBase p E).finrank (IsLocalRing.closedPoint K) = p := by
    change (pullback.snd (ellipticVerschiebung p E) (GroupScheme.zero E.group).1).finrank _ = _
    rw [Scheme.Hom.finrank_pullback_snd]
    simpa only [pow_one] using
      E.verschiebung_finrank p ((GroupScheme.zero E.group).1 (IsLocalRing.closedPoint K))
  exact (Fact.out : p.Prime).ne_one (hp.symm.trans hone)

end SupersingularCurves.Geometry.AbelianVariety
