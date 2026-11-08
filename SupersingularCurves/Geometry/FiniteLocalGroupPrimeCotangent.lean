/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.LocalAlgebraPrimeLength
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupOrder

/-!
# The cotangent dimension of an actual local group of order p

For a genuine finite one-point group scheme of order p, the actual identity
cotangent space has dimension one. Invariant derivations are constructed
from the actual group law, and the local power equations follow from length.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FiniteLocalGroupScheme
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
variable {K : Type u} [Field K] {X : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of K))
  (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  [IsFinite c] [Flat c] [Subsingleton X]
  (G : RelativeGroupLaw K c) (hs : G.one (𝟙 _) = s)

include G hs in
/-- Actual order p forces one-dimensional actual identity cotangent space. -/
theorem cotangent_finrank_eq_one_of_finrank_eq_prime
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hlen : c.finrank (IsLocalRing.closedPoint K) = p) :
    Module.finrank K (PointedCotangent.Cotangent c s) = 1 := by
  let : IsAffine X := isAffine_of_isAffineHom c
  let := FiniteGeometricPoints.finite_stalk c s
  let : IsNoetherianRing (PointedCotangent.Stalk c s) :=
    IsNoetherianRing.of_finite K (PointedCotangent.Stalk c s)
  have hdim : Module.finrank K (PointedCotangent.Stalk c s) = p :=
    (FiniteGeometricPoints.finrank_eq_stalk_finrank c s _).symm.trans hlen
  exact LocalAlgebraPrimeLength.cotangent_finrank_eq_one p
    (PointedCotangent.augmentation c s) (PointedCotangent.ker_augmentation c s) hdim
    (LocalGroupInvariantDerivation.exists_derivation_isUnit c s G hs)

end SupersingularCurves.Geometry.FiniteLocalGroupScheme
