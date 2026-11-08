/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.LocalAlgebraFrobeniusOrder
import SupersingularCurves.Geometry.LocalGroupInvariantDerivation
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupHeightOne
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupGroup
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupDimension
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupIdentity

/-!
# The actual order of the simultaneous Frobenius--Verschiebung kernel

The actual finite subgroup with cotangent dimension one has scheme-theoretic
order p. Its genuine group law produces the invariant derivation needed for
the length calculation; Frobenius vanishing is derived from its construction.
No subgroup order, group classification, or quotient is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian

namespace FiniteGeometricPoints
variable {K : Type u} [Field K] {X : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of K))
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    [IsFinite c] [Flat c] [Subsingleton X]

/-- Scheme-theoretic finite-flat rank of a one-point scheme over a field
is the dimension of its actual local stalk, using the canonical spectrum map. -/
theorem finrank_eq_stalk_finrank (y : Spec (CommRingCat.of K)) :
    c.finrank y = Module.finrank K (PointedCotangent.Stalk c s) := by
  let : IsAffine X := isAffine_of_isAffineHom c
  let := finite_stalk c s
  let := FiniteLocalGroupScheme.fromSpecStalk_isIso c s
  have h := congrFun (Scheme.Hom.finrank_comp_left_of_isIso
    (X.fromSpecStalk (s.1 (IsLocalRing.closedPoint K))) c) y
  rw [FiniteLocalGroupScheme.fromSpecStalk_over c s,
    Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free] at h
  exact h.symm

end FiniteGeometricPoints

namespace FiniteLocalGroupScheme
variable {K : Type u} [Field K] {X : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of K))
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    [IsFinite c] [Flat c] [Subsingleton X]
    (G : RelativeGroupLaw K c) (hs : G.one (𝟙 _) = s)

include G hs in
/-- A genuine finite local group scheme with one-dimensional cotangent
space and height-one local power equations has actual order p. -/
theorem finrank_eq_prime_of_cotangent_dimension_one
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hdim : Module.finrank K (PointedCotangent.Cotangent c s) = 1)
    (hF : ∀ x : IsLocalRing.maximalIdeal (PointedCotangent.Stalk c s),
      (x : PointedCotangent.Stalk c s) ^ p = 0)
    (y : Spec (CommRingCat.of K)) : c.finrank y = p := by
  let : IsAffine X := isAffine_of_isAffineHom c
  let := FiniteGeometricPoints.finite_stalk c s
  let : IsNoetherianRing (PointedCotangent.Stalk c s) :=
    IsNoetherianRing.of_finite K (PointedCotangent.Stalk c s)
  rw [FiniteGeometricPoints.finrank_eq_stalk_finrank c s y]
  apply LocalAlgebraFrobeniusOrder.finrank_eq_prime_of_cotangent_dimension_one
    p (PointedCotangent.augmentation c s) (PointedCotangent.ker_augmentation c s) hdim hF
  exact LocalGroupInvariantDerivation.exists_derivation_augmentation_ne_zero c s G hs

end FiniteLocalGroupScheme

namespace FrobeniusVerschiebungSubgroup
variable {K : Type u} [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]
    {g : ℕ} (A : AbelianVariety K g)

/-- The actual simultaneous finite subgroup has order p whenever its
actual identity cotangent space has dimension one. Every ring-theoretic
hypothesis is supplied by the actual subgroup and its genuine group law. -/
theorem finrank_eq_prime_of_cotangent_dimension_one
    (hdim : Module.finrank K (PointedCotangent.Cotangent
      (toBase p A) (identityPoint p A)) = 1) :
    (toBase p A).finrank (IsLocalRing.closedPoint K) = p := by
  let := subsingleton p A
  exact FiniteLocalGroupScheme.finrank_eq_prime_of_cotangent_dimension_one
    (toBase p A) (identityPoint p A) (subgroupLaw p A) rfl p hdim
    (fun x => maximalIdeal_pow_eq_zero p A x x.2) (IsLocalRing.closedPoint K)


/-- The two existing structure-map presentations give the same actual
cotangent dimension, by their canonical identity scheme isomorphism. -/
theorem cotangent_finrank_toBase_eq_fibre :
    Module.finrank K (PointedCotangent.Cotangent (toBase p A) (identityPoint p A)) =
      Module.finrank K (PointedCotangent.Cotangent (fibreToBase p A) (fibreIdentityPoint p A)) := by
  let e := PointedCotangent.isoEquiv
    (c := toBase p A) (d := fibreToBase p A)
    (s := identityPoint p A) (z := fibreIdentityPoint p A)
    (Iso.refl (scheme p A))
    (by simpa only [Iso.refl_hom, Category.id_comp] using (structure_eq_fibreToBase p A).symm)
    (by simpa only [Iso.refl_hom, Category.comp_id] using identityPoint_coe_eq_fibreIdentityPoint p A)
  exact e.finrank_eq.symm

/-- Order p in the presentation used by the existing actual cotangent
exact-sequence and dimension theorems. -/
theorem finrank_eq_prime_of_fibre_cotangent_dimension_one
    (hdim : Module.finrank K (PointedCotangent.Cotangent
      (fibreToBase p A) (fibreIdentityPoint p A)) = 1) :
    (toBase p A).finrank (IsLocalRing.closedPoint K) = p := by
  apply finrank_eq_prime_of_cotangent_dimension_one p A
  rw [cotangent_finrank_toBase_eq_fibre, hdim]

/-- For a p-rank-zero abelian surface with nonzero actual Verschiebung
cotangent map, the actual simultaneous kernel has scheme-theoretic order p. -/
theorem finrank_eq_prime_of_dimension_two (hg : g = 2)
    (hA : A.HasPRankOver p 0)
    (hV : GroupScheme.verschiebungCotangent p A.group
      (GroupScheme.law_commutative A.group) ≠ 0) :
    (toBase p A).finrank (IsLocalRing.closedPoint K) = p :=
  finrank_eq_prime_of_fibre_cotangent_dimension_one p A
    (cotangent_finrank_eq_one_of_dimension_two p A hg hA hV)

end FrobeniusVerschiebungSubgroup
end SupersingularCurves.Geometry
