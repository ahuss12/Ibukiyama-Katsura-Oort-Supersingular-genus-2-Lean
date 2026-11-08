import SupersingularCurves.Hyperelliptic.GenusTwoFrobeniusIsomorphism
import SupersingularCurves.Hyperelliptic.CharacteristicThreeObstruction
import SupersingularCurves.Hyperelliptic.FifthPowerClassification
import SupersingularCurves.Hyperelliptic.GenusTwoFiniteSubgroup

/-!
Concrete actual-geometry checks for y² = x⁵ − 1. In characteristic 19,
Cartier vanishing constructs the residual scheme and group isomorphisms.
In characteristic 3 the genuine V-kernel has length 9, and both that kernel
and ker F ∩ ker V have nonzero cotangent spaces, despite a unique geometric
point. No product isomorphism or product isogeny is assumed.
-/
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open SupersingularCurves.Geometry SupersingularCurves.Hyperelliptic

namespace Checkpoint25Examples
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance : NeZero (2 : AlgebraicClosure (ZMod 3)) :=
  ⟨fun h => (show ¬ 3 ∣ 2 by decide) ((CharP.cast_eq_zero_iff _ 3 2).mp h)⟩
local instance : NeZero (2 : AlgebraicClosure (ZMod 19)) :=
  ⟨fun h => (show ¬ 19 ∣ 2 by decide) ((CharP.cast_eq_zero_iff _ 19 2).mp h)⟩

private abbrev K := AlgebraicClosure (ZMod 3)
private abbrev M := FifthPowerClassification.model (K := K) 3 (by decide)
private abbrev J := M.jacobianRealization.jacobian
private abbrev A := J.abelianVariety
private abbrev M19 := FifthPowerClassification.model
  (K := AlgebraicClosure (ZMod 19)) 19 (by decide)
private abbrev J19 := M19.jacobianRealization.jacobian

example : ∃ e : SchemeFrobenius.Twist 19 (J19.twistToBase 19) ≅ J19.designation.P,
    SchemeFrobenius.relative 19 (J19.twistToBase 19) ≫ e.hom = J19.verschiebung 19 ∧
      e.hom ≫ J19.designation.toBase = SchemeFrobenius.toBase 19 (J19.twistToBase 19) :=
  M19.jacobian_exists_frobenius_factor_iso_of_globalCartier_zero 19
    (FifthPowerClassification.quintic_separable 19 (by decide))
    (Or.inl FifthPowerClassification.quintic_degree) (by decide) J19
    ((FifthPowerClassification.global_cartier_zero_iff 19 (by decide) (by decide)).mpr
      (by decide))

example : ∃ e : J19.abelianVariety.doubleFrobeniusTwistGroup 19 ≅ J19.abelianVariety.group,
    SchemeFrobenius.relative 19 (J19.twistToBase 19) ≫ e.hom.hom.hom.left =
      J19.verschiebung 19 :=
  (M19.globalCartier_zero_iff_jacobian_exists_frobenius_factor_groupIso 19
    (FifthPowerClassification.quintic_separable 19 (by decide))
    (Or.inl FifthPowerClassification.quintic_degree) (by decide) J19).mp
    ((FifthPowerClassification.global_cartier_zero_iff 19 (by decide) (by decide)).mpr
      (by decide))

example : ¬ J.IsSuperspecial 3 :=
  M.jacobian_not_isSuperspecial_three
    (FifthPowerClassification.quintic_separable 3 (by decide))
    (Or.inl FifthPowerClassification.quintic_degree) J

example : (FrobeniusVerschiebungSubgroup.vToBase 3 A).finrank
    (IsLocalRing.closedPoint K) = 9 := by
  rw [FrobeniusVerschiebungSubgroup.vKernel_finrank]
  rw [FifthPowerClassification.genus_eq_two 3 (by decide)]
  norm_num

example : ¬ Subsingleton (PointedCotangent.Cotangent
    (FrobeniusVerschiebungSubgroup.vToBase 3 A)
    (FrobeniusVerschiebungSubgroup.vIdentityPoint 3 A)) :=
  FrobeniusVerschiebungSubgroup.vKernel_cotangent_not_subsingleton 3 A
    ((FifthPowerClassification.jacobian_hasPRankOver_zero_iff 3
      (by decide) (by decide)).mpr (by decide))
    (by rw [FifthPowerClassification.genus_eq_two 3 (by decide)]; decide)

example : ¬ Subsingleton (PointedCotangent.Cotangent
    (FrobeniusVerschiebungSubgroup.fibreToBase 3 A)
    (FrobeniusVerschiebungSubgroup.fibreIdentityPoint 3 A)) :=
  FrobeniusVerschiebungSubgroup.cotangent_not_subsingleton 3 A
    ((FifthPowerClassification.jacobian_hasPRankOver_zero_iff 3
      (by decide) (by decide)).mpr (by decide))
    (by rw [FifthPowerClassification.genus_eq_two 3 (by decide)]; decide)

example : Module.finrank K (PointedCotangent.Cotangent
    (FrobeniusVerschiebungSubgroup.fibreToBase 3 A)
    (FrobeniusVerschiebungSubgroup.fibreIdentityPoint 3 A)) = 1 :=
  M.jacobian_subgroup_cotangent_finrank_one_of_globalCartier 3
    (FifthPowerClassification.quintic_separable 3 (by decide))
    (Or.inl FifthPowerClassification.quintic_degree) (by decide) J
    ((FifthPowerClassification.global_cartier_square_zero_iff 3
      (by decide) (by decide)).mpr (by decide))
    (M.not_all_globalCartier_three_zero
      (FifthPowerClassification.quintic_separable 3 (by decide))
      (Or.inl FifthPowerClassification.quintic_degree))

end Checkpoint25Examples
