import SupersingularCurves.Hyperelliptic.GenusTwoQuotient
import SupersingularCurves.Hyperelliptic.GenusTwoQuotientVanishing
import SupersingularCurves.Hyperelliptic.GenusTwoVerschiebungSquare
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientPoints
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorHom
import SupersingularCurves.Hyperelliptic.CharacteristicThreeObstruction
import SupersingularCurves.Hyperelliptic.FifthPowerClassification

/-!
Checks on the actual y² = x⁵ − 1 Jacobians. In characteristic 3 the actual
simultaneous subgroup and quotient have degree 3, both residual factors have
degree 3, the quotient retains p-rank zero, and the genuine twofold V
cotangent differential vanishes. In characteristic 19 the actual simultaneous
subgroup instead has order 19². No product classifier is assumed.
-/
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open SupersingularCurves.Geometry SupersingularCurves.Hyperelliptic
open FrobeniusVerschiebungSubgroup

namespace Checkpoint26Examples
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
private abbrev Q := quotientData 3 A
private abbrev M19 := FifthPowerClassification.model
  (K := AlgebraicClosure (ZMod 19)) 19 (by decide)
private abbrev J19 := M19.jacobianRealization.jacobian

private theorem C3_square_zero :
    ∀ ω : M.GlobalForms, M.globalCartier 3 (M.globalCartier 3 ω) = 0 :=
  (FifthPowerClassification.global_cartier_square_zero_iff 3
    (by decide) (by decide)).mpr (by decide)

private theorem C3_ne_zero : ¬ ∀ ω : M.GlobalForms, M.globalCartier 3 ω = 0 :=
  M.not_all_globalCartier_three_zero
    (FifthPowerClassification.quintic_separable 3 (by decide))
    (Or.inl FifthPowerClassification.quintic_degree)

private theorem A_prank_zero : A.HasPRankOver 3 0 :=
  (FifthPowerClassification.jacobian_hasPRankOver_zero_iff 3
    (by decide) (by decide)).mpr (by decide)

private theorem V3_ne_zero : GroupScheme.verschiebungCotangent 3 A.group
    (GroupScheme.law_commutative A.group) ≠ 0 := by
  intro h
  exact C3_ne_zero ((J.verschiebungCotangent_eq_zero_iff_forall
    (differentialChart M.curveModel) 3 M.x).mp
    ((J.groupScheme_verschiebungCotangent_eq_zero_iff 3).mp h))

example : (toBase 3 A).finrank (IsLocalRing.closedPoint K) = 3 :=
  M.jacobian_subgroup_order_eq_prime_of_globalCartier 3
    (FifthPowerClassification.quintic_separable 3 (by decide))
    (Or.inl FifthPowerClassification.quintic_degree) (by decide) J
    C3_square_zero C3_ne_zero

example : (toBase 19 J19.abelianVariety).finrank
    (IsLocalRing.closedPoint (AlgebraicClosure (ZMod 19))) = 361 := by
  have hV : GroupScheme.verschiebungCotangent 19 J19.abelianVariety.group
      (GroupScheme.law_commutative J19.abelianVariety.group) = 0 :=
    (J19.groupScheme_verschiebungCotangent_eq_zero_iff 19).mpr
      ((J19.verschiebungCotangent_eq_zero_iff_forall
        (differentialChart M19.curveModel) 19 M19.x).mpr
        ((FifthPowerClassification.global_cartier_zero_iff 19
          (by decide) (by decide)).mpr (by decide)))
  rw [simultaneousKernel_finrank_of_verschiebungCotangent_eq_zero 19 J19.abelianVariety hV,
    FifthPowerClassification.genus_eq_two 19 (by decide)]
  norm_num

example : ∃ B : AbelianVariety K (genusFF K M.FunctionField),
    ∃ q : twistGroup 3 A ⟶ B.group,
      IsIsogeny q ∧ ∀ y : B.group.X.left, q.hom.hom.left.finrank y = 3 :=
  M.jacobian_exists_degree_prime_quotient_of_globalCartier 3
    (FifthPowerClassification.quintic_separable 3 (by decide))
    (Or.inl FifthPowerClassification.quintic_degree) (by decide) J
    C3_square_zero C3_ne_zero

example (y : Q.carrier) (z : SchemeFrobenius.Twist 3 (base 3 A))
    (w : A.group.X.left) :
    Q.quotientMap.finrank y = 3 ∧ Q.frobeniusFactor.1.finrank z = 3 ∧
      Q.verschiebungFactor.1.finrank w = 3 := by
  have hg : genusFF K M.FunctionField = 2 :=
    FifthPowerClassification.genus_eq_two 3 (by decide)
  exact ⟨Q.finrank_eq_prime_of_dimension_two hg A_prank_zero V3_ne_zero y,
    Q.frobeniusFactor_finrank_eq_prime hg A_prank_zero V3_ne_zero z,
    Q.verschiebungFactor_finrank_eq_prime hg A_prank_zero V3_ne_zero w⟩

example : Q.abelianVariety.HasPRankOver 3 0 := Q.hasPRankOver_zero A_prank_zero

example : IsIsogeny Q.frobeniusFactorHom ∧ IsIsogeny Q.verschiebungFactorHom ∧
    Q.quotientMap ≫ Q.frobeniusFactorHom.hom.hom.left =
      SchemeFrobenius.relative 3 (base 3 A) :=
  ⟨Q.frobeniusFactorHom_isIsogeny, Q.verschiebungFactorHom_isIsogeny,
    Q.quotientMap_frobeniusFactor⟩

example : J.twistedVerschiebungCotangent 3 ∘ₗ J.verschiebungCotangent 3 = 0 :=
  M.jacobian_verschiebungCotangent_twice_eq_zero_of_globalCartier 3 J C3_square_zero

local instance : Smooth Q.group.X.hom := Q.smooth

example : GroupScheme.verschiebungCotangent 3 Q.group
    (GroupScheme.law_commutative Q.group) = 0 :=
  M.jacobian_quotient_verschiebungCotangent_eq_zero_of_globalCartier 3
    (FifthPowerClassification.quintic_separable 3 (by decide))
    (Or.inl FifthPowerClassification.quintic_degree) (by decide) J Q
    C3_square_zero C3_ne_zero

example : ∃ (B : AbelianVariety K (genusFF K M.FunctionField))
    (f : A.group ⟶ B.group), IsIsogeny f ∧
      GroupScheme.verschiebungCotangent 3 B.group
        (GroupScheme.law_commutative B.group) = 0 :=
  M.jacobian_exists_isogeny_to_zero_verschiebungCotangent_of_globalCartier 3
    (FifthPowerClassification.quintic_separable 3 (by decide))
    (Or.inl FifthPowerClassification.quintic_degree) (by decide) J C3_square_zero

end Checkpoint26Examples
