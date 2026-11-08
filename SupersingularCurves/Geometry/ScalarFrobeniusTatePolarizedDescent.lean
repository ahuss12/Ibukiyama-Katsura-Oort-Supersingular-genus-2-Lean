/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldPolarizedModel
import SupersingularCurves.Geometry.ScalarFrobeniusTatePolarizationModel
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentGroupIso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_tensor_of_projPresentation_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_isSectionBasis_of_closedImmersionBySections

/-! # Prescribed polarizations in actual finite-field abelian models -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open GoodReductionJacobian NeronModelInfra SchemeFrobenius FrobeniusDescent
  FrobeniusFiniteFieldDescent FrobeniusFiniteFieldGroupDescent

/-- A positive tensor power of an actual very ample line remains very ample. -/
theorem closedImmersionBySections_tensorPow {K : Type} [Field K] {X : Scheme.{0}}
    {c : X ⟶ Spec (CommRingCat.of K)} {L : X.Modules}
    (hL : L.ClosedImmersionBySections c) (n : ℕ) (hn : 0 < n) :
    (L.tensorPow n).ClosedImmersionBySections c := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  induction n with
  | zero =>
    obtain ⟨N, P, hP⟩ := hL
    obtain ⟨Q, hQ, _⟩ := P.exists_of_iso (Scheme.Modules.tensorPowOneIso L).symm
    exact ⟨N, Q, hQ ▸ hP⟩
  | succ n ih =>
    obtain ⟨N, P, hP⟩ := hL
    exact (ih (Nat.succ_pos _)).tensor_of_projPresentation_monoidalV2 P

namespace AbelianVariety
variable {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}
  (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p]
local instance : Smooth A.group.X.hom := SmoothOfRelativeDimension.smooth g A.group.X.hom

/-- Zero dV constructs an actual Fp² abelian model with a descended very ample
line whose pullback is exactly L^(p²), for the prescribed symmetric line L.
The exponent is independent of the variety and of L. -/
theorem exists_finiteField_polarized_abelian_model
    (hV : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0)
    (L : A.group.X.left.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hsym : Nonempty ((Scheme.Modules.pullback ((𝟙 A.group.X)⁻¹).left).obj L ≅ L))
    (hclosed : L.ClosedImmersionBySections A.group.X.hom) :
    ∃ (A₀ : AbelianVariety (fixedField K p 2) g)
      (M₀ : A₀.group.X.left.Modules) (d : A.group.X.left ⟶ A₀.group.X.left),
      Scheme.Modules.IsInvertible M₀ ∧ M₀.ClosedImmersionBySections A₀.group.X.hom ∧
      IsPullback d A.group.X.hom A₀.group.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K))) ∧
      Nonempty ((Scheme.Modules.pullback d).obj M₀ ≅ L.tensorPow (p ^ 2)) ∧
      Nonempty (A.group ≅ (A₀.baseChange K).group) ∧
      absolute p A₀.group.X.hom ≫ absolute p A₀.group.X.hom =
        (GroupScheme.law A₀.group).schemeNsmul p := by
  have hf : L.FiniteBySections A.group.X.hom := by
    obtain ⟨N, P, hP⟩ := hclosed
    letI := hP
    exact ⟨N, P, inferInstance⟩
  obtain ⟨τ, eM, hτ, hp, hM, hMf, hb, _⟩ :=
    A.exists_equivariant_model_of_symmetric_finite_bundle p hV L hL hsym hf
  let M := L.tensorPow (p ^ 2)
  have hMc : M.ClosedImmersionBySections A.group.X.hom :=
    closedImmersionBySections_tensorPow hclosed (p ^ 2) (pow_pos (Fact.out : p.Prime).pos 2)
  let := sectionsModule M A.group.X.hom
  let : Module.Finite K Γ(M, ⊤) := abelianVariety_finite_sections A M hM
  let : Nonempty A.group.X.left :=
    ⟨((GroupScheme.law A.group).one (𝟙 (Spec (CommRingCat.of K)))).1
      (IsLocalRing.closedPoint K)⟩
  obtain ⟨N, P, hP⟩ := hMf
  letI := hP
  obtain ⟨b, hb⟩ := hb
  obtain ⟨n, Q, _, hQb, hQfixed⟩ :=
    exists_finitePresentation_fixed A.group.X.hom M P (actionAddHom τ M eM) b hb
  letI : IsClosedImmersion Q.toProj :=
    Q.isClosedImmersion_toProj_of_isSectionBasis_of_closedImmersionBySections hMc hQb
  have hQτ := toProj_frobeniusSquare_equivariant_of_fixed_sections τ M eM A.group.X.hom
    p hτ Q hQfixed
  have hσ : (frobenius K p).comp (frobenius K p) = iterateFrobenius K p 2 := by
    ext x
    change (x ^ p) ^ p = x ^ (p ^ 2)
    rw [← pow_mul, pow_two]
  have hQτ' : τ.hom ≫ Q.toProj = Q.toProj ≫ coefficientMap (iterateFrobenius K p 2) n := by
    simpa only [coefficientFrobeniusSquare, hσ] using hQτ
  obtain ⟨X₀, c₀, M₀, P₀, d, hM₀, hP₀, _, hd, heM, hτd⟩ :=
    exists_fixedField_polarized_model p 2 A.group.X.hom M Q τ.hom hQτ' (by decide)
  obtain ⟨L₀, hA₀, hone⟩ := exists_descended_law p A c₀ d hd τ.hom hp hτd
  obtain ⟨hs, hpr, hc⟩ := descended_properties A c₀ d hd
  let G₀ : GroupScheme (fixedField K p 2) := { X := Over.mk c₀, grp := L₀.grpObjOverMk }
  let A₀ : AbelianVariety (fixedField K p 2) g :=
    { group := G₀
      comm := (L₀.isCommMonObj_grpObjOverMk_iff_mul_comm).mpr (hA₀.isCommutative L₀)
      smooth := hs
      proper := hpr
      connected := hc }
  have hone' : ((GroupScheme.law A.group).one (𝟙 _)).1 ≫ d =
      Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K)) ≫
        ((GroupScheme.law A₀.group).one (𝟙 _)).1 := by
    simpa only [A₀, G₀, GroupScheme.law, relativeGroupLawOfGrpObj_grpObjOverMk_one] using hone
  refine ⟨A₀, M₀, d, hM₀, ⟨n, P₀, hP₀⟩, hd, heM, ?_, ?_⟩
  · exact ⟨groupIsoOfPullbackOfOne A A₀ d hd hone'⟩
  · letI := L₀.grpObjOverMk
    change absolute p c₀ ≫ absolute p c₀ =
      (relativeGroupLawOfGrpObj (fixedField K p 2) c₀).schemeNsmul p
    rw [schemeNsmul_grpObjOverMk]
    exact descended_scalar_frobenius p A c₀ d hd τ.hom hp hτd L₀ hone

end AbelianVariety
end SupersingularCurves.Geometry
