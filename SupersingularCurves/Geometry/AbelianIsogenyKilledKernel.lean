/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateQuotientDescent
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul

/-! # Actual isogenies from a scheme-theoretically bounded kernel

The annihilation hypothesis is imposed on every test scheme. The proof embeds
the actual identity fibre into the actual finite multiplication kernel; it
does not infer finiteness from the set of geometric points.+-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace SupersingularCurves.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open FrobeniusFactorGroup ScalarFrobeniusTate

namespace AbelianVariety
variable {K : Type u} [Field K] [IsAlgClosed K] {g h : ℕ}
variable (A : AbelianVariety K g) (B : AbelianVariety K h)

/-- A surjective genuine homomorphism whose entire kernel is annihilated by
a positive integer is a finite flat isogeny. -/
theorem isIsogeny_of_surjective_of_kernel_killed
    (f : A.group ⟶ B.group) (hfs : Surjective (underlyingScheme.map f))
    (n : ℕ) (hn : n ≠ 0)
    (hk : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x : SchemeHomOver t A.group.X.hom),
      pointMap (underlyingScheme.map f) f.hom.hom.w x = (GroupScheme.law B.group).one t →
      (GroupScheme.law A.group).nsmul t n x = (GroupScheme.law A.group).one t) :
    IsIsogeny f ∧ Flat (underlyingScheme.map f) := by
  let L := GroupScheme.law A.group
  let M := GroupScheme.law B.group
  let φ := underlyingScheme.map f
  let Z := pullback φ (M.one (𝟙 _)).1
  let j : Z ⟶ A.group.X.left := pullback.fst φ (M.one (𝟙 _)).1
  let s : Z ⟶ Spec (CommRingCat.of K) := pullback.snd φ (M.one (𝟙 _)).1
  have hj : j ≫ A.group.X.hom = s :=
    PointedCotangent.Fibre.inclusion_over A.group.X.hom φ f.hom.hom.w
  let x : SchemeHomOver s A.group.X.hom := ⟨j, hj⟩
  have hx : pointMap φ f.hom.hom.w x = M.one s := by
    apply Subtype.ext
    change j ≫ φ = (M.one s).1
    rw [show j ≫ φ = s ≫ (M.one (𝟙 _)).1 from pullback.condition]
    exact congrArg Subtype.val (M.one_natural (𝟙 _) s s (Category.comp_id s))
  have hkill : j ≫ L.schemeNsmul n = s ≫ (L.one (𝟙 _)).1 := by
    have H := congrArg Subtype.val (hk s x hx)
    rw [L.coe_nsmul_eq_comp_schemeNsmul] at H
    exact H.trans (congrArg Subtype.val
      (L.one_natural (𝟙 _) s s (Category.comp_id s))).symm
  let Tn := pullback (L.schemeNsmul n) (L.one (𝟙 _)).1
  let k : Z ⟶ Tn := pullback.lift j s hkill
  have hkfst : k ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 = j :=
    pullback.lift_fst _ _ _
  have hks : k ≫ pullback.snd (L.schemeNsmul n) (L.one (𝟙 _)).1 = s :=
    pullback.lift_snd _ _ _
  haveI : IsProper φ := by
    haveI : IsProper (φ ≫ B.group.X.hom) := f.hom.hom.w.symm ▸ A.proper
    exact IsProper.of_comp φ B.group.X.hom
  haveI : IsProper s := inferInstanceAs
    (IsProper (pullback.snd φ (M.one (𝟙 _)).1))
  haveI : IsFinite (L.schemeNsmul n) := (multiplication_isIsogeny A n hn).1
  haveI : IsProper k := by
    haveI : IsProper (k ≫ pullback.snd (L.schemeNsmul n) (L.one (𝟙 _)).1) :=
      hks.symm ▸ inferInstanceAs (IsProper s)
    exact IsProper.of_comp k (pullback.snd (L.schemeNsmul n) (L.one (𝟙 _)).1)
  haveI : Mono k := by
    haveI : Mono (k ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1) :=
      hkfst.symm ▸ inferInstanceAs (Mono j)
    exact mono_of_mono k (pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1)
  haveI : IsClosedImmersion k :=
    (IsClosedImmersion.iff_isProper_and_mono k).mpr ⟨inferInstance, inferInstance⟩
  haveI : IsFinite s := by
    rw [← hks]
    infer_instance
  obtain ⟨hfinite, hflat⟩ :=
    RelativeGroupLaw.isFinite_and_flat_of_surjective_of_isFinite_pullback_snd
      L A.groupScheme_law_commutative A.abelianSchemePropertyBundle
      M B.groupScheme_law_commutative B.abelianSchemePropertyBundle
      ⟨φ, f.hom.hom.w⟩ (pointMap_mul f) hfs inferInstance
  exact ⟨⟨hfinite, hfs⟩, hflat⟩

end AbelianVariety
end SupersingularCurves.Geometry
