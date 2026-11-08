/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.CechCurvePullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback_of_le

/-!
# Pullback of normalized line-bundle frames

The frame on a pulled-back invertible sheaf is normalized on the actual
pullback of the chosen local section. This fixes its transition function.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.CechGluingPullback
open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open P2MW.S_AlgebraicGeometry_RelPicard_exists_trivialModDeformations_map_H1_tensor_natural


variable {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules}

/-- Actual pullback of a local section, restricted to a smaller source open. -/
def sectionLE (U : Y.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ U) (s : Γ(L, U)) :
    Γ((Scheme.Modules.pullback f).obj L, W) :=
  ((Scheme.Modules.pullback f).obj L).presheaf.map (homOfLE h).op
    (Scheme.Modules.pullbackLocalSection f s)

theorem sectionLE_smul (U : Y.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ U)
    (a : Γ(Y, U)) (s : Γ(L, U)) :
    sectionLE f U W h (a • s) = (f.appLE U W h).hom a • sectionLE f U W h s := by
  unfold sectionLE
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.map_smul]
  rfl

/-- Restricting a pulled-back section is compatible with both covers. -/
theorem sectionLE_restrict {U U' : Y.Opens} {W W' : X.Opens}
    (hU : U' ≤ U) (hW : W' ≤ W) (h : W ≤ f ⁻¹ᵁ U) (h' : W' ≤ f ⁻¹ᵁ U')
    (s : Γ(L, U)) :
    ((Scheme.Modules.pullback f).obj L).presheaf.map (homOfLE hW).op
        (sectionLE f U W h s) =
      sectionLE f U' W' h' (L.presheaf.map (homOfLE hU).op s) := by
  unfold sectionLE
  rw [← Scheme.Modules.map_homOfLE_pullbackLocalSection]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The pullback of a local basis is a basis, with a specified normalization. -/
theorem exists_frame (hL : Scheme.Modules.IsInvertible L)
    (U : Y.Opens) (hU : IsAffineOpen U) (W : X.Opens) (hW : IsAffineOpen W)
    (h : W ≤ f ⁻¹ᵁ U) (e : Γ(L, U) ≃ₗ[Γ(Y, U)] Γ(Y, U)) :
    ∃ E : Γ((Scheme.Modules.pullback f).obj L, W) ≃ₗ[Γ(X, W)] Γ(X, W),
      E (sectionLE f U W h (e.symm 1)) = 1 := by
  letI := (f.appLE U W h).hom.toAlgebra
  obtain ⟨β, hβ⟩ := hL.exists_baseChange_sections_linearEquiv_pullback_of_le f U hU W hW h
  let E := β.symm.trans ((e.baseChange Γ(Y, U) Γ(X, W)).trans
    (TensorProduct.AlgebraTensorModule.rid Γ(Y, U) Γ(X, W) Γ(X, W)))
  refine ⟨E, ?_⟩
  change (TensorProduct.AlgebraTensorModule.rid Γ(Y, U) Γ(X, W) Γ(X, W))
    ((e.baseChange Γ(Y, U) Γ(X, W)) (β.symm (sectionLE f U W h (e.symm 1)))) = 1
  rw [show sectionLE f U W h (e.symm 1) = β (1 ⊗ₜ e.symm 1) from (hβ _).symm,
    LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul,
    LinearEquiv.apply_symm_apply, TensorProduct.AlgebraTensorModule.rid_tmul]
  simp

private theorem expand_in_frame {B M : Type u} [CommRing B] [AddCommGroup M]
    [Module B M] (e : M ≃ₗ[B] B) (η : M) (hη : e η = 1) (x : M) :
    x = e x • η := by
  apply e.injective
  rw [map_smul, hη, smul_eq_mul, mul_one]

variable {K : Type u} [CommRing K]
variable {cX : X ⟶ Spec (CommRingCat.of K)} {cY : Y ⟶ Spec (CommRingCat.of K)}
variable (hf : f ≫ cY = cX) (𝒰 : X.TwoAffineOpenCover) (𝒱 : Y.TwoAffineOpenCover)
variable (h0 : 𝒰.U0 ≤ f ⁻¹ᵁ 𝒱.U0) (h1 : 𝒰.U1 ≤ f ⁻¹ᵁ 𝒱.U1)

/-- Pulling back a genuinely glued invertible sheaf pulls back its transition
unit by the actual map on overlap sections. -/
theorem gluedBy_pullback (hL : Scheme.Modules.IsInvertible L)
    (t : (𝒱.cover cY).A01ˣ) (ht : P2mTJ2.GluedBy 𝒱 cY L t) :
    P2mTJ2.GluedBy 𝒰 cX ((Scheme.Modules.pullback f).obj L)
      (Units.map (CechCurvePullback.appAlgHom f hf (𝒱.U0 ⊓ 𝒱.U1)
        (𝒰.U0 ⊓ 𝒰.U1) (CechCurvePullback.overlap_le f 𝒰 𝒱 h0 h1)).toMonoidHom t) := by
  obtain ⟨e0, e1, e01, he0, he1⟩ := ht
  let g0 := e0.symm 1
  let g1 := e1.symm 1
  let g01 := e01.symm 1
  have hr0 : (𝒱.sectionsOf cY L).r0 g0 = g01 := by
    apply e01.injective
    rw [he0]
    simp [g0, g01]
  have hr1 : (𝒱.sectionsOf cY L).r1 g1 = (t : (𝒱.cover cY).A01) • g01 := by
    apply e01.injective
    rw [he1, map_smul]
    simp [g1, g01]
  let h01 := CechCurvePullback.overlap_le f 𝒰 𝒱 h0 h1
  let η0 := sectionLE f 𝒱.U0 𝒰.U0 h0 g0
  let η1 := sectionLE f 𝒱.U1 𝒰.U1 h1 g1
  let η01 := sectionLE f (𝒱.U0 ⊓ 𝒱.U1) (𝒰.U0 ⊓ 𝒰.U1) h01 g01
  obtain ⟨E0, hE0⟩ := exists_frame f hL 𝒱.U0 𝒱.isAffineOpen_U0
    𝒰.U0 𝒰.isAffineOpen_U0 h0 e0
  obtain ⟨E1, hE1⟩ := exists_frame f hL 𝒱.U1 𝒱.isAffineOpen_U1
    𝒰.U1 𝒰.isAffineOpen_U1 h1 e1
  obtain ⟨E01, hE01⟩ := exists_frame f hL (𝒱.U0 ⊓ 𝒱.U1) 𝒱.isAffineOpen_inf
    (𝒰.U0 ⊓ 𝒰.U1) 𝒰.isAffineOpen_inf h01 e01
  change E0 η0 = 1 at hE0
  change E1 η1 = 1 at hE1
  change E01 η01 = 1 at hE01
  let S := 𝒰.sectionsOf cX ((Scheme.Modules.pullback f).obj L)
  have hr0' : S.r0 η0 = η01 := by
    change ((Scheme.Modules.pullback f).obj L).presheaf.map
      (homOfLE inf_le_left).op (sectionLE f _ _ h0 g0) = _
    rw [sectionLE_restrict f inf_le_left inf_le_left h0 h01]
    exact congrArg (sectionLE f _ _ h01) hr0
  have hr1' : S.r1 η1 = (f.appLE _ _ h01).hom (t : (𝒱.cover cY).A01) • η01 := by
    change ((Scheme.Modules.pullback f).obj L).presheaf.map
      (homOfLE inf_le_right).op (sectionLE f _ _ h1 g1) = _
    rw [sectionLE_restrict f inf_le_right inf_le_right h1 h01]
    change sectionLE f _ _ h01 ((𝒱.sectionsOf cY L).r1 g1) = _
    rw [hr1, sectionLE_smul]
  change ((Scheme.Modules.pullback f).obj L).presheaf.map
    (homOfLE inf_le_left).op η0 = η01 at hr0'
  change ((Scheme.Modules.pullback f).obj L).presheaf.map
    (homOfLE inf_le_right).op η1 = (f.appLE _ _ h01).hom (t : (𝒱.cover cY).A01) • η01 at hr1'
  refine ⟨E0, E1, E01, ?_, ?_⟩
  · change ∀ x : Γ((Scheme.Modules.pullback f).obj L, 𝒰.U0),
      E01 (((Scheme.Modules.pullback f).obj L).presheaf.map (homOfLE inf_le_left).op x) =
        (X.presheaf.map (homOfLE inf_le_left).op).hom (E0 x)
    intro x
    rw [expand_in_frame E0 η0 hE0 x, Scheme.Modules.map_smul, hr0', map_smul, hE01]
    rw [map_smul, hE0, smul_eq_mul, mul_one, smul_eq_mul, mul_one]
  · change ∀ x : Γ((Scheme.Modules.pullback f).obj L, 𝒰.U1),
      E01 (((Scheme.Modules.pullback f).obj L).presheaf.map (homOfLE inf_le_right).op x) =
        (f.appLE _ _ h01).hom (t : (𝒱.cover cY).A01) *
          (X.presheaf.map (homOfLE inf_le_right).op).hom (E1 x)
    intro x
    rw [expand_in_frame E1 η1 hE1 x, Scheme.Modules.map_smul, hr1', map_smul, map_smul, hE01]
    rw [map_smul, hE1]
    simp only [smul_eq_mul, mul_one]
    exact mul_comm _ _

end SupersingularCurves.Geometry.CechGluingPullback
