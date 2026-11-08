/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PointedCotangent
import SupersingularCurves.Geometry.SmoothDifferentialRoots

/-!
# Zero pointed cotangent maps and universal differentials

This module connects the actual pointed-scheme cotangent differential with
the universal differential of the actual local-ring map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.PointedCotangent
open CategoryTheory AlgebraicGeometry NeronModelInfra
open P2MW.S_AlgebraicGeometry_Scheme_exists_tangentPoints_equiv_linearMap_cotangentSpace

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of K)) (d : Y ⟶ Spec (CommRingCat.of K))
  (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  (f : X ⟶ Y) (hf : f ≫ d = c)

/-- The rational image point under the given base-preserving morphism. -/
def imagePoint : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) d :=
  ⟨s.1 ≫ f, by rw [Category.assoc, hf, s.2]⟩

/-- The actual local-ring map, retaining its ground-field algebra structure. -/
def pointedStalkMap : Stalk d (imagePoint c d s f hf) →ₐ[K] Stalk c s where
  __ := (f.stalkMap (s.1.base (IsLocalRing.closedPoint K))).hom
  commutes' a := by
    change (f.stalkMap _).hom
      ((Y.presheaf.germ ⊤ _ trivial).hom
        (d.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))) = _
    rw [Scheme.Hom.germ_stalkMap_apply]
    change (X.presheaf.germ ⊤ (s.1.base (IsLocalRing.closedPoint K)) trivial).hom
      ((f.app ⊤).hom (d.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))) = _
    change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ d.appTop ≫
      f.appTop ≫ X.presheaf.germ ⊤ _ trivial).hom a = _
    rw [← Category.assoc d.appTop, ← Scheme.Hom.comp_appTop, hf]
    rfl

/-- The actual local-ring map respects the rational-point augmentations. -/
theorem augmentation_pointedStalkMap
    (b : Stalk d (imagePoint c d s f hf)) :
    augmentation c s (pointedStalkMap c d s f hf b) =
      augmentation d (imagePoint c d s f hf) b := by
  change (f.stalkMap _ ≫ Scheme.stalkClosedPointTo s.1).hom b =
    (Scheme.stalkClosedPointTo (s.1 ≫ f)).hom b
  rw [Scheme.stalkClosedPointTo_comp]
  rfl

private theorem liftHom_zero {Z : Scheme.{u}}
    (e : Z ⟶ Spec (CommRingCat.of K))
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) e)
    (N : Type u) [AddCommGroup N] [Module K N]
    [Module Kᵐᵒᵖ N] [IsCentralScalar K N]
    (b : Stalk e a) :
    P2mTJ1.liftHom (P2mTJ1.π_algebraMap (fun _ => rfl) a.2)
      (0 : (RingHom.ker (augmentation e a)).Cotangent →ₗ[K] N) b =
        TrivSqZeroExt.inl (augmentation e a b) := by
  let ψ : Stalk e a →ₐ[K] TrivSqZeroExt K N :=
    (IsScalarTower.toAlgHom K K (TrivSqZeroExt K N)).comp (augmentation e a)
  have hψ := P2mTJ1.liftHom_unique
    (P2mTJ1.π_algebraMap (fun _ => rfl) a.2)
    (0 : (RingHom.ker (augmentation e a)).Cotangent →ₗ[K] N) ψ
    (fun b => by simp [ψ, TrivSqZeroExt.algebraMap_eq_inl]; rfl)
    (fun b => by simp [ψ, TrivSqZeroExt.algebraMap_eq_inl])
  rw [← hψ]
  rfl

/-- Zero actual cotangent differential makes every cotangent functional
on the source lift constant after composition with the local-ring map. -/
theorem liftHom_pointedStalkMap_of_differential_eq_zero
    (hdf : differential c s (z := imagePoint c d s f hf) f hf rfl = 0)
    (N : Type u) [AddCommGroup N] [Module K N]
    [Module Kᵐᵒᵖ N] [IsCentralScalar K N]
    (l : Cotangent c s →ₗ[K] N)
    (b : Stalk d (imagePoint c d s f hf)) :
    (P2mTJ1.liftHom (P2mTJ1.π_algebraMap (fun _ => rfl) s.2)
      (l ∘ₗ (augmentationEquiv c s).symm.toLinearMap)
      (pointedStalkMap c d s f hf b)).snd = 0 := by
  let z := imagePoint c d s f hf
  let ψX := P2mTJ1.liftHom (P2mTJ1.π_algebraMap (fun _ => rfl) s.2)
    (l ∘ₗ (augmentationEquiv c s).symm.toLinearMap)
  let ψY := P2mTJ1.liftHom (P2mTJ1.π_algebraMap (fun _ => rfl) z.2)
    (0 : (RingHom.ker (augmentation d z)).Cotangent →ₗ[K] N)
  have ht := differential_action c s f hf (z := z) rfl l
  rw [hdf, LinearMap.comp_zero] at ht
  have ht' := congrArg Subtype.val ht
  change P2mTJ1.Λ₀ z.1 (CommRingCat.ofHom ψY.toRingHom) =
    P2mTJ1.Λ₀ s.1 (CommRingCat.ofHom ψX.toRingHom) ≫ f at ht'
  have hnat : P2mTJ1.Λ₀ s.1 (CommRingCat.ofHom ψX.toRingHom) ≫ f =
      P2mTJ1.Λ₀ z.1
        (CommRingCat.ofHom (ψX.comp (pointedStalkMap c d s f hf)).toRingHom) := by
    dsimp only [P2mTJ1.Λ₀]
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc]
    rfl
  have hfst : ∀ r, ((ψX.comp (pointedStalkMap c d s f hf)) r).fst = P2mTJ1.π z.1 r := by
    intro r
    rw [AlgHom.comp_apply, P2mTJ1.fst_liftHom]
    exact augmentation_pointedStalkMap c d s f hf r
  let : IsLocalHom (CommRingCat.ofHom ψY.toRingHom).hom :=
    P2mTJ1.isLocalHom_of_fst_eq _ (P2mTJ1.fst_liftHom _ _)
  let : IsLocalHom
      (CommRingCat.ofHom (ψX.comp (pointedStalkMap c d s f hf)).toRingHom).hom :=
    P2mTJ1.isLocalHom_of_fst_eq _ hfst
  have he := P2mTJ1.Λ₀_injective (ht'.trans hnat)
  have hb := congrArg (fun φ : Stalk d z ⟶ CommRingCat.of (TrivSqZeroExt K N) =>
    (φ.hom b).snd) he
  change (ψY b).snd = _ at hb
  rw [liftHom_zero] at hb
  exact hb.symm

/-- A zero cotangent differential sends the target maximal ideal into
the square of the source maximal ideal. -/
theorem pointedStalkMap_mem_sq_of_differential_eq_zero
    (hdf : differential c s (z := imagePoint c d s f hf) f hf rfl = 0)
    (b : Stalk d (imagePoint c d s f hf))
    (hb : b ∈ IsLocalRing.maximalIdeal (Stalk d (imagePoint c d s f hf))) :
    pointedStalkMap c d s f hf b ∈ IsLocalRing.maximalIdeal (Stalk c s) ^ 2 := by
  let : Module Kᵐᵒᵖ (Cotangent c s) :=
    Module.compHom _ (RingEquiv.toOpposite K).symm.toRingHom
  let : IsCentralScalar K (Cotangent c s) := ⟨fun _ _ => rfl⟩
  have hb0 : augmentation d (imagePoint c d s f hf) b = 0 := by
    exact RingHom.mem_ker.mp ((ker_augmentation d _).symm ▸ hb)
  have hmem : pointedStalkMap c d s f hf b ∈ RingHom.ker (augmentation c s) := by
    rw [RingHom.mem_ker, augmentation_pointedStalkMap, hb0]
  have hz := liftHom_pointedStalkMap_of_differential_eq_zero c d s f hf hdf
    (Cotangent c s) LinearMap.id b
  rw [P2mTJ1.snd_liftHom _ _ ⟨_, hmem⟩] at hz
  change (augmentationEquiv c s).symm
    ((RingHom.ker (augmentation c s)).toCotangent ⟨_, hmem⟩) = 0 at hz
  have hz' := (augmentationEquiv c s).symm.injective (hz.trans (map_zero _).symm)
  have hm := ((RingHom.ker (augmentation c s)).toCotangent_eq_zero ⟨_, hmem⟩).mp hz'
  change pointedStalkMap c d s f hf b ∈ RingHom.ker (augmentation c s) ^ 2 at hm
  rwa [ker_augmentation] at hm

/-- The image of any germ differs from its residue constant by an element
of the square of the actual maximal ideal. -/
theorem pointedStalkMap_sub_residue_mem_sq_of_differential_eq_zero
    (hdf : differential c s (z := imagePoint c d s f hf) f hf rfl = 0)
    (b : Stalk d (imagePoint c d s f hf)) :
    pointedStalkMap c d s f hf b -
      algebraMap K (Stalk c s) (augmentation d (imagePoint c d s f hf) b) ∈
        IsLocalRing.maximalIdeal (Stalk c s) ^ 2 := by
  have hb : b - algebraMap K _ (augmentation d (imagePoint c d s f hf) b) ∈
      IsLocalRing.maximalIdeal (Stalk d (imagePoint c d s f hf)) := by
    rw [← ker_augmentation, RingHom.mem_ker, map_sub, AlgHom.commutes,
      Algebra.algebraMap_self_apply, sub_self]
  simpa only [map_sub, AlgHom.commutes] using
    pointedStalkMap_mem_sq_of_differential_eq_zero c d s f hf hdf _ hb

/-- Universal differentiation sends I² into I times the differential module. -/
theorem D_mem_smul_of_mem_sq {S : Type u} [CommRing S] [Algebra K S]
    (I : Ideal S) {b : S} (hb : b ∈ I ^ 2) :
    KaehlerDifferential.D K S b ∈
      I • (⊤ : Submodule S (KaehlerDifferential K S)) := by
  rw [pow_two] at hb
  refine Submodule.mul_induction_on hb (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  ·
    rw [Derivation.leibniz]
    exact Submodule.add_mem _
      (Submodule.smul_mem_smul hx (Submodule.mem_top))
      (Submodule.smul_mem_smul hy (Submodule.mem_top))
  ·
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- Vanishing of the actual pointed cotangent map implies vanishing of the
universal differential in the residue fibre of the actual source stalk. -/
theorem D_stalkMap_mem_maximalIdeal_smul_of_differential_eq_zero
    (hdf : differential c s (z := imagePoint c d s f hf) f hf rfl = 0)
    (b : Stalk d (imagePoint c d s f hf)) :
    KaehlerDifferential.D K (Stalk c s)
      ((f.stalkMap (s.1.base (IsLocalRing.closedPoint K))).hom b) ∈
        IsLocalRing.maximalIdeal (Stalk c s) •
          (⊤ : Submodule (Stalk c s) (KaehlerDifferential K (Stalk c s))) := by
  have h := D_mem_smul_of_mem_sq (K := K) (IsLocalRing.maximalIdeal (Stalk c s))
    (pointedStalkMap_sub_residue_mem_sq_of_differential_eq_zero c d s f hf hdf b)
  have he : pointedStalkMap c d s f hf b =
      (f.stalkMap (s.1.base (IsLocalRing.closedPoint K))).hom b := rfl
  rw [he] at h
  simpa only [map_sub, Derivation.map_algebraMap, sub_zero] using h

end SupersingularCurves.Geometry.PointedCotangent
