/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AffineInvariantDerivation

/-! # Actual affine square-zero points and the coordinate augmentation cotangent -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.PointedCotangent.AffineAugmentation
open CategoryTheory AlgebraicGeometry NeronModelInfra

variable {K : Type u} [Field K] {H : Type u} [CommRing H] [Algebra K H]
variable (π : H →ₐ[K] K)

abbrev structureMap := AffineInvariantDerivation.toBase K H

/-- The actual rational point defined by the augmentation. -/
def sectionPoint : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (structureMap (H := H)) :=
  ⟨Spec.map (CommRingCat.ofHom π.toRingHom),
    (AffineInvariantDerivation.point K π).2.trans (Spec.map_id _)⟩

abbrev CoordinateCotangent := (RingHom.ker π).Cotangent

variable {V : Type u} [AddCommGroup V] [Module K V]
  [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
variable {W : Type u} [AddCommGroup W] [Module K W]
  [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

/-- The unique actual algebra map with the specified first-order part. -/
def lift (l : CoordinateCotangent π →ₗ[K] V) : H →ₐ[K] TrivSqZeroExt K V :=
  (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap π l).choose

theorem fst_lift (l : CoordinateCotangent π →ₗ[K] V) (a : H) :
    (lift π l a).fst = π a :=
  (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap π l).choose_spec.1.1 a

theorem snd_lift (l : CoordinateCotangent π →ₗ[K] V) (a : RingHom.ker π) :
    (lift π l a).snd = l ((RingHom.ker π).toCotangent a) :=
  (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap π l).choose_spec.1.2 a

theorem lift_unique (l : CoordinateCotangent π →ₗ[K] V)
    (ψ : H →ₐ[K] TrivSqZeroExt K V) (hf : ∀ a, (ψ a).fst = π a)
    (hs : ∀ a : RingHom.ker π, (ψ a).snd = l ((RingHom.ker π).toCotangent a)) :
    ψ = lift π l :=
  (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap π l).unique ⟨hf, hs⟩
    (AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap π l).choose_spec.1

/-- A coordinate cotangent functional gives its actual affine tangent point. -/
def coordinatePoint (l : CoordinateCotangent π →ₗ[K] V) :
    TangentPoints (structureMap (H := H)) (sectionPoint π).1 V :=
  ⟨Spec.map (CommRingCat.ofHom (lift π l).toRingHom),
    (AffineInvariantDerivation.point K (lift π l)).2, by
      change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K V).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (lift π l).toRingHom) =
          Spec.map (CommRingCat.ofHom π.toRingHom)
      rw [← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      ext a
      exact fst_lift π l a⟩

theorem coordinatePoint_injective : Function.Injective (coordinatePoint π (V := V)) := by
  intro f g h
  have he := Spec.map_injective (congrArg Subtype.val h)
  have hlift : lift π f = lift π g := by
    apply AlgHom.ext
    intro a
    exact congrArg (fun e : CommRingCat.of H ⟶ CommRingCat.of (TrivSqZeroExt K V) => e.hom a) he
  ext x
  obtain ⟨a, rfl⟩ := (RingHom.ker π).toCotangent_surjective x
  rw [← snd_lift, ← snd_lift, hlift]

theorem coordinatePoint_surjective : Function.Surjective (coordinatePoint π (V := V)) := by
  intro t
  let ψ := AffineInvariantDerivation.coordinates K
    (⟨t.1, t.2.1⟩ : SchemeHomOver (AffineInvariantDerivation.toBase K (TrivSqZeroExt K V))
      (structureMap (H := H)))
  have hψ : Spec.map (CommRingCat.ofHom ψ.toRingHom) = t.1 :=
    congrArg Subtype.val (AffineInvariantDerivation.point_coordinates K ⟨t.1, t.2.1⟩)
  have hf : ∀ a, (ψ a).fst = π a := by
    have ht := t.2.2
    rw [← hψ] at ht
    change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K V).toRingHom) ≫
      Spec.map (CommRingCat.ofHom ψ.toRingHom) = Spec.map (CommRingCat.ofHom π.toRingHom) at ht
    rw [← Spec.map_comp] at ht
    have hh := Spec.map_injective ht
    intro a
    exact congrArg (fun f : CommRingCat.of H ⟶ CommRingCat.of K => f.hom a) hh
  obtain ⟨l, hl⟩ := AlgHom.exists_cotangent_linearMap_of_fst_eq π ψ hf
  have he := lift_unique π l ψ hf hl
  refine ⟨l, TangentPoints.ext ?_⟩
  change Spec.map (CommRingCat.ofHom (lift π l).toRingHom) = t.1
  rw [← he, hψ]

theorem lift_map (φ : V →ₗ[K] W) (l : CoordinateCotangent π →ₗ[K] V) :
    (TrivSqZeroExt.map φ).comp (lift π l) = lift π (φ ∘ₗ l) := by
  apply lift_unique
  · intro a
    rw [AlgHom.comp_apply, TrivSqZeroExt.fst_map, fst_lift]
  · intro a
    rw [AlgHom.comp_apply, TrivSqZeroExt.snd_map, snd_lift, LinearMap.comp_apply]

theorem coordinatePoint_map (φ : V →ₗ[K] W) (l : CoordinateCotangent π →ₗ[K] V) :
    coordinatePoint π (φ ∘ₗ l) = (coordinatePoint π l).map φ := by
  apply TangentPoints.ext
  change Spec.map (CommRingCat.ofHom (lift π (φ ∘ₗ l)).toRingHom) =
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map φ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (lift π l).toRingHom)
  rw [← Spec.map_comp, ← lift_map]
  rfl

end SupersingularCurves.Geometry.PointedCotangent.AffineAugmentation
