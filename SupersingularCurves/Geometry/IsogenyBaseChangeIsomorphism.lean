/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianVariety

/-!
# Isogenies and base change along a field isomorphism

The scalar pullback of a group-scheme morphism is an actual isogeny exactly
when the original morphism is, provided the structural field map is bijective.
Both pullback projections are scheme isomorphisms, so the underlying morphisms
are conjugate. Finiteness and surjectivity are transferred by these scheme
isomorphisms; no pointwise replacement of the isogeny condition is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Actual finite-surjective group morphisms are invariant under pullback
along an isomorphism of the ground fields. -/
theorem isIsogeny_baseChange_iff (L : Type u) [Field L] [Algebra K L]
    (h : Function.Bijective (algebraMap K L))
    {G H : GroupScheme K} (f : G ⟶ H) :
    IsIsogeny (((Over.pullback (Spec.map
      (CommRingCat.ofHom (algebraMap K L)))).mapGrp).map f) ↔ IsIsogeny f := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let : IsIso (CommRingCat.ofHom (algebraMap K L)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr h
  have : IsIso b := by dsimp [b]; infer_instance
  let F := Over.pullback b
  let f' := F.mapGrp.map f
  let prG := pullback.fst G.X.hom b
  let prH := pullback.fst H.X.hom b
  have : IsIso prG := by dsimp [prG]; infer_instance
  have : IsIso prH := by dsimp [prH]; infer_instance
  have hcomm : underlyingScheme.map f' ≫ prH = prG ≫ underlyingScheme.map f := by
    change ((Over.pullback b).map f.hom.hom).left ≫ pullback.fst H.X.hom b =
      pullback.fst G.X.hom b ≫ f.hom.hom.left
    simp
  have hforward : underlyingScheme.map f' =
      prG ≫ underlyingScheme.map f ≫ inv prH := by
    apply (cancel_mono prH).mp
    simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using hcomm
  have hbackward : underlyingScheme.map f =
      inv prG ≫ underlyingScheme.map f' ≫ prH := by
    rw [hcomm, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  change IsIsogeny f' ↔ IsIsogeny f
  constructor
  · intro hf
    let := hf.1
    let := hf.2
    unfold IsIsogeny
    rw [hbackward]
    exact ⟨inferInstance, inferInstance⟩
  · intro hf
    let := hf.1
    let := hf.2
    unfold IsIsogeny
    rw [hforward]
    exact ⟨inferInstance, inferInstance⟩

end SupersingularCurves.Geometry
