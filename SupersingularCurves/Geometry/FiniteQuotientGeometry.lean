/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianVariety

/-!
# Geometry inherited by actual finite quotients

Geometric connectedness descends through an actual surjective scheme
morphism. The proof applies connectedness of the source after each field
base change and the actual surjective pullback morphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FiniteQuotientGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {X Y S : Scheme.{u}}
variable (c : X ⟶ S) (d : Y ⟶ S) (q : X ⟶ Y) (hq : q ≫ d = c)

include hq in
/-- A surjective morphism from a geometrically connected scheme over a
base proves geometric connectedness of its actual target over that base. -/
theorem geometricallyConnected_of_surjective
    [GeometricallyConnected c] [Surjective q] : GeometricallyConnected d := by
  constructor
  apply (geometrically_iff_of_isClosedUnderIsomorphisms
    (P := fun Z : Scheme.{u} => ConnectedSpace Z) (f := d)).mpr
  intro L _ s
  let φ : pullback c s ⟶ pullback d s :=
    pullback.map c s d s q (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using hq.symm)
      (by simp only [Category.comp_id, Category.id_comp])
  let : Surjective φ := MorphismProperty.pullbackMap (P := @Surjective.{u})
    (inferInstance : Surjective q) (inferInstance : Surjective (𝟙 _))
    (by simpa only [Category.comp_id] using hq.symm)
    (by simp only [Category.comp_id, Category.id_comp])
  let : ConnectedSpace ↥(pullback c s) :=
    pullback_of_geometrically
      (GeometricallyConnected.geometrically_connectedSpace (f := c)) L s
  exact φ.surjective.connectedSpace φ.continuous

end SupersingularCurves.Geometry.FiniteQuotientGeometry
