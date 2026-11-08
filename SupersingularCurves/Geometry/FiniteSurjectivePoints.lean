/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FiniteGeometricPoints
import SupersingularCurves.Geometry.GroupTranslationCotangent

/-! # Rational-point lifting through an actual finite surjective morphism -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FiniteSurjectivePoints
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of K)) (d : Y ⟶ Spec (CommRingCat.of K))
  (f : X ⟶ Y) (hf : f ≫ d = c) [IsFinite f] [Surjective f]

/-- The actual fibre is nonempty and finite over an algebraically closed
field, so it supplies a rational lift of every actual target point. -/
theorem pointMap_surjective :
    Function.Surjective (GroupTranslation.mapPoint f hf
      (t := 𝟙 (Spec (CommRingCat.of K)))) := by
  intro y
  let Z := pullback f y.1
  let r : Z ⟶ Spec (CommRingCat.of K) := pullback.snd f y.1
  have : IsFinite r := inferInstance
  have : Surjective r := inferInstance
  obtain ⟨z, _⟩ := r.surjective (IsLocalRing.closedPoint K)
  obtain ⟨t, _⟩ := FiniteGeometricPoints.exists_rationalPoint r z
  let x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c :=
    ⟨t.1 ≫ pullback.fst f y.1, by
      rw [← hf, ← Category.assoc, Category.assoc t.1, pullback.condition,
        Category.assoc, Category.assoc, y.2, Category.comp_id]
      exact t.2⟩
  refine ⟨x, Subtype.ext ?_⟩
  change (t.1 ≫ pullback.fst f y.1) ≫ f = y.1
  rw [Category.assoc, pullback.condition, ← Category.assoc, t.2, Category.id_comp]

end SupersingularCurves.Geometry.FiniteSurjectivePoints
