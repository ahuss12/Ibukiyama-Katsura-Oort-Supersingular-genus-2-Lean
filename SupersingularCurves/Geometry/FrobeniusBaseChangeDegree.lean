/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.VerschiebungNaturality
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Actual base change of morphisms under field Frobenius

The previously constructed map of Frobenius twists is an actual pullback
of the original morphism. Finite flat degree and surjectivity therefore
persist, including for the descended quotient isogenies.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.SchemeFrobenius
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p]
variable {X Y : Scheme.{u}} {c : X ⟶ Spec (CommRingCat.of K)}
  {d : Y ⟶ Spec (CommRingCat.of K)}
variable (f : X ⟶ Y) (hf : f ≫ d = c)

/-- The actual Frobenius-twisted map is a base change of the original map. -/
theorem map_isPullback :
    IsPullback (map p f hf) (projection p c) (projection p d) f := by
  have houter : IsPullback (map p f hf ≫ toBase p d) (projection p c)
      (baseMap p K) (f ≫ d) := by
    rw [map_toBase p f hf, hf]
    exact (IsPullback.of_hasPullback c (baseMap p K)).flip
  exact houter.of_right (map_projection p f hf)
    (IsPullback.of_hasPullback d (baseMap p K)).flip

instance map_isFinite [IsFinite f] : IsFinite (map p f hf) :=
  MorphismProperty.of_isPullback (P := @IsFinite) (map_isPullback p f hf).flip inferInstance

instance map_flat [Flat f] : Flat (map p f hf) :=
  MorphismProperty.of_isPullback (P := @Flat) (map_isPullback p f hf).flip inferInstance

instance map_surjective [Surjective f] : Surjective (map p f hf) :=
  MorphismProperty.of_isPullback (P := @Surjective) (map_isPullback p f hf).flip inferInstance

/-- Finite-flat rank is unchanged by actual Frobenius base change. -/
theorem map_finrank [IsFinite f] [Flat f] (y : Twist p d) :
    (map p f hf).finrank y = f.finrank (projection p d y) :=
  Scheme.Hom.finrank_of_isPullback _ _ _ _ (map_isPullback p f hf).flip y

/-- A constant finite-flat degree remains constant on the actual twist. -/
theorem map_finrank_eq_const [IsFinite f] [Flat f] (n : ℕ)
    (h : ∀ y, f.finrank y = n) (y : Twist p d) :
    (map p f hf).finrank y = n := by
  rw [map_finrank]
  exact h _

end SupersingularCurves.Geometry.SchemeFrobenius
