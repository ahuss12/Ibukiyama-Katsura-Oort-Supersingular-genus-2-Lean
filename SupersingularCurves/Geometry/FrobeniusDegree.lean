/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.Frobenius
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_finrank_eq_pow_of_isPullback_frobenius

/-!
# Scheme-theoretic degree of actual relative Frobenius

For a smooth scheme of relative dimension `g` over a perfect field, the
constructed relative Frobenius has constant finite-flat rank `p^g`. The proof
uses genuine smooth local coordinates and finite-flat module rank, not a
count of rational points.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.SchemeFrobenius
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-- The actual relative Frobenius has scheme-theoretic degree `p^g`. -/
theorem relative_finrank (p : ℕ) [Fact p.Prime]
    {K : Type u} [Field K] [PerfectField K] [CharP K p]
    {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K))
    (g : ℕ) [SmoothOfRelativeDimension g c] (y : Twist p c) :
    (relative p c).finrank y = p ^ g :=
  SmoothOfRelativeDimension.finrank_eq_pow_of_isPullback_frobenius
    K p c (toBase p c) g (projection p c)
    (IsPullback.of_hasPullback c (baseMap p K))
    (relative p c) (relative_toBase p c) (relative_on_affine p c) y

end SupersingularCurves.Geometry.SchemeFrobenius
