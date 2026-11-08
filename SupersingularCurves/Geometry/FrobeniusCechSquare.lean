/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusCechSemilinear

/-!
# Two successive actual relative Frobenius pullbacks

Absolute Frobenius commutes with projection pullback on actual overlap
sections. Over a perfect field the two projection equivalences therefore
identify two successive relative Frobenius pullbacks with the square of
absolute Frobenius on the original Čech cohomology.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.SchemeFrobenius
open CategoryTheory AlgebraicGeometry InfinitesimalPicard

variable (p : ℕ) [Fact p.Prime] {K : Type u} [Field K] [CharP K p]
variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
variable (𝒱 : C.TwoAffineOpenCover)

/-- Absolute Frobenius commutes with the actual projection pullback on Čech H1. -/
theorem absoluteCech_projectionCech (q : CechH1 c 𝒱) :
    absoluteCech p (toBase p c) (twistedCover p c 𝒱) (projectionCech p c 𝒱 q) =
      projectionCech p c 𝒱 (absoluteCech p c 𝒱 q) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [projectionCech_mk, absoluteCech_mk, absoluteCech_mk, projectionCech_mk, map_pow]

variable [PerfectField K]

/-- The same naturality statement for the genuine semilinear equivalence. -/
theorem absoluteCech_projectionCechEquiv (q : CechH1 c 𝒱) :
    absoluteCech p (toBase p c) (twistedCover p c 𝒱)
        (projectionCechEquiv p c 𝒱 q) =
      projectionCechEquiv p c 𝒱 (absoluteCech p c 𝒱 q) :=
  absoluteCech_projectionCech p c 𝒱 q

/-- On doubly projected classes, the actual twofold relative pullback is the
square of the original absolute Frobenius. -/
theorem cechPullback_twice_projectionCechEquiv (q : CechH1 c 𝒱) :
    cechPullback p c 𝒱
      (cechPullback p (toBase p c) (twistedCover p c 𝒱)
        (projectionCechEquiv p (toBase p c) (twistedCover p c 𝒱)
          (projectionCechEquiv p c 𝒱 q))) =
      absoluteCech p c 𝒱 (absoluteCech p c 𝒱 q) := by
  rw [cechPullback_projectionCechEquiv, absoluteCech_projectionCechEquiv,
    cechPullback_projectionCechEquiv]

/-- Square-zero absolute Frobenius gives zero for the two actual relative
pullbacks, retaining both successive Frobenius twists. -/
theorem cechPullback_twice_eq_zero_of_absoluteCech_square_zero
    (h : ∀ q : CechH1 c 𝒱, absoluteCech p c 𝒱 (absoluteCech p c 𝒱 q) = 0)
    (q₂ : CechH1 (toBase p (toBase p c))
      (twistedCover p (toBase p c) (twistedCover p c 𝒱))) :
    cechPullback p c 𝒱
      (cechPullback p (toBase p c) (twistedCover p c 𝒱) q₂) = 0 := by
  obtain ⟨q₁, rfl⟩ :=
    (projectionCechEquiv p (toBase p c) (twistedCover p c 𝒱)).surjective q₂
  obtain ⟨q, rfl⟩ := (projectionCechEquiv p c 𝒱).surjective q₁
  rw [cechPullback_twice_projectionCechEquiv]
  exact h q

end SupersingularCurves.Geometry.SchemeFrobenius
