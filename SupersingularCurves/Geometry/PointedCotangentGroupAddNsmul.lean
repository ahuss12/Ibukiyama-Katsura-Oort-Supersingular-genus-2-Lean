/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PointedCotangentGroupAdd
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

/-! # The actual multiplication map acts by its integer on the cotangent space -/
set_option autoImplicit false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.PointedCotangent
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

variable {K : Type u} [Field K] {X : Scheme.{u}}
variable {c : X ⟶ Spec (CommRingCat.of K)} (L : RelativeGroupLaw K c)

/-- Genuine multiplication preserves the actual group identity. -/
theorem schemeNsmul_point (n : ℕ) :
    (L.one (𝟙 _)).1 ≫ L.schemeNsmul n = (L.one (𝟙 _)).1 := by
  have h := L.nsmul_natural c (𝟙 _) (L.one (𝟙 _)).1
    (L.one (𝟙 _)).2 n RelativeGroupLaw.idPoint
  have hh : schemeHomOverComp (L.one (𝟙 _)).1 (L.one (𝟙 _)).2
      RelativeGroupLaw.idPoint = L.one (𝟙 _) := by
    apply Subtype.ext
    exact Category.comp_id _
  rw [hh, L.nsmul_unit] at h
  exact congrArg Subtype.val h

/-- Differentiate the genuine scheme multiplication map, with no supplied
linear action or identification of tangent spaces. -/
theorem differential_schemeNsmul (n : ℕ) :
    differential c (L.one (𝟙 _)) (L.schemeNsmul n) (L.schemeNsmul_over n)
      (schemeNsmul_point L n) =
        (n : K) • (LinearMap.id : Cotangent c (L.one (𝟙 _)) →ₗ[K]
          Cotangent c (L.one (𝟙 _))) := by
  induction n with
  | zero =>
      simpa only [RelativeGroupLaw.schemeNsmul, RelativeGroupLaw.nsmul_zero,
        Nat.cast_zero, zero_smul] using
        (differential_law_one L (L.one (𝟙 _)))
  | succ n ih =>
      change differential c (L.one (𝟙 _))
        (L.mul c (L.nsmul c n RelativeGroupLaw.idPoint) RelativeGroupLaw.idPoint).1
        _ _ = _
      rw [differential_law_mul L (L.one (𝟙 _))
        (L.nsmul c n RelativeGroupLaw.idPoint) RelativeGroupLaw.idPoint
        (schemeNsmul_point L n) (Category.comp_id _)]
      rw [show differential c (L.one (𝟙 _))
        (L.nsmul c n RelativeGroupLaw.idPoint).1 _ _ =
          (n : K) • LinearMap.id from ih, differential_id]
      simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]

end SupersingularCurves.Geometry.PointedCotangent
