/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PointedCotangent
import SupersingularCurves.Geometry.Frobenius

/-!
# The actual cotangent differential of relative Frobenius

Frobenius kills the infinitesimal component of every square-zero test
algebra. Consequently the independently defined relative Frobenius has
zero pointed cotangent differential at every rational point. This does
not require smoothness or perfection of the base field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.PointedCotangent
open CategoryTheory AlgebraicGeometry NeronModelInfra

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of K))
  (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  (V : Type u) [AddCommGroup V] [Module K V]
  [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

/-- The zero cotangent functional gives the actual constant square-zero
point at the specified rational point. -/
theorem pointsEquiv_zero_coe :
    (pointsEquiv c s V 0).1 = SquareZero.toBase K V ≫ s.1 := by
  have h := congrArg Subtype.val
    (pointsEquiv_map c s (0 : V →ₗ[K] V) (0 : Cotangent c s →ₗ[K] V))
  rw [LinearMap.zero_comp] at h
  rw [h, TangentPoints.map_coe]
  have hzero : SquareZero.specMap K (0 : V →ₗ[K] V) =
      SquareZero.toBase K V ≫ SquareZero.basePoint K V := by
    rw [SquareZero.specMap, SquareZero.toBase, SquareZero.basePoint, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext a <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [hzero, Category.assoc, (pointsEquiv c s V 0).2.2]

end SupersingularCurves.Geometry.PointedCotangent

namespace SupersingularCurves.Geometry.SchemeFrobenius
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p]
  (V : Type u) [AddCommGroup V] [Module K V]
  [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

local instance squareZeroCharP : CharP (TrivSqZeroExt K V) p :=
  charP_of_injective_algebraMap (algebraMap K (TrivSqZeroExt K V)).injective p

/-- Frobenius on a square-zero test scheme factors through its reduced
base point and the Frobenius of the ground field. -/
theorem squareZero_frobenius :
    Spec.map (CommRingCat.ofHom (frobenius (TrivSqZeroExt K V) p)) =
      SquareZero.toBase K V ≫ baseMap p K ≫ SquareZero.basePoint K V := by
  rw [SquareZero.toBase, baseMap, SquareZero.basePoint, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext x
  · simp [frobenius_def, TrivSqZeroExt.algebraMap_eq_inl]
  · change (x ^ p).snd = 0
    rw [TrivSqZeroExt.snd_pow]
    rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero K p, zero_smul]

variable {V}
variable {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K))
  (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)

/-- Every square-zero point has constant image under the actual relative
Frobenius. -/
theorem tangentPoint_relative (t : TangentPoints c s.1 V) :
    t.1 ≫ relative p c = SquareZero.toBase K V ≫ (twistedSection p c s).1 := by
  apply pullback.hom_ext
  · change (t.1 ≫ relative p c) ≫ projection p c = _
    rw [Category.assoc, relative_on_affine p c, squareZero_frobenius p V]
    simp only [Category.assoc, t.2.2, twistedSection, pullback.lift_fst]
  · change (t.1 ≫ relative p c) ≫ toBase p c = _
    rw [Category.assoc, relative_toBase, t.2.1]
    simp only [Category.assoc, twistedSection, pullback.lift_snd, Category.comp_id]

local instance cotangentOppositeModule : Module Kᵐᵒᵖ (PointedCotangent.Cotangent c s) :=
  Module.compHom _ (RingEquiv.toOpposite K).symm.toRingHom

local instance cotangentCentralScalar : IsCentralScalar K (PointedCotangent.Cotangent c s) :=
  ⟨fun _ _ => rfl⟩

/-- Relative Frobenius has zero differential on the actual local
cotangent spaces at every rational point. -/
theorem relative_differential_eq_zero :
    PointedCotangent.differential c s (relative p c) (relative_toBase p c)
      (section_relative p c s) = 0 := by
  apply (PointedCotangent.pointsEquiv (toBase p c) (twistedSection p c s)
    (PointedCotangent.Cotangent c s)).injective
  rw [PointedCotangent.differential, Equiv.apply_symm_apply]
  apply TangentPoints.ext
  rw [PointedCotangent.pointsEquiv_zero_coe]
  exact tangentPoint_relative p c s _

end SupersingularCurves.Geometry.SchemeFrobenius
