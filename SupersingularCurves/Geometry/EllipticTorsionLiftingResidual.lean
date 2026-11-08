/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingAmbient
import SupersingularCurves.Geometry.FrobeniusSquareLineBundle
import SupersingularCurves.Geometry.RationalCotangentFrobenius

/-! # The actual semilinear residual automorphism when dV vanishes -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.TorsionLevels
open CategoryTheory AlgebraicGeometry SchemeFrobenius PerfectFieldVerschiebung

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
  (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p]

local instance : Smooth A.group.X.hom := SmoothOfRelativeDimension.smooth g A.group.X.hom

variable (hV : GroupScheme.verschiebungCotangent p A.group
  A.groupScheme_law_commutative = 0)

/-- The actual residual isomorphism constructed from vanishing dV. -/
def residualTwistIso : Twist p (toBase p A.group.X.hom) ≅ A.group.X.left :=
  Classical.choose (A.exists_frobenius_factor_iso_of_verschiebungCotangent_eq_zero p hV)

theorem residualTwistIso_factor :
    relative p (toBase p A.group.X.hom) ≫ (residualTwistIso A p hV).hom =
      verschiebung p A.group.X.hom (GroupScheme.law A.group)
        A.groupScheme_law_commutative :=
  (Classical.choose_spec
    (A.exists_frobenius_factor_iso_of_verschiebungCotangent_eq_zero p hV)).1

theorem residualTwistIso_over :
    (residualTwistIso A p hV).hom ≫ A.group.X.hom =
      toBase p (toBase p A.group.X.hom) :=
  (Classical.choose_spec
    (A.exists_frobenius_factor_iso_of_verschiebungCotangent_eq_zero p hV)).2

/-- An actual automorphism of the underlying scheme, semilinear over inverse
Frobenius squared, obtained by removing both base-change projections. -/
def residualAbsoluteIso : A.group.X.left ≅ A.group.X.left :=
  (asIso (doubleProjection p A.group.X.hom)).symm ≪≫ residualTwistIso A p hV

theorem residualAbsoluteIso_hom :
    (residualAbsoluteIso A p hV).hom =
      inv (doubleProjection p A.group.X.hom) ≫ (residualTwistIso A p hV).hom := rfl

/-- The scalar field action is inverse Frobenius squared. -/
theorem residualAbsoluteIso_over :
    (residualAbsoluteIso A p hV).hom ≫ A.group.X.hom =
      A.group.X.hom ≫ inv (baseMap p K) ≫ inv (baseMap p K) := by
  rw [residualAbsoluteIso_hom, Category.assoc, residualTwistIso_over]
  change inv (projection p (toBase p A.group.X.hom) ≫ projection p A.group.X.hom) ≫
    toBase p (toBase p A.group.X.hom) = _
  rw [IsIso.inv_comp]
  rw [Category.assoc, inverse_projection_over,
    ← Category.assoc, inverse_projection_over, Category.assoc]
  rw [inverse_baseMap]

/-- Actual ambient Verschiebung is absolute Frobenius followed by the
constructed residual semilinear automorphism. -/
theorem ambientVerschiebung_eq_absolute_residual :
    ambientVerschiebung A p =
      absolute p A.group.X.hom ≫ (residualAbsoluteIso A p hV).hom := by
  have h : absolute p A.group.X.hom ≫ inv (doubleProjection p A.group.X.hom) =
      inv (projection p A.group.X.hom) ≫ relative p (toBase p A.group.X.hom) := by
    apply (cancel_mono (doubleProjection p A.group.X.hom)).mp
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    simp only [doubleProjection, Category.assoc]
    rw [← Category.assoc (relative p (toBase p A.group.X.hom)), relative_projection]
    have hn := Scheme.frobenius_comp (projection p A.group.X.hom) p 1
      (Fact.out : p.Prime) (globalChar p (toBase p A.group.X.hom))
      (globalChar p A.group.X.hom)
    change absolute p (toBase p A.group.X.hom) ≫ projection p A.group.X.hom =
      projection p A.group.X.hom ≫ absolute p A.group.X.hom at hn
    rw [hn, IsIso.inv_hom_id_assoc]
  rw [residualAbsoluteIso_hom, ← Category.assoc, h, Category.assoc,
    residualTwistIso_factor]
  rfl

/-- The actual residual automorphism has the identity section with the
same inverse-Frobenius-square scalar action. -/
theorem residualAbsoluteIso_zero :
    (GroupScheme.zero A.group).1 ≫ (residualAbsoluteIso A p hV).hom =
      inv (baseMap p K) ≫ inv (baseMap p K) ≫ (GroupScheme.zero A.group).1 := by
  apply (cancel_epi (baseMap p K)).mp
  have hz := Scheme.frobenius_comp (GroupScheme.zero A.group).1 p 1
    (Fact.out : p.Prime) (Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero K p))
    (globalChar p A.group.X.hom)
  rw [baseMap_eq_absolute] at hz
  change baseMap p K ≫ (GroupScheme.zero A.group).1 =
    (GroupScheme.zero A.group).1 ≫ absolute p A.group.X.hom at hz
  rw [← Category.assoc, hz, Category.assoc,
    ← ambientVerschiebung_eq_absolute_residual, zero_ambientVerschiebung,
    IsIso.hom_inv_id_assoc]

end SupersingularCurves.Geometry.TorsionLevels
