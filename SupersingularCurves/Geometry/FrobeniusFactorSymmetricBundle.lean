/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusSquareLineBundle
import SupersingularCurves.Geometry.VerschiebungFrobeniusCriterion
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_zpow_iso_tensorPow_of_symmetric

/-!
# Symmetric line bundles and the actual residual Frobenius isomorphism

When V factors through relative Frobenius, the residual map preserves the
p²-th tensor power of any actual symmetric invertible sheaf, relative to the
actual double projection. This is a sheaf isomorphism, proved from the actual
multiplication-by-p identity and the absolute Frobenius sheaf formula.

The symmetric multiplication theorem is applied to the actual group object.
No ample bundle,
polarized moduli point, finite-field descent, or elliptic-product decomposition
is constructed or assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open SchemeFrobenius PerfectFieldVerschiebung FrobeniusLineBundle
open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p]

local instance : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth g A.group.X.hom

local instance : IsCommMonObj (Over.mk A.group.X.hom) := by
  change IsCommMonObj A.group.X
  infer_instance

variable (L : A.group.X.left.Modules) (hL : Scheme.Modules.IsInvertible L)
variable (hsym : Nonempty ((Scheme.Modules.pullback ((𝟙 A.group.X)⁻¹).left).obj L ≅ L))

omit [IsAlgClosed K] in
private theorem schemeNsmul_eq_power (n : ℕ) :
    (GroupScheme.law A.group).schemeNsmul n = ((𝟙 A.group.X) ^ n).left := by
  have h := congrArg Subtype.val
    (GroupScheme.nsmul_eq_pow A.group A.group.X.hom n (𝟙 A.group.X))
  rw [nsmul_point] at h
  change (𝟙 A.group.X.left) ≫ (GroupScheme.law A.group).schemeNsmul n =
    ((𝟙 A.group.X) ^ n).left at h
  simpa only [Category.id_comp] using h

include hL hsym

/-- Multiplication by p on the actual group object pulls back a symmetric
invertible sheaf to its p²-th tensor power. -/
def multiplicationPullbackSymmetricBundleIso :
    (Scheme.Modules.pullback ((GroupScheme.law A.group).schemeNsmul p)).obj L ≅
      L.tensorPow (p ^ 2) := by
  letI : GrpObj (Over.mk A.group.X.hom) := A.group.grp
  letI : IsCommMonObj (Over.mk A.group.X.hom) := A.comm
  have h := Scheme.Modules.nonempty_pullback_zpow_iso_tensorPow_of_symmetric
    K A.group.X.hom (inferInstance : Smooth A.group.X.hom)
    (inferInstance : IsProper A.group.X.hom)
    (inferInstance : GeometricallyConnected A.group.X.hom) L hL hsym (p : ℤ)
  rw [A.schemeNsmul_eq_power p]
  apply Nonempty.some
  have hn : ((p : ℤ) * (p : ℤ)).toNat = p * p := by omega
  simp only [zpow_natCast, hn, pow_two] at h ⊢
  exact h

/-- The actual factorization forces an isomorphism of the two actual
pullbacks of the p²-th tensor power of a symmetric invertible sheaf. -/
def frobeniusFactorSymmetricBundleIso
    (W : Twist p (toBase p A.group.X.hom) ⟶ A.group.X.left)
    (hW : relative p (toBase p A.group.X.hom) ≫ W =
      verschiebung p A.group.X.hom (GroupScheme.law A.group)
        A.groupScheme_law_commutative) :
    (Scheme.Modules.pullback W).obj (L.tensorPow (p ^ 2)) ≅
      (Scheme.Modules.pullback (doubleProjection p A.group.X.hom)).obj
        (L.tensorPow (p ^ 2)) := by
  have hdouble : doubleRelative p A.group.X.hom ≫ W =
      (GroupScheme.law A.group).schemeNsmul p := by
    rw [doubleRelative, Category.assoc, hW, frobenius_verschiebung]
  let eF := absoluteSquarePullbackIso L A.group.X.hom p hL
  let eM := A.multiplicationPullbackSymmetricBundleIso p L hL hsym
  exact ((Scheme.Modules.pullback W).mapIso eF).symm ≪≫
    (Scheme.Modules.pullbackComp W _).app L ≪≫
    (Scheme.Modules.pullbackCongr
      (factor_absolute_square p A.group.X.hom W _ hdouble)).app L ≪≫
    ((Scheme.Modules.pullbackComp (doubleProjection p A.group.X.hom) _).app L).symm ≪≫
    (Scheme.Modules.pullback (doubleProjection p A.group.X.hom)).mapIso eM

/-- Zero actual Verschiebung cotangent produces the actual residual scheme
isomorphism together with its proved symmetric line-bundle compatibility. -/
theorem exists_frobenius_factor_iso_symmetric_bundle
    (hV : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0) :
    ∃ e : Twist p (toBase p A.group.X.hom) ≅ A.group.X.left,
      relative p (toBase p A.group.X.hom) ≫ e.hom =
        verschiebung p A.group.X.hom (GroupScheme.law A.group)
          A.groupScheme_law_commutative ∧
      e.hom ≫ A.group.X.hom = toBase p (toBase p A.group.X.hom) ∧
      Nonempty ((Scheme.Modules.pullback e.hom).obj (L.tensorPow (p ^ 2)) ≅
        (Scheme.Modules.pullback (doubleProjection p A.group.X.hom)).obj
          (L.tensorPow (p ^ 2))) := by
  obtain ⟨e, he, hover⟩ :=
    A.exists_frobenius_factor_iso_of_verschiebungCotangent_eq_zero p hV
  exact ⟨e, he, hover, ⟨A.frobeniusFactorSymmetricBundleIso p L hL hsym e.hom he⟩⟩

end SupersingularCurves.Geometry.AbelianVariety
