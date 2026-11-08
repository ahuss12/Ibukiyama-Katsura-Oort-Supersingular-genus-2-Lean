/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFactorSymmetricBundle
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isInvertible_nonempty_pullback_inv_iso_coeff_pos_forall_eulerChar_tensorPow_eq

/-!
# An actual symmetric bundle with a finite projective presentation

An actual invertible sheaf with a finite projective presentation is
symmetrized using pullback along inversion. The tensor product retains the
finite projective presentation. This constructs the sheaf used by the
residual Frobenius-isomorphism compatibility theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian SchemeFrobenius PerfectFieldVerschiebung
open scoped CategoryTheory.MonObj
open P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isInvertible_nonempty_pullback_inv_iso_coeff_pos_forall_eulerChar_tensorPow_eq

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable (A : AbelianVariety K g)

local instance : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth g A.group.X.hom

/-- Every actual abelian variety has an actual symmetric invertible sheaf
admitting a finite morphism to projective space defined by its sections. -/
theorem exists_symmetric_finiteBySections :
    ∃ L : A.group.X.left.Modules, Scheme.Modules.IsInvertible L ∧
      Nonempty ((Scheme.Modules.pullback ((𝟙 A.group.X)⁻¹).left).obj L ≅ L) ∧
      L.FiniteBySections A.group.X.hom := by
  let G := GroupScheme.law A.group
  obtain ⟨L₀, hL₀, N, P, hP⟩ :=
    AbelianSchemePropertyBundle.exists_isInvertible_finiteBySections
      K A.group.X.hom A.abelianSchemePropertyBundle
  obtain ⟨P', _, _, hsq⟩ :=
    Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback
      (P2mSymAmpleTop.isPullback_invMor G) P
  have hP' : IsFinite P'.toProj :=
    MorphismProperty.of_isPullback (P := @IsFinite) hsq hP
  have hfinite : ((Scheme.Modules.pullback (P2mSymAmpleTop.invMor G)).obj L₀).FiniteBySections
      A.group.X.hom := ⟨N, P', hP'⟩
  let L := L₀ ⊗ (Scheme.Modules.pullback (P2mSymAmpleTop.invMor G)).obj L₀
  have hsym : Nonempty ((Scheme.Modules.pullback ((𝟙 A.group.X)⁻¹).left).obj L ≅ L) := by
    change Nonempty ((Scheme.Modules.pullback (P2mSymAmpleTop.invMor G)).obj L ≅ L)
    exact P2mSymAmpleTop.nonempty_pullback_symm_iso (P2mSymAmpleTop.invMor G)
      (P2mSymAmpleTop.invMor_comp_invMor G) L₀
  exact ⟨L, hL₀.tensor (hL₀.pullback (P2mSymAmpleTop.invMor G)), hsym,
    Scheme.Modules.FiniteBySections.tensor ⟨N, P, hP⟩ hfinite⟩

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Zero actual Verschiebung cotangent constructs both the symmetric sheaf
with a finite projective presentation and the genuine residual scheme
isomorphism, with their actual p²-th-power pullbacks isomorphic. -/
theorem exists_frobenius_factor_iso_symmetric_projective_bundle
    (hV : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0) :
    ∃ (L : A.group.X.left.Modules)
      (e : Twist p (toBase p A.group.X.hom) ≅ A.group.X.left),
      Scheme.Modules.IsInvertible L ∧
      Nonempty ((Scheme.Modules.pullback ((𝟙 A.group.X)⁻¹).left).obj L ≅ L) ∧
      L.FiniteBySections A.group.X.hom ∧
      relative p (toBase p A.group.X.hom) ≫ e.hom =
        verschiebung p A.group.X.hom (GroupScheme.law A.group)
          A.groupScheme_law_commutative ∧
      e.hom ≫ A.group.X.hom = toBase p (toBase p A.group.X.hom) ∧
      Nonempty ((Scheme.Modules.pullback e.hom).obj (L.tensorPow (p ^ 2)) ≅
        (Scheme.Modules.pullback (doubleProjection p A.group.X.hom)).obj
          (L.tensorPow (p ^ 2))) := by
  obtain ⟨L, hL, hsym, hfinite⟩ := A.exists_symmetric_finiteBySections
  obtain ⟨e, he, hover, hcompat⟩ :=
    A.exists_frobenius_factor_iso_symmetric_bundle p L hL hsym hV
  exact ⟨L, e, hL, hsym, hfinite, he, hover, hcompat⟩

end SupersingularCurves.Geometry.AbelianVariety
