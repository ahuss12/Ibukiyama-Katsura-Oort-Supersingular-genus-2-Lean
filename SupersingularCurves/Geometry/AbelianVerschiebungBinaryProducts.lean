/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianVarietyProductMaps
import SupersingularCurves.Geometry.VerschiebungNaturality

/-! # Actual Verschiebung vanishing on binary abelian products -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.PointedCotangent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

variable {K : Type u} [Field K] {g h : ℕ}
  (A : AbelianVariety K g) (B : AbelianVariety K h)
  {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K))
  (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)

local instance binaryCotangentOppositeModule : Module Kᵐᵒᵖ (Cotangent c s) :=
  Module.compHom _ (RingEquiv.toOpposite K).symm.toRingHom
local instance binaryCotangentCentralScalar : IsCentralScalar K (Cotangent c s) :=
  ⟨fun _ _ => rfl⟩

/-- The actual fibre-product universal property detects vanishing of a
cotangent map from its two projection composites. -/
theorem differential_eq_zero_of_abelian_prod_components
    (f : X ⟶ (A.prod B).group.X.left) (hf : f ≫ (A.prod B).group.X.hom = c)
    (hfs : s.1 ≫ f = (GroupScheme.zero (A.prod B).group).1)
    (hfst : differential c s (f ≫ (A.prodFst B).hom.hom.left)
      (by rw [Category.assoc, (A.prodFst B).hom.hom.w, hf])
      (by rw [← Category.assoc, hfs, GroupScheme.zero_natural]) = 0)
    (hsnd : differential c s (f ≫ (A.prodSnd B).hom.hom.left)
      (by rw [Category.assoc, (A.prodSnd B).hom.hom.w, hf])
      (by rw [← Category.assoc, hfs, GroupScheme.zero_natural]) = 0) :
    differential c s f hf hfs = 0 := by
  let P := (A.prod B).group
  let V := Cotangent c s
  let t := pointsEquiv c s V LinearMap.id
  let z := GroupScheme.zero P
  let q := mapPoint c s f hf hfs t
  let q₀ := pointsEquiv P.X.hom z V 0
  have hπ {d : ℕ} (D : AbelianVariety K d) (π : P ⟶ D.group)
      (hcomp : differential c s (f ≫ π.hom.hom.left)
        (by rw [Category.assoc, π.hom.hom.w, hf])
        (by rw [← Category.assoc, hfs, GroupScheme.zero_natural]) = 0) :
      q.1 ≫ π.hom.hom.left = q₀.1 ≫ π.hom.hom.left := by
    have h₁ := differential_action c s (f ≫ π.hom.hom.left)
      (by rw [Category.assoc, π.hom.hom.w, hf])
      (by rw [← Category.assoc, hfs, GroupScheme.zero_natural])
      (LinearMap.id : V →ₗ[K] V)
    rw [hcomp, LinearMap.comp_zero] at h₁
    have h₂ := differential_action P.X.hom z π.hom.hom.left
      π.hom.hom.w (GroupScheme.zero_natural π)
      (0 : Cotangent P.X.hom z →ₗ[K] V)
    rw [LinearMap.zero_comp] at h₂
    have hp := congrArg Subtype.val (h₁.symm.trans h₂)
    simpa only [q, q₀, t, mapPoint, Category.assoc] using hp
  have heq : q = q₀ := by
    apply TangentPoints.ext
    apply pullback.hom_ext
    · exact hπ A (A.prodFst B) hfst
    · exact hπ B (A.prodSnd B) hsnd
  apply (pointsEquiv P.X.hom z V).injective
  change pointsEquiv P.X.hom z V ((pointsEquiv P.X.hom z V).symm q) = q₀
  rw [Equiv.apply_symm_apply]
  exact heq

end SupersingularCurves.Geometry.PointedCotangent

namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory AlgebraicGeometry
variable {K : Type u} [Field K] {g h : ℕ}
  (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]

local instance {d : ℕ} (A : AbelianVariety K d) : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth d A.group.X.hom

/-- Zero actual dV on the two factors gives zero actual dV on their genuine
binary product, in arbitrary dimensions. -/
theorem verschiebungCotangent_prod_eq_zero
    (A : AbelianVariety K g) (B : AbelianVariety K h)
    (hA : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0)
    (hB : GroupScheme.verschiebungCotangent p B.group B.groupScheme_law_commutative = 0) :
    GroupScheme.verschiebungCotangent p (A.prod B).group
      (A.prod B).groupScheme_law_commutative = 0 := by
  apply PointedCotangent.differential_eq_zero_of_abelian_prod_components A B
  · have h := GroupScheme.verschiebungCotangent_natural p (A.prodFst B)
      (A.prod B).groupScheme_law_commutative A.groupScheme_law_commutative
    rw [hA, LinearMap.comp_zero] at h
    rw [PointedCotangent.differential_comp]
    exact h.symm
  · have h := GroupScheme.verschiebungCotangent_natural p (A.prodSnd B)
      (A.prod B).groupScheme_law_commutative B.groupScheme_law_commutative
    rw [hB, LinearMap.comp_zero] at h
    rw [PointedCotangent.differential_comp]
    exact h.symm

end SupersingularCurves.Geometry.AbelianVariety
