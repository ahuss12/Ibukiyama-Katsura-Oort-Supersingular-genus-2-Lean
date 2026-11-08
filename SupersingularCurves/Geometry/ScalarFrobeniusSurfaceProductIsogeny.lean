/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusProductIsogeny
import SupersingularCurves.Geometry.AbelianVarietyProductCategorical
import SupersingularCurves.Geometry.JacobianPoints
import SupersingularCurves.Geometry.Superspecial

/-! # Supersingular elliptic factors from an actual elliptic subgroup

The input subgroup is a genuine smooth connected closed subscheme with a
compatible group law. Its existence is not supplied by this theorem.
For a p-rank-zero surface, both resulting factors have trivial geometric
p-torsion, and the product map in each direction is an actual isogeny.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open FrobeniusFactorGroup AbelianVariety
open scoped CategoryTheory.MonObj
variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Trivial geometric p-torsion is inherited by an actual elliptic subgroup. -/
theorem AbelianVariety.isSupersingularElliptic_of_mono
    (p : ℕ) [Fact p.Prime] [CharP K p] {g : ℕ}
    (A : AbelianVariety K g) (hA : A.HasPRankOver p 0)
    (E : AbelianVariety K 1) (j : E.group ⟶ A.group)
    [Mono (underlyingScheme.map j)] : E.IsSupersingularElliptic p := by
  intro x hx
  have hjx : (x ≫ j.hom.hom) ^ p = 1 := by
    rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have hz := (A.hasPRankOver_zero_iff p).mp hA (x ≫ j.hom.hom) hjx
  apply Over.OverMorphism.ext
  apply (cancel_mono (underlyingScheme.map j)).mp
  exact congrArg Over.Hom.left (show x ≫ j.hom.hom = 1 ≫ j.hom.hom by
    rw [hz, MonObj.one_comp])

namespace ScalarFrobeniusTate

/-- Once an actual elliptic subgroup exists, a p-rank-zero abelian surface
admits actual isogenies to and from a product of supersingular elliptic curves. -/
theorem exists_supersingular_elliptic_product_isogeny_of_closed_subgroup
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (A : AbelianVariety K 2) (hA : A.HasPRankOver p 0)
    {X : Scheme.{u}} (j : X ⟶ A.group.X.left)
    [IsClosedImmersion j] [ConnectedSpace X]
    (L : RelativeGroupLaw K (j ≫ A.group.X.hom))
    [SmoothOfRelativeDimension 1 (j ≫ A.group.X.hom)]
    (hj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (j ≫ A.group.X.hom)),
      pointMap j rfl (L.mul t x y) =
        (GroupScheme.law A.group).mul t (pointMap j rfl x) (pointMap j rfl y)) :
    ∃ E C : AbelianVariety K 1,
      E.IsSupersingularElliptic p ∧ C.IsSupersingularElliptic p ∧
      (∃ f : (E.prod C).group ⟶ A.group, IsIsogeny f) ∧
      (∃ q : A.group ⟶ (E.prod C).group, IsIsogeny q) := by
  obtain ⟨E, C, jG, iG, hjG, hiG, _, hf, q, hq⟩ :=
    exists_product_isogeny_of_closed_subgroup A j L 1 hj
  letI := hjG
  letI := hiG
  exact ⟨E, C, A.isSupersingularElliptic_of_mono p hA E jG,
    A.isSupersingularElliptic_of_mono p hA C iG, ⟨E.prodCopair C jG iG, hf⟩, q, hq⟩

/-- The product isogeny meets the original, independent geometric definition.
The initial actual closed elliptic subgroup remains an explicit input. -/
theorem isSupersingularOver_of_closed_elliptic_subgroup
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (A : AbelianVariety K 2) (hA : A.HasPRankOver p 0)
    {X : Scheme.{u}} (j : X ⟶ A.group.X.left)
    [IsClosedImmersion j] [ConnectedSpace X]
    (L : RelativeGroupLaw K (j ≫ A.group.X.hom))
    [SmoothOfRelativeDimension 1 (j ≫ A.group.X.hom)]
    (hj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (j ≫ A.group.X.hom)),
      pointMap j rfl (L.mul t x y) =
        (GroupScheme.law A.group).mul t (pointMap j rfl x) (pointMap j rfl y)) :
    A.IsSupersingularOver p := by
  obtain ⟨E, C, hE, hC, _, q, hq⟩ :=
    exists_supersingular_elliptic_product_isogeny_of_closed_subgroup p A hA j L hj
  refine ⟨![E, C], ?_, q ≫ (E.prodFinTwoIso C).hom,
    hq.comp (isIsogeny_of_isIso (E.prodFinTwoIso C).hom)⟩
  intro i
  fin_cases i
  · exact hE
  · exact hC

end ScalarFrobeniusTate
end SupersingularCurves.Geometry
