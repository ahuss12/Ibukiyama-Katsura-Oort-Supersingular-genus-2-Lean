/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientPoints
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorHom
import SupersingularCurves.Geometry.PRankZeroVerschiebungKernel

/-!
# Rational injectivity of the actual descended Verschiebung

At p-rank zero, the actual residual Verschiebung and its actual Frobenius
twist have trivial rational kernels. The argument uses the constructed
quotient's point surjectivity and the original Verschiebung point criterion.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.SchemeFrobenius
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open FrobeniusFactorGroup
variable {K : Type u} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
  {X Y : Scheme.{u}} {c : X ⟶ Spec (CommRingCat.of K)}
  {d : Y ⟶ Spec (CommRingCat.of K)} (f : X ⟶ Y) (hf : f ≫ d = c)

omit [PerfectField K] in
/-- Actual relative Frobenius identifies the point map of a morphism with
the point map of its base change. -/
theorem relativePoint_mapPoint
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) :
    pointMap (map p f hf) (map_toBase p f hf) (relativePoint p c x) =
      relativePoint p d (pointMap f hf x) := by
  apply Subtype.ext
  change (x.1 ≫ relative p c) ≫ map p f hf = (x.1 ≫ f) ≫ relative p d
  rw [Category.assoc, relative_natural, Category.assoc]

/-- Rational injectivity is preserved by the actual Frobenius base change. -/
theorem pointMap_map_injective
    (h : Function.Injective (pointMap f hf (t := 𝟙 (Spec (CommRingCat.of K))))) :
    Function.Injective
      (pointMap (map p f hf) (map_toBase p f hf) (t := 𝟙 (Spec (CommRingCat.of K)))) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := relativePoint_surjective p c x
  obtain ⟨y, rfl⟩ := relativePoint_surjective p c y
  rw [relativePoint_mapPoint, relativePoint_mapPoint] at hxy
  exact congrArg (relativePoint p c) (h (relativePoint_injective p d hxy))

end SupersingularCurves.Geometry.SchemeFrobenius

namespace SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open SchemeFrobenius PerfectFieldVerschiebung FrobeniusFactorGroup
variable {K : Type u} [Field K] [IsAlgClosed K]
  {p : ℕ} [Fact p.Prime] [CharP K p] {g : ℕ} {A : AbelianVariety K g}
  (D : QuotientData p A)

/-- The actual descended Verschiebung has trivial rational kernel at p-rank zero. -/
theorem verschiebungFactorPoint_kernel_trivial (hA : A.HasPRankOver p 0)
    (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.structureMap)
    (hy : pointMap D.verschiebungFactor.1 D.verschiebungFactor.2 y =
      (GroupScheme.law A.group).one (𝟙 _)) :
    y = D.quotientLaw.one (𝟙 _) := by
  obtain ⟨x, hx⟩ := FiniteSurjectivePoints.pointMap_surjective
    (base p A) D.structureMap D.quotientMap D.over_base y
  have hv : verschiebungPoint p A.group.X.hom (GroupScheme.law A.group)
      A.groupScheme_law_commutative x = (GroupScheme.law A.group).one (𝟙 _) := by
    apply Subtype.ext
    have hy' := congrArg Subtype.val hy
    have hx' := congrArg Subtype.val hx
    change x.1 ≫ V p A = _
    rw [← D.quotientMap_verschiebungFactor, ← Category.assoc]
    exact (congrArg (fun z => z ≫ D.verschiebungFactor.1) hx').trans hy'
  rw [← hx, vPoint_kernel_trivial p A hA x hv]
  exact D.map_one (𝟙 _)

/-- The actual residual morphism is injective on rational points. -/
theorem verschiebungFactorPoint_injective (hA : A.HasPRankOver p 0) :
    Function.Injective (pointMap D.verschiebungFactor.1 D.verschiebungFactor.2
      (t := 𝟙 (Spec (CommRingCat.of K)))) := by
  let : Group (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.structureMap) :=
    D.quotientLaw.pointGroup _
  let : Group (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) A.group.X.hom) :=
    (GroupScheme.law A.group).pointGroup _
  let m : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.structureMap →*
      SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) A.group.X.hom :=
    { toFun := pointMap D.verschiebungFactor.1 D.verschiebungFactor.2
      map_one' := D.verschiebungFactor_one _
      map_mul' := D.verschiebungFactor_mul _ }
  exact (injective_iff_map_eq_one m).mpr (D.verschiebungFactorPoint_kernel_trivial hA)

/-- The actual Frobenius twist of the residual morphism is also injective
on rational points, by relative Frobenius naturality. -/
theorem verschiebungFactorTwistPoint_injective (hA : A.HasPRankOver p 0) :
    Function.Injective (pointMap
      (SchemeFrobenius.map p D.verschiebungFactor.1 D.verschiebungFactor.2)
      (map_toBase p D.verschiebungFactor.1 D.verschiebungFactor.2)
      (t := 𝟙 (Spec (CommRingCat.of K)))) :=
  pointMap_map_injective p D.verschiebungFactor.1 D.verschiebungFactor.2
    (D.verschiebungFactorPoint_injective hA)

end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
