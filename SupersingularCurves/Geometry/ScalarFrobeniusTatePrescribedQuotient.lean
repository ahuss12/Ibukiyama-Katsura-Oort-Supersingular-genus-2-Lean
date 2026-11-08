/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateKernelPoints
import SupersingularCurves.Geometry.ScalarFrobeniusTateQuotientImage

/-! # Quotients realizing prescribed actual torsion point subgroups -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian FrobeniusFactorGroup AbelianTate
open scoped CategoryTheory.MonObj
variable {K : Type} [Field K] {g : ℕ} (A : AbelianVariety K g)

@[simp] theorem pointsMap_multiplication (m : ℕ) (x : A.AdditivePoints) :
    pointsMap (multiplication A m) x = m • x := by
  apply congrArg Additive.ofMul
  apply Over.OverMorphism.ext
  have H := congrArg Subtype.val (GroupScheme.nsmul_eq_pow A.group (𝟙 _) m x.toMul)
  rw [SchemeFrobenius.nsmul_point] at H
  exact H

/-- Every prescribed subgroup of actual m-torsion points is realized by a
finite flat closed subgroup and actual quotient; its degree is its order.
The statement retains exact point membership for every m-torsion point. -/
theorem exists_quotient_of_torsion_point_subgroup [IsAlgClosed K]
    (m : ℕ) (hm : m ≠ 0) (S : AddSubgroup A.AdditivePoints)
    (hS : ∀ x ∈ S, m • x = 0) :
    ∃ H : FiniteSubgroup A, ∃ D : Quotient A H,
      (H.inclusion ≫ A.group.X.hom).finrank (IsLocalRing.closedPoint K) = Nat.card S ∧
      H.inclusion ≫ (GroupScheme.law A.group).schemeNsmul m =
        (H.inclusion ≫ A.group.X.hom) ≫ ((GroupScheme.law A.group).one (𝟙 _)).1 ∧
      ∀ x : A.AdditivePoints, m • x = 0 →
        ((∃ a : Spec (CommRingCat.of K) ⟶ H.carrier, a ≫ H.inclusion = x.toMul.left) ↔
          x ∈ S) := by
  let f := multiplication A m
  letI : IsFinite (underlyingScheme.map f) := (multiplication_isIsogeny A m hm).1
  let G := kernelGroup A A f
  let i := kernelInclusionHom A A f
  let k := kernelPointsMap A A f
  let N := S.comap k
  obtain ⟨H, j, hj, hrank, hpoints⟩ := exists_finiteSubgroup_of_points A G i N
  have hcard : Nat.card N = Nat.card S := by
    apply Nat.card_congr
    apply Equiv.ofBijective (fun y : N => (⟨k y.val, y.property⟩ : S))
    constructor
    · intro y z hyz
      apply Subtype.ext
      exact kernelPointsMap_injective A A f (congrArg Subtype.val hyz)
    · intro x
      have hx : pointsMap f x.val = 0 := (pointsMap_multiplication A m x.val).trans (hS _ x.property)
      obtain ⟨y, hy⟩ := (mem_range_kernelPointsMap A A f x.val).mpr hx
      exact ⟨⟨y, by change k y ∈ S; rw [hy]; exact x.property⟩, Subtype.ext hy⟩
  obtain ⟨D⟩ := nonempty_quotient_of_isAlgClosed A H
  refine ⟨H, D, hrank.trans hcard, ?_, ?_⟩
  · have hj' : j ≫ kernelInclusion A A f = H.inclusion := hj
    have hbase : kernelInclusion A A f ≫ A.group.X.hom = (kernelGroup A A f).X.hom :=
      (kernelInclusionHom A A f).hom.hom.w
    have hker : kernelInclusion A A f ≫ (GroupScheme.law A.group).schemeNsmul m =
        (kernelInclusion A A f ≫ A.group.X.hom) ≫ (GroupScheme.zero A.group).1 := by
      rw [hbase]
      exact pullback.condition
    rw [← hj', Category.assoc, hker]
    simp only [Category.assoc]
    rfl
  · intro x hx
    have hxf : pointsMap f x = 0 := (pointsMap_multiplication A m x).trans hx
    obtain ⟨y, hy⟩ := (mem_range_kernelPointsMap A A f x).mpr hxf
    have hleft : x.toMul.left = y.toMul.left ≫ underlyingScheme.map i := by
      rw [← hy, kernelPointsMap_left]
      rfl
    rw [hleft, hpoints]
    change k y ∈ S ↔ x ∈ S
    rw [hy]

/-- Prescribed actual ℓ^n-torsion subgroups give exactly the required integral
Tate lattices, as the images of actual isogenies from actual quotient varieties. -/
theorem exists_quotient_with_tate_image [IsAlgClosed K]
    (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (S : AddSubgroup A.AdditivePoints)
    (hS : ∀ x ∈ S, (ℓ ^ n) • x = 0) :
    ∃ H : FiniteSubgroup A, ∃ D : Quotient A H,
      ∃ hk : H.inclusion ≫ (GroupScheme.law A.group).schemeNsmul (ℓ ^ n) =
        (H.inclusion ≫ A.group.X.hom) ≫ ((GroupScheme.law A.group).one (𝟙 _)).1,
      (H.inclusion ≫ A.group.X.hom).finrank (IsLocalRing.closedPoint K) = Nat.card S ∧
      ∀ x : Integral ℓ A,
        x ∈ LinearMap.range (integralMap ℓ (D.multiplicationFactor (ℓ ^ n) hk)) ↔
          TateModule.proj ℓ A.AdditivePoints n x ∈ S := by
  obtain ⟨H, D, hrank, hk, hpoints⟩ := exists_quotient_of_torsion_point_subgroup A
    (ℓ ^ n) (pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero) S hS
  refine ⟨H, D, hk, hrank, ?_⟩
  intro x
  rw [D.mem_tate_range_iff_subgroup ℓ n hk]
  apply hpoints
  simpa only [natCast_zsmul] using TateModule.torsionBy_proj n x

end SupersingularCurves.Geometry.ScalarFrobeniusTate
