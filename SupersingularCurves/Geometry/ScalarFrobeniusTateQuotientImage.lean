/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateLatticeImage
import SupersingularCurves.Geometry.AbelianTateFunctor

/-!
# Exact Tate-module image of the actual quotient multiplication factor

For an actual finite subgroup H killed by ℓ^n and its actual quotient
q:A→A/H, the constructed complementary map f:A/H→A has integral Tate image
exactly the lattice whose nth-level torsion point lies in H. The proof uses
the actual scheme kernel theorem, actual functorial Tate maps, and the two
proved multiplication identities.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SupersingularCurves.Geometry.ScalarFrobeniusTate.Quotient
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open FrobeniusFactorGroup AbelianTate
open scoped CategoryTheory.MonObj

variable {K : Type} [Field K] {g : ℕ} {A : AbelianVariety K g}
variable {H : FiniteSubgroup A} (D : Quotient A H)
variable (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
variable (hk : H.inclusion ≫ (GroupScheme.law A.group).schemeNsmul (ℓ ^ n) =
  (H.inclusion ≫ A.group.X.hom) ≫ ((GroupScheme.law A.group).one (𝟙 _)).1)

/-- The exact integral image is the inverse image of the actual quotient's
point kernel at torsion level n. -/
theorem mem_tate_range_iff_pointsMap_zero (x : Integral ℓ A) :
    x ∈ LinearMap.range (integralMap ℓ (D.multiplicationFactor (ℓ ^ n) hk)) ↔
      pointsMap D.map (TateModule.proj ℓ A.AdditivePoints n x) = 0 := by
  apply mem_range_iff_level_kernel ℓ
    (integralMap ℓ (D.multiplicationFactor (ℓ ^ n) hk)) (integralMap ℓ D.map) n
  · intro y
    have h := congrArg (integralMap ℓ) (D.multiplicationFactor_map (ℓ ^ n) hk)
    rw [integralMap_comp, integralMap_multiplication, Nat.cast_pow] at h
    exact congrArg (fun f => f y) h
  · intro y
    have h := congrArg (integralMap ℓ) (D.map_multiplicationFactor (ℓ ^ n) hk)
    rw [integralMap_comp, integralMap_multiplication, Nat.cast_pow] at h
    exact congrArg (fun f => f y) h
  · intro y
    rfl

/-- This image condition is precisely that the actual nth-level point
factors through the given closed subgroup scheme H. -/
theorem mem_tate_range_iff_subgroup (x : Integral ℓ A) :
    x ∈ LinearMap.range (integralMap ℓ (D.multiplicationFactor (ℓ ^ n) hk)) ↔
      ∃ e : Spec (CommRingCat.of K) ⟶ H.carrier,
        e ≫ H.inclusion =
          ((TateModule.proj ℓ A.AdditivePoints n x).toMul).left := by
  rw [D.mem_tate_range_iff_pointsMap_zero ℓ n hk]
  let z : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) A.group.X.hom :=
    overHomToSchemeHomOver ((TateModule.proj ℓ A.AdditivePoints n x).toMul)
  have hzero : pointsMap D.map (TateModule.proj ℓ A.AdditivePoints n x) = 0 ↔
      pointMap (underlyingScheme.map D.map) D.map.hom.hom.w z =
        (GroupScheme.law D.variety.group).one (𝟙 _) := by
    constructor
    · intro h
      have hp := congrArg (fun v : D.variety.AdditivePoints => v.toMul.left) h
      exact Subtype.ext hp
    · intro h
      apply congrArg Additive.ofMul
      apply Over.OverMorphism.ext
      exact congrArg Subtype.val h
  exact hzero.trans (D.kernel (𝟙 _) z)

end SupersingularCurves.Geometry.ScalarFrobeniusTate.Quotient
