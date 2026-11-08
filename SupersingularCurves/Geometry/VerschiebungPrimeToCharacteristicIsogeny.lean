/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PointedCotangentGroupAddNsmul
import SupersingularCurves.Geometry.ScalarFrobeniusTateQuotientDescent

/-! # Vanishing of actual dV under prime-to-characteristic isogenies -/
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.GroupScheme
open CategoryTheory AlgebraicGeometry
variable {K : Type u} [Field K] {G H J : GroupScheme K}

/-- The genuine cotangent pullback at the group identity. -/
def cotangentMap (f : G ⟶ H) :
    PointedCotangent.Cotangent H.X.hom (zero H) →ₗ[K]
      PointedCotangent.Cotangent G.X.hom (zero G) :=
  PointedCotangent.differential G.X.hom (zero G) f.hom.hom.left
    f.hom.hom.w (zero_natural f)

@[simp] theorem cotangentMap_comp (f : G ⟶ H) (q : H ⟶ J) :
    cotangentMap (f ≫ q) = cotangentMap f ∘ₗ cotangentMap q :=
  PointedCotangent.differential_comp _ _ _ _ _ _ _ _

end SupersingularCurves.Geometry.GroupScheme

namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open GroupScheme ScalarFrobeniusTate
variable {K : Type u} [Field K] {g h : ℕ}
variable (A : AbelianVariety K g) (B : AbelianVariety K h)

@[simp] theorem cotangentMap_multiplication (n : ℕ) :
    cotangentMap (multiplication A n) = (n : K) • LinearMap.id :=
  PointedCotangent.differential_schemeNsmul (GroupScheme.law A.group) n

/-- A genuine quasi-inverse with composite [n], where n is nonzero in K,
forces surjectivity of the actual cotangent pullback. -/
theorem cotangentMap_surjective_of_multiplication_factor
    (f : A.group ⟶ B.group) (q : B.group ⟶ A.group) (n : ℕ) (hn : (n : K) ≠ 0)
    (hq : q ≫ f = multiplication B n) : Function.Surjective (cotangentMap q) := by
  have H : cotangentMap q ∘ₗ cotangentMap f = (n : K) • LinearMap.id := by
    rw [← cotangentMap_comp, hq, cotangentMap_multiplication]
  intro x
  refine ⟨cotangentMap f ((n : K)⁻¹ • x), ?_⟩
  have hh := LinearMap.congr_fun H ((n : K)⁻¹ • x)
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    smul_smul, mul_inv_cancel₀ hn, one_smul] using hh

variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
local instance : Smooth A.group.X.hom := SmoothOfRelativeDimension.smooth g A.group.X.hom
local instance : Smooth B.group.X.hom := SmoothOfRelativeDimension.smooth h B.group.X.hom

/-- Prime-to-characteristic quasi-inverse isogenies preserve zero actual dV.
Both group maps and their multiplication identity are genuine geometric data. -/
theorem verschiebungCotangent_zero_of_multiplication_factor
    (f : A.group ⟶ B.group) (q : B.group ⟶ A.group) (n : ℕ) (hn : (n : K) ≠ 0)
    (hq : q ≫ f = multiplication B n)
    (hA : verschiebungCotangent p A.group A.groupScheme_law_commutative = 0) :
    verschiebungCotangent p B.group B.groupScheme_law_commutative = 0 := by
  have hs := A.cotangentMap_surjective_of_multiplication_factor B f q n hn hq
  have hnatur := verschiebungCotangent_natural p q
    B.groupScheme_law_commutative A.groupScheme_law_commutative
  rw [hA, LinearMap.comp_zero] at hnatur
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hs x
  exact (LinearMap.congr_fun hnatur y).symm

end SupersingularCurves.Geometry.AbelianVariety

namespace SupersingularCurves.Geometry.ScalarFrobeniusTate.Quotient
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open GroupScheme
variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable {A : AbelianVariety K g} {H : FiniteSubgroup A} (D : Quotient A H)
variable (p : ℕ) [Fact p.Prime] [CharP K p]
local instance : Smooth A.group.X.hom := SmoothOfRelativeDimension.smooth g A.group.X.hom
local instance : Smooth D.variety.group.X.hom := SmoothOfRelativeDimension.smooth g D.variety.group.X.hom

/-- The actual finite quotient used for a prime-to-p Tate lattice retains dV=0. -/
theorem verschiebungCotangent_zero (n : ℕ) (hn : (n : K) ≠ 0)
    (hk : H.inclusion ≫ (GroupScheme.law A.group).schemeNsmul n =
      (H.inclusion ≫ A.group.X.hom) ≫ ((GroupScheme.law A.group).one (𝟙 _)).1)
    (hA : verschiebungCotangent p A.group A.groupScheme_law_commutative = 0) :
    verschiebungCotangent p D.variety.group D.variety.groupScheme_law_commutative = 0 :=
  A.verschiebungCotangent_zero_of_multiplication_factor D.variety p
    D.map (D.multiplicationFactor n hk) n hn (D.multiplicationFactor_map n hk) hA

end SupersingularCurves.Geometry.ScalarFrobeniusTate.Quotient
