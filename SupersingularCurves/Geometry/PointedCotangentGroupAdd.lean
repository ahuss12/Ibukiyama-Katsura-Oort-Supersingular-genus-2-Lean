/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusCotangentVanishing
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

/-! # The actual group law adds cotangent functionals on square-zero points -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.PointedCotangent
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

variable {K : Type u} [Field K] {X : Scheme.{u}}
variable {c : X ⟶ Spec (CommRingCat.of K)} (L : RelativeGroupLaw K c)
variable {V : Type u} [AddCommGroup V] [Module K V]
  [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
variable {W : Type u} [AddCommGroup W] [Module K W]
  [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

/-- Multiply actual square-zero points with the genuine scheme group law. -/
def tangentMul (x y : TangentPoints c (L.one (𝟙 _)).1 V) :
    TangentPoints c (L.one (𝟙 _)).1 V :=
  ⟨(L.mul (SquareZero.toBase K V) ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩).1,
    (L.mul _ _ _).2, by
      have hx : schemeHomOverComp (SquareZero.basePoint K V)
          (SquareZero.basePoint_toBase K V) (⟨x.1, x.2.1⟩ : SchemeHomOver _ c) =
          L.one (𝟙 _) := Subtype.ext x.2.2
      have hy : schemeHomOverComp (SquareZero.basePoint K V)
          (SquareZero.basePoint_toBase K V) (⟨y.1, y.2.1⟩ : SchemeHomOver _ c) =
          L.one (𝟙 _) := Subtype.ext y.2.2
      have H := L.mul_natural (SquareZero.toBase K V)
        (𝟙 _) (SquareZero.basePoint K V) (SquareZero.basePoint_toBase K V)
        ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩
      rw [hx, hy, L.one_mul] at H
      exact congrArg Subtype.val H⟩

theorem tangentMul_map (φ : V →ₗ[K] W)
    (x y : TangentPoints c (L.one (𝟙 _)).1 V) :
    (tangentMul L x y).map φ = tangentMul L (x.map φ) (y.map φ) := by
  apply TangentPoints.ext
  have H := congrArg Subtype.val (L.mul_natural (SquareZero.toBase K V)
    (SquareZero.toBase K W) (SquareZero.specMap K φ) (SquareZero.specMap_toBase K φ)
    ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩)
  exact H

private theorem pointsEquiv_zero_as_one :
    (⟨(pointsEquiv c (L.one (𝟙 _)) V 0).1, (pointsEquiv c (L.one (𝟙 _)) V 0).2.1⟩ :
      SchemeHomOver (SquareZero.toBase K V) c) = L.one (SquareZero.toBase K V) := by
  apply Subtype.ext
  rw [pointsEquiv_zero_coe]
  exact congrArg Subtype.val (L.one_natural (𝟙 _) (SquareZero.toBase K V)
    (SquareZero.toBase K V) (Category.comp_id _))

theorem tangentMul_zero_left (x : TangentPoints c (L.one (𝟙 _)).1 V) :
    tangentMul L (pointsEquiv c (L.one (𝟙 _)) V 0) x = x := by
  apply TangentPoints.ext
  change (L.mul _ _ _).1 = _
  rw [pointsEquiv_zero_as_one, L.one_mul]

theorem tangentMul_zero_right (x : TangentPoints c (L.one (𝟙 _)).1 V) :
    tangentMul L x (pointsEquiv c (L.one (𝟙 _)) V 0) = x := by
  apply TangentPoints.ext
  change (L.mul _ _ _).1 = _
  rw [pointsEquiv_zero_as_one, L.mul_one]

/-- The group operation transported through the actual local cotangent comparison. -/
def cotangentMul (f g : Cotangent c (L.one (𝟙 _)) →ₗ[K] V) :
    Cotangent c (L.one (𝟙 _)) →ₗ[K] V :=
  (pointsEquiv c (L.one (𝟙 _)) V).symm
    (tangentMul L (pointsEquiv c (L.one (𝟙 _)) V f) (pointsEquiv c (L.one (𝟙 _)) V g))

theorem cotangentMul_map (φ : V →ₗ[K] W) (f g : Cotangent c (L.one (𝟙 _)) →ₗ[K] V) :
    φ ∘ₗ cotangentMul L f g = cotangentMul L (φ ∘ₗ f) (φ ∘ₗ g) := by
  apply (pointsEquiv c (L.one (𝟙 _)) W).injective
  rw [pointsEquiv_map, cotangentMul, Equiv.apply_symm_apply,
    tangentMul_map, cotangentMul, Equiv.apply_symm_apply,
    ← pointsEquiv_map, ← pointsEquiv_map]

@[simp] theorem cotangentMul_zero_left (f : Cotangent c (L.one (𝟙 _)) →ₗ[K] V) :
    cotangentMul L 0 f = f := by
  rw [cotangentMul, tangentMul_zero_left, Equiv.symm_apply_apply]

@[simp] theorem cotangentMul_zero_right (f : Cotangent c (L.one (𝟙 _)) →ₗ[K] V) :
    cotangentMul L f 0 = f := by
  rw [cotangentMul, tangentMul_zero_right, Equiv.symm_apply_apply]

/-- Naturality and the actual group identity force the tangent operation to be
the canonical addition on linear maps. -/
theorem cotangentMul_eq_add (f g : Cotangent c (L.one (𝟙 _)) →ₗ[K] V) :
    cotangentMul L f g = f + g := by
  let F := f.prod (0 : Cotangent c (L.one (𝟙 _)) →ₗ[K] V)
  let G := (0 : Cotangent c (L.one (𝟙 _)) →ₗ[K] V).prod g
  have hfst : LinearMap.fst K V V ∘ₗ cotangentMul L F G = f := by
    rw [cotangentMul_map]
    simp only [F, G, LinearMap.fst_prod, cotangentMul_zero_right]
  have hsnd : LinearMap.snd K V V ∘ₗ cotangentMul L F G = g := by
    rw [cotangentMul_map]
    simp only [F, G, LinearMap.snd_prod, cotangentMul_zero_left]
  have H := cotangentMul_map L (LinearMap.fst K V V + LinearMap.snd K V V) F G
  simpa only [LinearMap.add_comp, hfst, hsnd, F, G, LinearMap.fst_prod,
    LinearMap.snd_prod, add_zero, zero_add] using H.symm

/-- The local-ring comparison turns addition of functionals into the actual
scheme multiplication on square-zero points. -/
theorem pointsEquiv_add (f g : Cotangent c (L.one (𝟙 _)) →ₗ[K] V) :
    pointsEquiv c (L.one (𝟙 _)) V (f + g) =
      tangentMul L (pointsEquiv c (L.one (𝟙 _)) V f) (pointsEquiv c (L.one (𝟙 _)) V g) := by
  rw [← cotangentMul_eq_add L, cotangentMul, Equiv.apply_symm_apply]

section Differential
variable {Y : Scheme.{u}} {d : Y ⟶ Spec (CommRingCat.of K)}
variable (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) d)
variable (f g : SchemeHomOver d c)
variable (hf : s.1 ≫ f.1 = (L.one (𝟙 _)).1)
  (hg : s.1 ≫ g.1 = (L.one (𝟙 _)).1)

include hf hg in
/-- The sum of pointed maps remains pointed at the actual group identity. -/
theorem law_mul_point : s.1 ≫ (L.mul d f g).1 = (L.one (𝟙 _)).1 := by
  have H := L.mul_natural d (𝟙 _) s.1 s.2 f g
  have hf' : schemeHomOverComp s.1 s.2 f = L.one (𝟙 _) := Subtype.ext hf
  have hg' : schemeHomOverComp s.1 s.2 g = L.one (𝟙 _) := Subtype.ext hg
  rw [hf', hg', L.one_mul] at H
  exact congrArg Subtype.val H

local instance groupAddCotangentOppositeModule : Module Kᵐᵒᵖ (Cotangent d s) :=
  Module.compHom _ (RingEquiv.toOpposite K).symm.toRingHom

local instance groupAddCotangentCentralScalar : IsCentralScalar K (Cotangent d s) :=
  ⟨fun _ _ => rfl⟩

/-- The constant group-identity map sends the given point to the identity. -/
theorem law_one_point : s.1 ≫ (L.one d).1 = (L.one (𝟙 _)).1 :=
  congrArg Subtype.val (L.one_natural d (𝟙 _) s.1 s.2)

/-- The actual constant map has zero cotangent differential. -/
theorem differential_law_one :
    differential d s (L.one d).1 (L.one d).2 (law_one_point L s) = 0 := by
  apply (pointsEquiv c (L.one (𝟙 _)) (Cotangent d s)).injective
  rw [differential, Equiv.apply_symm_apply]
  apply TangentPoints.ext
  rw [pointsEquiv_zero_coe]
  have H := congrArg Subtype.val (L.one_natural (𝟙 _) d d (Category.comp_id d))
  change d ≫ (L.one (𝟙 _)).1 = (L.one d).1 at H
  change (pointsEquiv d s (Cotangent d s) LinearMap.id).1 ≫ (L.one d).1 = _
  rw [← H, ← Category.assoc, (pointsEquiv d s (Cotangent d s) LinearMap.id).2.1]

/-- Differentiating the actual pointwise scheme group law adds the actual
contravariant cotangent maps. -/
theorem differential_law_mul :
    differential d s (L.mul d f g).1 (L.mul d f g).2 (law_mul_point L s f g hf hg) =
      differential d s f.1 f.2 hf + differential d s g.1 g.2 hg := by
  apply (pointsEquiv c (L.one (𝟙 _)) (Cotangent d s)).injective
  rw [pointsEquiv_add L]
  simp only [differential, Equiv.apply_symm_apply]
  apply TangentPoints.ext
  have H := congrArg Subtype.val (L.mul_natural d (SquareZero.toBase K (Cotangent d s))
    (pointsEquiv d s (Cotangent d s) LinearMap.id).1
    (pointsEquiv d s (Cotangent d s) LinearMap.id).2.1 f g)
  exact H

end Differential

end SupersingularCurves.Geometry.PointedCotangent
