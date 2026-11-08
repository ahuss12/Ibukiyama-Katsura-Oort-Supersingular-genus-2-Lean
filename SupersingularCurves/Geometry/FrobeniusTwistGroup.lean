/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.Frobenius
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

/-!
# The actual group law on a Frobenius base change

The points of the fibre product are identified, by its universal property,
with points of the original scheme over the Frobenius-composed base map.
Transporting the original group operations across this particular equivalence
constructs the base-changed group law. Absolute Frobenius naturality then
proves that relative Frobenius is a group morphism. No Cartier operator is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.SchemeFrobenius
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p]
variable {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K))

/-- The point equivalence of the actual Frobenius fibre product. -/
def twistPointsEquiv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    SchemeHomOver t (toBase p c) ≃ SchemeHomOver (t ≫ baseMap p K) c where
  toFun x := ⟨x.1 ≫ projection p c, by
    rw [Category.assoc, show projection p c ≫ c = toBase p c ≫ baseMap p K from
      pullback.condition, ← Category.assoc, x.2]⟩
  invFun x := ⟨pullback.lift x.1 t x.2, pullback.lift_snd _ _ _⟩
  left_inv x := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans x.2.symm
  right_inv x := Subtype.ext (pullback.lift_fst _ _ _)

@[simp]
theorem twistPointsEquiv_apply_coe {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t (toBase p c)) :
    (twistPointsEquiv p c t x).1 = x.1 ≫ projection p c := rfl

theorem twistPointsEquiv_natural {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (t' : T' ⟶ Spec (CommRingCat.of K))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t (toBase p c)) :
    twistPointsEquiv p c t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      GoodReductionJacobian.schemeHomOverComp ψ
        (by rw [← Category.assoc, hψ]) (twistPointsEquiv p c t x) :=
  Subtype.ext (Category.assoc _ _ _)

variable (L : RelativeGroupLaw K c)

/-- Base change of the actual group law along the field Frobenius. -/
def twistLaw : RelativeGroupLaw K (toBase p c) where
  mul t x y := (twistPointsEquiv p c t).symm
    (L.mul _ (twistPointsEquiv p c t x) (twistPointsEquiv p c t y))
  one t := (twistPointsEquiv p c t).symm (L.one _)
  inv t x := (twistPointsEquiv p c t).symm (L.inv _ (twistPointsEquiv p c t x))
  mul_assoc t x y z := by simp only [Equiv.apply_symm_apply, L.mul_assoc]
  one_mul t x := by simp only [Equiv.apply_symm_apply, L.one_mul, Equiv.symm_apply_apply]
  mul_one t x := by simp only [Equiv.apply_symm_apply, L.mul_one, Equiv.symm_apply_apply]
  inv_mul_cancel t x := by simp only [Equiv.apply_symm_apply, L.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply (twistPointsEquiv p c t').injective
    rw [twistPointsEquiv_natural]
    simp only [Equiv.apply_symm_apply, L.mul_natural, twistPointsEquiv_natural]

@[simp]
theorem twistLaw_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (toBase p c)) :
    twistPointsEquiv p c t ((twistLaw p c L).mul t x y) =
      L.mul _ (twistPointsEquiv p c t x) (twistPointsEquiv p c t y) :=
  Equiv.apply_symm_apply _ _

@[simp]
theorem twistLaw_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    twistPointsEquiv p c t ((twistLaw p c L).one t) = L.one _ :=
  Equiv.apply_symm_apply _ _

theorem twistLaw_commutative (hc : L.IsCommutative) : (twistLaw p c L).IsCommutative := by
  intro T t x y
  apply (twistPointsEquiv p c t).injective
  rw [twistLaw_mul, twistLaw_mul, hc]

/-- The action of actual relative Frobenius on arbitrary test-scheme points. -/
def relativePoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (x : SchemeHomOver t c) : SchemeHomOver t (toBase p c) :=
  ⟨x.1 ≫ relative p c, by rw [Category.assoc, relative_toBase, x.2]⟩

theorem relativePoint_projection {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t c) :
    twistPointsEquiv p c t (relativePoint p c x) =
      GoodReductionJacobian.schemeHomOverComp (absolute p t) (absolute_over p t) x := by
  apply Subtype.ext
  change (x.1 ≫ relative p c) ≫ projection p c = absolute p t ≫ x.1
  rw [Category.assoc, relative_projection]
  exact (Scheme.frobenius_comp x.1 p 1 (Fact.out : p.Prime)
    (globalChar p t) (globalChar p c)).symm

/-- Relative Frobenius respects the independently base-changed group law. -/
theorem relative_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t c) :
    relativePoint p c (L.mul t x y) =
      (twistLaw p c L).mul t (relativePoint p c x) (relativePoint p c y) := by
  apply (twistPointsEquiv p c t).injective
  rw [twistLaw_mul, relativePoint_projection, relativePoint_projection,
    relativePoint_projection, L.mul_natural]

theorem relative_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    relativePoint p c (L.one t) = (twistLaw p c L).one t := by
  apply (twistPointsEquiv p c t).injective
  rw [relativePoint_projection, twistLaw_one, L.one_natural]

theorem relative_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (n : ℕ) (x : SchemeHomOver t c) :
    relativePoint p c (L.nsmul t n x) =
      (twistLaw p c L).nsmul t n (relativePoint p c x) := by
  induction n with
  | zero => exact relative_one p c L t
  | succ n ih => rw [L.nsmul_succ, relative_mul, (twistLaw p c L).nsmul_succ, ih]

theorem nsmul_point {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (n : ℕ) (x : SchemeHomOver t c) :
    (L.nsmul t n x).1 = x.1 ≫ L.schemeNsmul n := by
  have h := L.nsmul_natural c t x.1 x.2 n ⟨𝟙 _, Category.id_comp _⟩
  have hi : GoodReductionJacobian.schemeHomOverComp x.1 x.2
      (⟨𝟙 _, Category.id_comp _⟩ : SchemeHomOver c c) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hi] at h
  exact (congrArg Subtype.val h).symm

theorem schemeNsmul_relative (n : ℕ) :
    L.schemeNsmul n ≫ relative p c = relative p c ≫ (twistLaw p c L).schemeNsmul n := by
  have h := congrArg Subtype.val (relative_nsmul p c L c n ⟨𝟙 _, Category.id_comp _⟩)
  simpa only [relativePoint, nsmul_point, Category.id_comp] using h

end SupersingularCurves.Geometry.SchemeFrobenius
