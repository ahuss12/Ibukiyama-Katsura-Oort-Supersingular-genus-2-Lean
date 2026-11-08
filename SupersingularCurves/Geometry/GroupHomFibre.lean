/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PointedCotangentFibreExact
import SupersingularCurves.Geometry.FrobeniusFactorGroup

/-! # The actual group law on the identity fibre of a group morphism -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.GroupHomFibre
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian FrobeniusFactorGroup

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
  {c : X ⟶ Spec (CommRingCat.of K)} {d : Y ⟶ Spec (CommRingCat.of K)}
  (L : RelativeGroupLaw K c) (M : RelativeGroupLaw K d)
  (f : X ⟶ Y) (hf : f ≫ d = c)
  (hm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t c),
    pointMap f hf (L.mul t x y) = M.mul t (pointMap f hf x) (pointMap f hf y))

include hm in
theorem map_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    pointMap f hf (L.one t) = M.one t := by
  let : Group (SchemeHomOver t d) := M.pointGroup t
  let a := pointMap f hf (L.one t)
  have ha : a * a = a * 1 := by
    change M.mul t a a = M.mul t a (M.one t)
    rw [M.mul_one, ← hm, L.one_mul]
  exact mul_left_cancel ha

def pointsHom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    letI := L.pointGroup t
    letI := M.pointGroup t
    SchemeHomOver t c →* SchemeHomOver t d := by
  letI := L.pointGroup t
  letI := M.pointGroup t
  exact ⟨⟨pointMap f hf, map_one L M f hf hm t⟩, hm t⟩

include hm in
theorem map_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t c) :
    pointMap f hf (L.inv t x) = M.inv t (pointMap f hf x) := by
  let := L.pointGroup t
  let := M.pointGroup t
  exact (pointsHom L M f hf hm t).map_inv x

abbrev scheme : Scheme.{u} := PointedCotangent.Fibre.scheme f (z := M.one (𝟙 _))

abbrev toBase : scheme M f ⟶ Spec (CommRingCat.of K) :=
  PointedCotangent.Fibre.toBase f (z := M.one (𝟙 _))

abbrev inclusion : scheme M f ⟶ X := PointedCotangent.Fibre.inclusion f

def inclusionPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (x : SchemeHomOver t (toBase M f)) : SchemeHomOver t c :=
  ⟨x.1 ≫ inclusion M f, by
    rw [Category.assoc, PointedCotangent.Fibre.inclusion_over c f hf, x.2]⟩

theorem inclusionPoint_injective {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) :
    Function.Injective (inclusionPoint M f hf (t := t)) := by
  intro x y h
  apply Subtype.ext
  exact (cancel_mono (inclusion M f)).mp (congrArg Subtype.val h)

private theorem one_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    (M.one t).1 = t ≫ (M.one (𝟙 _)).1 :=
  (congrArg Subtype.val (M.one_natural (𝟙 _) t t (Category.comp_id t))).symm

theorem inclusionPoint_kernel {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (x : SchemeHomOver t (toBase M f)) :
    pointMap f hf (inclusionPoint M f hf x) = M.one t := by
  apply Subtype.ext
  change (x.1 ≫ pullback.fst _ _) ≫ f = _
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  change (x.1 ≫ toBase M f) ≫ _ = _
  rw [x.2]
  exact (one_coe M t).symm

def liftPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (x : SchemeHomOver t c) (hx : pointMap f hf x = M.one t) :
    SchemeHomOver t (toBase M f) :=
  ⟨pullback.lift x.1 t ((congrArg Subtype.val hx).trans (one_coe M t)),
    pullback.lift_snd _ _ _⟩

theorem inclusionPoint_liftPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (x : SchemeHomOver t c) (hx : pointMap f hf x = M.one t) :
    inclusionPoint M f hf (liftPoint M f hf x hx) = x :=
  Subtype.ext (pullback.lift_fst _ _ _)

private def mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (toBase M f)) : SchemeHomOver t (toBase M f) :=
  liftPoint M f hf (L.mul t (inclusionPoint M f hf x) (inclusionPoint M f hf y))
    (by rw [hm, inclusionPoint_kernel, inclusionPoint_kernel, M.one_mul])

private def one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    SchemeHomOver t (toBase M f) :=
  liftPoint M f hf (L.one t) (map_one L M f hf hm t)

private def inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t (toBase M f)) : SchemeHomOver t (toBase M f) :=
  liftPoint M f hf (L.inv t (inclusionPoint M f hf x)) (by
    rw [map_inv L M f hf hm, inclusionPoint_kernel]
    let := M.pointGroup t
    exact inv_one)

private theorem inclusionPoint_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (toBase M f)) :
    inclusionPoint M f hf (mul L M f hf hm t x y) =
      L.mul t (inclusionPoint M f hf x) (inclusionPoint M f hf y) :=
  inclusionPoint_liftPoint M f hf _ _

private theorem inclusionPoint_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    inclusionPoint M f hf (one L M f hf hm t) = L.one t :=
  inclusionPoint_liftPoint M f hf _ _

private theorem inclusionPoint_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t (toBase M f)) :
    inclusionPoint M f hf (inv L M f hf hm t x) = L.inv t (inclusionPoint M f hf x) :=
  inclusionPoint_liftPoint M f hf _ _

theorem inclusionPoint_natural {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)} {t' : T' ⟶ Spec (CommRingCat.of K)}
    (a : T' ⟶ T) (ha : a ≫ t = t') (x : SchemeHomOver t (toBase M f)) :
    inclusionPoint M f hf (schemeHomOverComp a ha x) =
      schemeHomOverComp a ha (inclusionPoint M f hf x) :=
  Subtype.ext (Category.assoc _ _ _)

/-- The group law on the actual scheme-theoretic identity fibre. -/
def law : RelativeGroupLaw K (toBase M f) where
  mul := mul L M f hf hm
  one := one L M f hf hm
  inv := inv L M f hf hm
  mul_assoc := by
    intro T t x y z
    apply inclusionPoint_injective M f hf t
    simp only [inclusionPoint_mul, L.mul_assoc]
  one_mul := by
    intro T t x
    apply inclusionPoint_injective M f hf t
    rw [inclusionPoint_mul, inclusionPoint_one, L.one_mul]
  mul_one := by
    intro T t x
    apply inclusionPoint_injective M f hf t
    rw [inclusionPoint_mul, inclusionPoint_one, L.mul_one]
  inv_mul_cancel := by
    intro T t x
    apply inclusionPoint_injective M f hf t
    rw [inclusionPoint_mul, inclusionPoint_inv, inclusionPoint_one, L.inv_mul_cancel]
  mul_natural := by
    intro T T' t t' a ha x y
    apply inclusionPoint_injective M f hf t'
    rw [inclusionPoint_natural, inclusionPoint_mul, inclusionPoint_mul,
      inclusionPoint_natural, inclusionPoint_natural, L.mul_natural]

/-- Its identity is the independently defined pointed-fibre lift. -/
theorem law_one_eq_point :
    (law L M f hf hm).one (𝟙 _) =
      PointedCotangent.Fibre.point c (L.one (𝟙 _)) f
        (congrArg Subtype.val (map_one L M f hf hm (𝟙 _))) := by
  apply inclusionPoint_injective M f hf (𝟙 _)
  rw [show (law L M f hf hm).one (𝟙 _) = one L M f hf hm (𝟙 _) from rfl,
    inclusionPoint_one]
  apply Subtype.ext
  exact (PointedCotangent.Fibre.point_inclusion c (L.one (𝟙 _)) f _).symm

end SupersingularCurves.Geometry.GroupHomFibre
