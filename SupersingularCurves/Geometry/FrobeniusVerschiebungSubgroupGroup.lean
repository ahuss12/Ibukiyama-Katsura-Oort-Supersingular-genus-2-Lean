/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
import SupersingularCurves.Geometry.FrobeniusFactorGroup

/-!
# The group scheme on the simultaneous Frobenius and Verschiebung kernel

The actual closed subscheme constructed in `FrobeniusVerschiebungSubgroup`
inherits the multiplication, identity, and inverse of the Frobenius twist.
The inclusion is a morphism of the resulting actual commutative group schemes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open CategoryTheory.MonoidalCategory
open GoodReductionJacobian SchemeFrobenius
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

variable {K : Type u} [Field K]
variable (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]
variable {g : ℕ} (A : AbelianVariety K g)

/-- The inclusion on points of every test scheme. -/
def inclusionPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (x : SchemeHomOver t (toBase p A)) : SchemeHomOver t (base p A) :=
  ⟨x.1 ≫ inclusion p A, by rw [Category.assoc]; exact x.2⟩

theorem inclusionPoint_injective {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) :
    Function.Injective (inclusionPoint p A (t := t)) := by
  intro x y h
  apply Subtype.ext
  exact (cancel_mono (inclusion p A)).mp (congrArg Subtype.val h)

private def liftPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (x : SchemeHomOver t (base p A))
    (hx : ∃ e : T ⟶ scheme p A, e ≫ inclusion p A = x.1) :
    SchemeHomOver t (toBase p A) :=
  ⟨hx.choose, by
    change hx.choose ≫ inclusion p A ≫ base p A = t
    rw [← Category.assoc, hx.choose_spec, x.2]⟩

private theorem inclusionPoint_liftPoint {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)} (x : SchemeHomOver t (base p A))
    (hx : ∃ e : T ⟶ scheme p A, e ≫ inclusion p A = x.1) :
    inclusionPoint p A (liftPoint p A x hx) = x :=
  Subtype.ext hx.choose_spec

private def subgroupMul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (toBase p A)) : SchemeHomOver t (toBase p A) :=
  liftPoint p A ((law p A).mul t (inclusionPoint p A x) (inclusionPoint p A y))
    (mul_factors p A t _ _ ⟨x.1, rfl⟩ ⟨y.1, rfl⟩)

private def subgroupOne {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    SchemeHomOver t (toBase p A) :=
  liftPoint p A ((law p A).one t) (one_factors p A t)

private def subgroupInv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t (toBase p A)) : SchemeHomOver t (toBase p A) :=
  liftPoint p A ((law p A).inv t (inclusionPoint p A x))
    (inv_factors p A t _ ⟨x.1, rfl⟩)

private theorem inclusionPoint_mul {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t (toBase p A)) :
    inclusionPoint p A (subgroupMul p A t x y) =
      (law p A).mul t (inclusionPoint p A x) (inclusionPoint p A y) :=
  inclusionPoint_liftPoint p A _ _

private theorem inclusionPoint_one {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) :
    inclusionPoint p A (subgroupOne p A t) = (law p A).one t :=
  inclusionPoint_liftPoint p A _ _

private theorem inclusionPoint_inv {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t (toBase p A)) :
    inclusionPoint p A (subgroupInv p A t x) =
      (law p A).inv t (inclusionPoint p A x) :=
  inclusionPoint_liftPoint p A _ _

theorem inclusionPoint_natural {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)} {t' : T' ⟶ Spec (CommRingCat.of K)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t (toBase p A)) :
    inclusionPoint p A (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp ψ hψ (inclusionPoint p A x) :=
  Subtype.ext (Category.assoc _ _ _)

/-- Restriction of the actual group law to the actual simultaneous kernel. -/
def subgroupLaw : RelativeGroupLaw K (toBase p A) where
  mul := subgroupMul p A
  one := subgroupOne p A
  inv := subgroupInv p A
  mul_assoc := by
    intro T t x y z
    apply inclusionPoint_injective p A t
    simp only [inclusionPoint_mul, (law p A).mul_assoc]
  one_mul := by
    intro T t x
    apply inclusionPoint_injective p A t
    rw [inclusionPoint_mul, inclusionPoint_one, (law p A).one_mul]
  mul_one := by
    intro T t x
    apply inclusionPoint_injective p A t
    rw [inclusionPoint_mul, inclusionPoint_one, (law p A).mul_one]
  inv_mul_cancel := by
    intro T t x
    apply inclusionPoint_injective p A t
    rw [inclusionPoint_mul, inclusionPoint_inv, inclusionPoint_one,
      (law p A).inv_mul_cancel]
  mul_natural := by
    intro T T' t t' ψ hψ x y
    apply inclusionPoint_injective p A t'
    rw [inclusionPoint_natural, inclusionPoint_mul, inclusionPoint_mul,
      inclusionPoint_natural, inclusionPoint_natural, (law p A).mul_natural]

theorem inclusionPoint_subgroupLaw_mul {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t (toBase p A)) :
    inclusionPoint p A ((subgroupLaw p A).mul t x y) =
      (law p A).mul t (inclusionPoint p A x) (inclusionPoint p A y) :=
  inclusionPoint_mul p A t x y

theorem inclusionPoint_subgroupLaw_one {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) :
    inclusionPoint p A ((subgroupLaw p A).one t) = (law p A).one t :=
  inclusionPoint_one p A t

theorem inclusionPoint_subgroupLaw_inv {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t (toBase p A)) :
    inclusionPoint p A ((subgroupLaw p A).inv t x) =
      (law p A).inv t (inclusionPoint p A x) :=
  inclusionPoint_inv p A t x

theorem subgroupLaw_commutative : (subgroupLaw p A).IsCommutative := by
  intro T t x y
  apply inclusionPoint_injective p A t
  rw [inclusionPoint_subgroupLaw_mul, inclusionPoint_subgroupLaw_mul]
  exact twistLaw_commutative p A.group.X.hom (GroupScheme.law A.group)
    A.groupScheme_law_commutative t _ _

/-- The genuine group scheme carried by the actual simultaneous kernel. -/
def subgroupGroup : GroupScheme K where
  X := Over.mk (toBase p A)
  grp := (subgroupLaw p A).grpObjOverMk

/-- The genuine group scheme on the original Frobenius twist. -/
def twistGroup : GroupScheme K where
  X := Over.mk (base p A)
  grp := (law p A).grpObjOverMk

instance subgroupGroup_isCommMonObj : IsCommMonObj (subgroupGroup p A).X :=
  ((subgroupLaw p A).isCommMonObj_grpObjOverMk_iff_mul_comm).mpr
    (subgroupLaw_commutative p A)

instance twistGroup_isCommMonObj : IsCommMonObj (twistGroup p A).X :=
  ((law p A).isCommMonObj_grpObjOverMk_iff_mul_comm).mpr
    (twistLaw_commutative p A.group.X.hom (GroupScheme.law A.group)
      A.groupScheme_law_commutative)

/-- The inclusion is a group morphism, as an actual morphism over the field. -/
instance inclusion_isMonHom :
    IsMonHom (Over.homMk (inclusion p A) rfl :
      (subgroupGroup p A).X ⟶ (twistGroup p A).X) := by
  apply GroupScheme.isMonHom_of_pointMap
    (G := subgroupGroup p A) (H := twistGroup p A) (inclusion p A) rfl
  · intro T t
    simpa only [GroupScheme.law, subgroupGroup, twistGroup,
      relativeGroupLawOfGrpObj_grpObjOverMk_one, FrobeniusFactorGroup.pointMap,
      inclusionPoint] using
      inclusionPoint_subgroupLaw_one p A t
  · intro T t x y
    simpa only [GroupScheme.law, subgroupGroup, twistGroup,
      relativeGroupLawOfGrpObj_grpObjOverMk_mul, FrobeniusFactorGroup.pointMap,
      inclusionPoint] using
      inclusionPoint_subgroupLaw_mul p A t x y

/-- The bundled inclusion has the original closed immersion as its scheme map. -/
def inclusionHom : subgroupGroup p A ⟶ twistGroup p A :=
  Grp.homMk (Over.homMk (inclusion p A) rfl :
    (subgroupGroup p A).X ⟶ (twistGroup p A).X)

theorem inclusionHom_left : (inclusionHom p A).hom.hom.left = inclusion p A := rfl

/-- The new group scheme has the identity point already used for its cotangent space. -/
theorem subgroupGroup_zero : GroupScheme.zero (subgroupGroup p A) = identityPoint p A := by
  simpa only [GroupScheme.zero, GroupScheme.law, subgroupGroup,
    relativeGroupLawOfGrpObj_grpObjOverMk_one] using
    (show (subgroupLaw p A).one (𝟙 _) = identityPoint p A from rfl)

/-- Multiplication preservation as an equality of actual scheme morphisms. -/
theorem inclusion_mul_map :
    (μ[(subgroupGroup p A).X]).left ≫ inclusion p A =
      ((inclusionHom p A).hom.hom ⊗ₘ (inclusionHom p A).hom.hom).left ≫
        (μ[(twistGroup p A).X]).left :=
  congrArg Over.Hom.left (IsMonHom.mul_hom (inclusionHom p A).hom.hom)

/-- Inverse preservation as an equality of actual scheme morphisms. -/
theorem inclusion_inv_map :
    (ι[(subgroupGroup p A).X]).left ≫ inclusion p A =
      inclusion p A ≫ (ι[(twistGroup p A).X]).left :=
  congrArg Over.Hom.left (GrpObj.inv_hom (inclusionHom p A).hom.hom)

end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
