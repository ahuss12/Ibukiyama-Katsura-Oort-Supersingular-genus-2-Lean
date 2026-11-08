/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PicardFrobeniusTwist
import SupersingularCurves.Geometry.FrobeniusLineBundle
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_pow_iso_tensorPow

/-!
# Curve Frobenius pullback and independently constructed Verschiebung

The comparison is made on the actual Poincare bundle. Applying relative
Frobenius in both factors and then the base-change projection is absolute
Frobenius of the product. Absolute Frobenius pullback is its p-th tensor
power, so the represented composite is multiplication by p.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.SchemeFrobenius
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra GoodReductionJacobian

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p]
variable {C D : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
  (d : D ⟶ Spec (CommRingCat.of K))

/-- Relative Frobenius in both factors of the actual fibre product. -/
def productRelative : pullback c d ⟶ pullback (toBase p c) (toBase p d) :=
  pullback.map c d (toBase p c) (toBase p d) (relative p c) (relative p d)
    (𝟙 _) (by simp) (by simp)

/-- Projection from the two Frobenius-twisted factors to the original product. -/
def productProjection : pullback (toBase p c) (toBase p d) ⟶ pullback c d :=
  pullback.map (toBase p c) (toBase p d) c d (projection p c) (projection p d)
    (baseMap p K) pullback.condition.symm pullback.condition.symm

/-- The simultaneous relative Frobenius becomes absolute Frobenius after
projection from the twists. This is equality of scheme morphisms. -/
theorem productRelative_projection :
    productRelative p c d ≫ productProjection p c d =
      absolute p (pullback.snd c d ≫ d) := by
  apply pullback.hom_ext
  · simp only [productRelative, productProjection, pullback.lift_fst,
      Category.assoc, pullback.lift_fst_assoc, relative_projection]
    exact (Scheme.frobenius_comp (pullback.fst c d) p 1 (Fact.out : p.Prime)
      (globalChar p (pullback.snd c d ≫ d)) (globalChar p c)).symm
  · simp only [productRelative, productProjection, pullback.lift_snd,
      Category.assoc, pullback.lift_snd_assoc, relative_projection]
    exact (Scheme.frobenius_comp (pullback.snd c d) p 1 (Fact.out : p.Prime)
      (globalChar p (pullback.snd c d ≫ d)) (globalChar p d)).symm

/-- The product map factors as parameter Frobenius followed by curve Frobenius. -/
theorem productRelative_factor :
    baseChangeSnd c ⟨relative p d, relative_toBase p d⟩ ≫
      curveChange (relative p c) (relative_toBase p c) (toBase p d) =
        productRelative p c d := by
  apply pullback.hom_ext <;>
    simp only [baseChangeSnd, curveChange, productRelative, Category.assoc,
      pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      Category.comp_id]

variable {c} {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
variable {P : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c s (algEquivZeroCut c s) P)

/-- The actual twisted Poincare bundle is the pullback of the original bundle
along the simultaneous projection from the two twisted factors. -/
def twistPoincareIsoProjection :
    (twistPoincare p h).L ≅
      (Scheme.Modules.pullback (productProjection p c P.toBase)).obj h.poincare.L := by
  letI : Algebra K K := (frobenius K p).toAlgebra
  have hm : (BaseChange.κ c K (toBase p P.toBase)).hom ≫
      baseChangeSnd c ⟨projection p P.toBase, pullback.condition⟩ =
        productProjection p c P.toBase := by
    apply pullback.hom_ext
    · simp only [Category.assoc, BaseChange.baseChangeSnd_fst', BaseChange.κ_hom_fst,
        productProjection, pullback.lift_fst]
      rfl
    · rw [Category.assoc, BaseChange.baseChangeSnd_snd',
        ← Category.assoc, BaseChange.κ_hom_snd]
      simp only [productProjection, pullback.lift_snd]
      rfl
  exact (Scheme.Modules.pullbackComp _ _).app h.poincare.L ≪≫
    (Scheme.Modules.pullbackCongr hm).app h.poincare.L

/-- Tensor powers transport actual sheaf isomorphisms. -/
def tensorPowerCongr {X : Scheme.{u}} {L N : X.Modules} (e : L ≅ N) :
    (n : ℕ) → L.tensorPow n ≅ N.tensorPow n
  | 0 => Iso.refl _
  | n + 1 => tensorPowerCongr e n ⊗ᵢ e

/-- The identity parameter gives back the actual Poincare bundle. -/
def poincareIdentityIso :
    (h.poincare.pullbackAlong ⟨𝟙 _, Category.id_comp _⟩).L ≅ h.poincare.L :=
  (Scheme.Modules.pullbackCongr (baseChangeSnd_id c P.toBase)).app h.poincare.L ≪≫
    (Scheme.Modules.pullbackId _).app h.poincare.L

/-- The multiplication-by-n parameter classifies the n-th tensor power. -/
def poincareNsmulIsoTensorPower (n : ℕ) :
    (h.poincare.pullbackAlong
      ((h.relativeGroupLaw (P := algEquivZeroGroupCut c s)).nsmul P.toBase n
        ⟨𝟙 _, Category.id_comp _⟩)).L ≅ h.poincare.L.tensorPow n := by
  let G := h.relativeGroupLaw (P := algEquivZeroGroupCut c s)
  letI := G.pointGroup P.toBase
  let a : SchemeHomOver P.toBase P.toBase := ⟨𝟙 _, Category.id_comp _⟩
  have hn : G.nsmul P.toBase n a = a ^ n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [G.nsmul_succ, ih, pow_succ]; rfl
  change (h.poincare.pullbackAlong (G.nsmul P.toBase n a)).L ≅ _
  rw [hn]
  exact (h.nonempty_poincare_pullbackAlong_pow_iso_tensorPow
      (P := algEquivZeroGroupCut c s) P.toBase a n).some ≪≫
    tensorPowerCongr (poincareIdentityIso h) n

/-- The universal point of the composite of relative Frobenius and Picard pullback. -/
def picardFrobeniusCompositePoint : SchemeHomOver P.toBase P.toBase :=
  postComp (picardPullback p h (twistRepresents p h))
    ⟨relative p P.toBase, relative_toBase p P.toBase⟩

/-- On the Poincare bundle the represented composite is the p-th tensor power.
The proof uses the sheaf Frobenius isomorphism, not a Cartier assumption. -/
def poincareFrobeniusCompositeIso :
    (h.poincare.pullbackAlong (picardFrobeniusCompositePoint p h)).L ≅
      h.poincare.L.tensorPow p := by
  let h' := twistRepresents p h
  let f : SchemeHomOver P.toBase (toBase p P.toBase) :=
    ⟨relative p P.toBase, relative_toBase p P.toBase⟩
  let q := picardPullback p h h'
  have hq : Nonempty ((h.poincare.pullbackAlong q).L ≅
      (h'.poincare.pullbackCurve (relative p c) (relative_toBase p c)
        (section_relative p c s)).L) :=
    h.classify_spec (toBase p P.toBase) _
      (FibrewiseAlgEquivZero.pullbackCurve (relative p c) (relative_toBase p c)
        (section_relative p c s) h'.poincare_mem)
  exact (h.poincare.pullbackAlongPullbackAlongIso' q f).symm ≪≫
    (Scheme.Modules.pullback (baseChangeSnd c f)).mapIso hq.some ≪≫
    (Scheme.Modules.pullbackComp _ _).app h'.poincare.L ≪≫
    (Scheme.Modules.pullbackCongr (productRelative_factor p c P.toBase)).app h'.poincare.L ≪≫
    (Scheme.Modules.pullback (productRelative p c P.toBase)).mapIso
      ((twistRepresents_poincare p h).some ≪≫ twistPoincareIsoProjection p h) ≪≫
    (Scheme.Modules.pullbackComp _ _).app h.poincare.L ≪≫
    (Scheme.Modules.pullbackCongr (productRelative_projection p c P.toBase)).app h.poincare.L ≪≫
    FrobeniusLineBundle.pullbackIsoTensorPower p (Fact.out : p.Prime)
      (globalChar p (pullback.snd c P.toBase ≫ P.toBase)) h.poincare.isInvertible

/-- Actual curve-Frobenius Picard pullback factors multiplication by p through
the independent relative Frobenius of the representing scheme. -/
theorem frobenius_picardPullback :
    relative p P.toBase ≫ (picardPullback p h (twistRepresents p h)).1 =
      (h.relativeGroupLaw (P := algEquivZeroGroupCut c s)).schemeNsmul p := by
  have he := h.ext_of_iso P.toBase (picardFrobeniusCompositePoint p h)
    ((h.relativeGroupLaw (P := algEquivZeroGroupCut c s)).nsmul P.toBase p
      ⟨𝟙 _, Category.id_comp _⟩)
    ⟨poincareFrobeniusCompositeIso p h ≪≫ (poincareNsmulIsoTensorPower h p).symm⟩
  exact congrArg Subtype.val he

end SupersingularCurves.Geometry.SchemeFrobenius

namespace SupersingularCurves.Geometry.Jacobian
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p] [PerfectField K]
variable {F : Type v} [Field F] [Algebra K F]
variable {M : CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (J : Jacobian M s)

omit [PerfectField K] in
/-- Curve-Frobenius Picard pullback composed with Jacobian Frobenius is [p]. -/
theorem frobenius_frobeniusPicardPullback :
    J.relativeFrobenius p ≫ J.frobeniusPicardPullback p = J.groupLaw.schemeNsmul p :=
  SchemeFrobenius.frobenius_picardPullback p J.represents

/-- Actual equality with the independently descended Jacobian Verschiebung. -/
theorem frobeniusPicardPullback_eq_verschiebung :
    J.frobeniusPicardPullback p = J.verschiebung p :=
  J.verschiebung_unique p _ (J.frobenius_frobeniusPicardPullback p)

/-- Equality of the two actual local-ring cotangent differentials, with the
Frobenius twist retained. Identifying these with curve Cartier is a further step. -/
theorem frobeniusPicardPullbackCotangent_eq_verschiebungCotangent :
    J.frobeniusPicardPullbackCotangent p = J.verschiebungCotangent p := by
  unfold frobeniusPicardPullbackCotangent verschiebungCotangent
  congr 1
  exact J.frobeniusPicardPullback_eq_verschiebung p

end SupersingularCurves.Geometry.Jacobian
