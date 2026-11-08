/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.Jacobian
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Theorems.Thm_AlgebraicCurve_CurveModel_finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic

/-!
# Infinitesimal points of the independently representing Jacobian

The comparison here uses the actual Poincare line bundle on the representing
Jacobian. A tangent point is a morphism from a square-zero thickening, and its
image is the isomorphism class of the pulled-back line bundle. The inverse is
provided by Picard representability. The comparison is natural under changes
of the square-zero coefficient module and under pointed curve morphisms.

This is an infinitesimal Picard comparison, not a Cartier--Verschiebung theorem.
No Cartier operator or supersingularity predicate enters any construction.
The pinned upstream `P2mTJ` helpers implement the Poincare pullback and its
inverse; they are reused with their original definitions and proofs.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace SupersingularCurves.Geometry
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian

namespace InfinitesimalPicard

variable {K : Type u} [Field K] {C : Scheme.{u}}
variable (c : C ⟶ Spec (CommRingCat.of K))
variable (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
variable (V : Type u) [AddCommGroup V] [Module K V]
  [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

/-- Isomorphism of the underlying rigidified line bundles, in the convention
used by the representing Picard functor. -/
def deformationSetoid : Setoid (TrivialModDeformations c s V) where
  r L L' := Nonempty (L.1.L ≅ L'.1.L)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e ≪≫ e'⟩⟩

/-- First-order line-bundle deformation classes on the actual curve. -/
abbrev DeformationClasses := Quotient (deformationSetoid c s V)

/-- The class of a line bundle whose special fibre is trivial. -/
def deformationClass (L : TrivialModDeformations c s V) : DeformationClasses c s V :=
  Quotient.mk _ L

variable {c s V}

theorem deformationClass_eq_iff (L L' : TrivialModDeformations c s V) :
    deformationClass c s V L = deformationClass c s V L' ↔
      Nonempty (L.1.L ≅ L'.1.L) := Quotient.eq

variable {W : Type u} [AddCommGroup W] [Module K W]
  [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

/-- Change the coefficient module of an actual first-order deformation. -/
def mapCoefficients (φ : V →ₗ[K] W) :
    DeformationClasses c s V → DeformationClasses c s W :=
  Quotient.map (fun L => L.map φ) (fun _ _ h =>
    RigidifiedLineBundle.pullbackAlong_congr (SquareZero.specMapOver K φ) h)

variable {C' : Scheme.{u}} {c' : C' ⟶ Spec (CommRingCat.of K)}
  {s' : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c'}
variable (f : C' ⟶ C) (hf : f ≫ c = c') (hs : s'.1 ≫ f = s.1)

/-- Pull back a first-order deformation along a pointed curve morphism. -/
def pullbackDeformation (L : TrivialModDeformations c s V) :
    TrivialModDeformations c' s' V :=
  ⟨L.1.pullbackCurve f hf hs, ⟨
    L.1.pullbackCurvePullbackAlongIso f hf hs (SquareZero.basePointOver K V) ≪≫
      (Scheme.Modules.pullback _).mapIso L.2.some ≪≫
      RigidifiedLineBundle.unitPullbackCurveIso f hf hs _⟩⟩

/-- Pullback on deformation classes, induced by scheme-theoretic pullback. -/
def pullbackClasses : DeformationClasses c s V → DeformationClasses c' s' V :=
  Quotient.map (pullbackDeformation f hf hs) (fun _ _ h =>
    RigidifiedLineBundle.pullbackCurve_congr f hf hs h)

end InfinitesimalPicard

namespace Jacobian

open InfinitesimalPicard
open P2MW.S_AlgebraicCurve_CurveModel_finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
variable {M : AlgebraicCurve.CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (J : Jacobian M s)
variable (V : Type u) [AddCommGroup V] [Module K V]
  [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

/-- Actual infinitesimal points at the zero section of the Jacobian scheme. -/
abbrev InfinitesimalPoints :=
  TangentPoints J.designation.toBase J.designation.zeroSection V

/-- Pull back the independently constructed Poincare bundle along a tangent
point. Its reduction is trivial because the tangent point lies over zero. -/
def poincareDeformation (t : J.InfinitesimalPoints V) :
    TrivialModDeformations M.toBase s V := P2mTJ.defOf J.represents t

/-- The comparison is the actual Poincare pullback, not a dimension argument. -/
def infinitesimalClass (t : J.InfinitesimalPoints V) :
    DeformationClasses M.toBase s V :=
  deformationClass _ _ _ (J.poincareDeformation V t)

theorem infinitesimalClass_bijective : Function.Bijective (J.infinitesimalClass V) := by
  constructor
  · intro t t' h
    have hiso := (deformationClass_eq_iff
      (J.poincareDeformation V t) (J.poincareDeformation V t')).mp h
    apply P2mTJ.defOf_injective J.represents
    exact Quotient.sound hiso
  · intro q
    induction q using Quotient.inductionOn with
    | h L =>
      obtain ⟨t, ht⟩ := P2mTJ.exists_defOf_iso J.represents L
      exact ⟨t, Quotient.sound ht⟩

/-- The infinitesimal Picard comparison for every coefficient module. -/
def infinitesimalPicardEquiv :
    J.InfinitesimalPoints V ≃ DeformationClasses M.toBase s V :=
  Equiv.ofBijective (J.infinitesimalClass V) (J.infinitesimalClass_bijective V)

variable {V}
variable {W : Type u} [AddCommGroup W] [Module K W]
  [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

/-- Naturality in the square-zero coefficient module. -/
theorem infinitesimalPicardEquiv_mapCoefficients (φ : V →ₗ[K] W)
    (t : J.InfinitesimalPoints V) :
    J.infinitesimalPicardEquiv W (t.map φ) =
      mapCoefficients φ (J.infinitesimalPicardEquiv V t) := by
  exact Quotient.sound (P2mTJ.nonempty_iso_defOf_map J.represents φ t)

variable {F' : Type w} [Field F'] [Algebra K F']
  {M' : AlgebraicCurve.CurveModel K F'}
  {s' : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M'.toBase}
variable (J' : Jacobian M' s')
variable (f : M'.C ⟶ M.C) (hf : f ≫ M.toBase = M'.toBase)
  (hs : s'.1 ≫ f = s.1)

/-- The tangent map of the actual morphism of Picard-representing schemes
induced by curve pullback. -/
def pullbackInfinitesimalPoint (t : J.InfinitesimalPoints V) :
    J'.InfinitesimalPoints V :=
  ⟨t.1 ≫ (RepresentsRelSubPic.pullbackHom f hf hs J.represents J'.represents).1,
    by rw [Category.assoc,
      (RepresentsRelSubPic.pullbackHom f hf hs J.represents J'.represents).2, t.2.1],
    by rw [← Category.assoc, t.2.2,
      RepresentsRelSubPic.zeroSection_pullbackHom]⟩

/-- The infinitesimal Picard comparison commutes with actual curve pullback. -/
theorem infinitesimalPicardEquiv_pullback (t : J.InfinitesimalPoints V) :
    J'.infinitesimalPicardEquiv V (J.pullbackInfinitesimalPoint J' f hf hs t) =
      pullbackClasses f hf hs (J.infinitesimalPicardEquiv V t) := by
  apply Quotient.sound
  change Nonempty
    ((J'.represents.poincare.pullbackAlong
      (postComp (RepresentsRelSubPic.pullbackHom f hf hs J.represents J'.represents)
        (P2mTJ.toOver t))).L ≅
      ((J.represents.poincare.pullbackAlong (P2mTJ.toOver t)).pullbackCurve f hf hs).L)
  exact ⟨(J'.represents.poincare.pullbackAlongPullbackAlongIso' _ _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso
      (J'.represents.classify_spec _ _ _).some ≪≫
    J.represents.poincare.pullbackCurvePullbackAlongIso f hf hs (P2mTJ.toOver t)⟩

end Jacobian
end SupersingularCurves.Geometry
