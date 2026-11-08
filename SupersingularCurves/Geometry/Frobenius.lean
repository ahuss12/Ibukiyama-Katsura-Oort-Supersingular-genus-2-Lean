/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.JacobianInfinitesimal
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius
import Theorems.Thm_AlgebraicGeometry_Smooth_isFinite_and_flat_and_surjective_of_isPullback_frobenius

/-!
# Relative Frobenius and its actual Picard pullback

The relative Frobenius is a morphism of schemes to the Frobenius base change.
For a smooth scheme over a perfect field it is finite, flat and surjective.
For pointed curves its pullback on independently representing Picard schemes
is constructed by pulling back the actual Poincare line bundle.

The Picard pullback below is not yet identified with Jacobian Verschiebung:
that additionally requires the Picard base-change identification and the
multiplication-by-p factorization. No Cartier operator is used here.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.SchemeFrobenius
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

variable (p : ℕ) [Fact p.Prime]

theorem powerRingHom_one (R : Type u) [CommRing R] [CharP R p]
    (hR : (p : R) = 0) :
    powCharRingHom R p 1 (Fact.out : p.Prime) hR = frobenius R p := by
  ext x
  simp [frobenius_def]

/-- Absolute Frobenius of the base field, as a scheme morphism. -/
def baseMap (K : Type u) [Field K] [CharP K p] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (frobenius K p))

variable {K : Type u} [Field K] [CharP K p]
variable {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K))

include c in
theorem globalChar : (p : Γ(X, ⊤)) = 0 := by
  have h := congrArg c.appTop
    (Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero K p))
  simpa using h

theorem baseMap_eq_absolute :
    (Spec (CommRingCat.of K)).frobenius p 1 (Fact.out : p.Prime)
      (Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero K p)) = baseMap p K := by
  rw [Scheme.frobenius_Spec p 1 (Fact.out : p.Prime) (CharP.cast_eq_zero K p),
    powerRingHom_one p K (CharP.cast_eq_zero K p)]
  rfl

/-- Absolute Frobenius on the actual total scheme. -/
def absolute : X ⟶ X := X.frobenius p 1 (Fact.out : p.Prime) (globalChar p c)

/-- The actual fibre product defining the Frobenius twist. -/
abbrev Twist := pullback c (baseMap p K)

def projection : Twist p c ⟶ X := pullback.fst c (baseMap p K)

def toBase : Twist p c ⟶ Spec (CommRingCat.of K) := pullback.snd c (baseMap p K)

theorem absolute_over : absolute p c ≫ c = c ≫ baseMap p K := by
  rw [← baseMap_eq_absolute p]
  exact Scheme.frobenius_comp c p 1 (Fact.out : p.Prime) _ _

/-- Relative Frobenius, defined by the universal property of the fibre product. -/
def relative : X ⟶ Twist p c :=
  pullback.lift (absolute p c) c (absolute_over p c)

@[reassoc (attr := simp)]
theorem relative_projection : relative p c ≫ projection p c = absolute p c :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem relative_toBase : relative p c ≫ toBase p c = c :=
  pullback.lift_snd _ _ _

/-- On every affine test scheme the defining map is the actual p-power map. -/
theorem relative_on_affine (B : Type u) [CommRing B] [CharP B p]
    (x : Spec (CommRingCat.of B) ⟶ X) :
    x ≫ relative p c ≫ projection p c =
      Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x := by
  rw [relative_projection]
  have h := Scheme.frobenius_comp x p 1 (Fact.out : p.Prime)
    (Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero B p)) (globalChar p c)
  rw [Scheme.frobenius_Spec p 1 (Fact.out : p.Prime) (CharP.cast_eq_zero B p),
    powerRingHom_one p B (CharP.cast_eq_zero B p)] at h
  exact h.symm

/-- The constructed relative Frobenius is finite faithfully flat for a smooth
scheme over a perfect field. These are scheme properties, not point counts. -/
theorem finite_flat_surjective [PerfectField K] [Smooth c] :
    IsFinite (relative p c) ∧ Flat (relative p c) ∧
      LocallyOfFinitePresentation (relative p c) ∧ Surjective (relative p c) := by
  exact Smooth.isFinite_and_flat_and_surjective_of_isPullback_frobenius
    K p c (toBase p c) (projection p c)
    (IsPullback.of_hasPullback c (baseMap p K))
    (relative p c) (relative_toBase p c) (relative_on_affine p c)

variable (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)

/-- The base-changed rational section on the actual twist. -/
def twistedSection : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (toBase p c) :=
  ⟨pullback.lift (baseMap p K ≫ s.1) (𝟙 _)
      (by simp only [Category.assoc, s.2, Category.comp_id, Category.id_comp]),
    pullback.lift_snd _ _ _⟩

/-- Relative Frobenius is a pointed morphism for the base-changed section. -/
theorem section_relative : s.1 ≫ relative p c = (twistedSection p c s).1 := by
  apply pullback.hom_ext
  · change (s.1 ≫ relative p c) ≫ projection p c = _
    rw [Category.assoc, relative_projection]
    simp only [twistedSection, pullback.lift_fst]
    have h := Scheme.frobenius_comp s.1 p 1 (Fact.out : p.Prime)
      (Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero K p)) (globalChar p c)
    rw [baseMap_eq_absolute] at h
    exact h.symm
  · change (s.1 ≫ relative p c) ≫ toBase p c = _
    rw [Category.assoc, relative_toBase]
    simpa only [twistedSection, pullback.lift_snd] using s.2

variable {c s}
variable {D : RelativePic0Designation K c}
  {D' : RelativePic0Designation K (toBase p c)}
variable (h : RepresentsRelSubPic c s (algEquivZeroCut c s) D)
  (h' : RepresentsRelSubPic (toBase p c) (twistedSection p c s)
    (algEquivZeroCut (toBase p c) (twistedSection p c s)) D')

/-- Pullback by the actual curve relative Frobenius on independently
representing Picard schemes. The Verschiebung identification is a further theorem. -/
def picardPullback : SchemeHomOver D'.toBase D.toBase :=
  RepresentsRelSubPic.pullbackHom (relative p c) (relative_toBase p c)
    (section_relative p c s) h' h

/-- The map classifies pullback of each actual line bundle, on every test scheme. -/
theorem picardPullback_classify {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (L : RigidifiedLineBundle (toBase p c) (twistedSection p c s) t)
    (hL : (algEquivZeroCut (toBase p c) (twistedSection p c s)).P t L) :
    postComp (picardPullback p h h') (h'.classify t L hL) =
      h.classify t
        (L.pullbackCurve (relative p c) (relative_toBase p c) (section_relative p c s))
        (FibrewiseAlgEquivZero.pullbackCurve (relative p c) (relative_toBase p c)
          (section_relative p c s) hL) :=
  RepresentsRelSubPic.postComp_pullbackHom_classify _ _ _ h' h t L hL

theorem picardPullback_zero :
    D'.zeroSection ≫ (picardPullback p h h').1 = D.zeroSection :=
  RepresentsRelSubPic.zeroSection_pullbackHom _ _ _ h' h

end SupersingularCurves.Geometry.SchemeFrobenius
