/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Mathlib

/-!
# Abelian varieties, geometric isomorphisms, and isogenies

The underlying objects are actual schemes over `Spec K` with Mathlib group
objects, hence scheme group laws on every test scheme. Smoothness, properness,
geometric connectedness, and relative dimension are genuine scheme properties.
An isogeny is a finite surjective morphism of these group schemes.
No abstract point group is substituted for a group scheme.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SupersingularCurves.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

abbrev GroupScheme (K : Type u) [Field K] := Grp (Over (Spec (CommRingCat.of K)))

/-- An abelian variety of specified dimension, without a chosen polarization. -/
structure AbelianVariety (K : Type u) [Field K] (g : ℕ) where
  group : GroupScheme K
  [comm : IsCommMonObj group.X]
  [smooth : SmoothOfRelativeDimension g group.X.hom]
  [proper : IsProper group.X.hom]
  [connected : GeometricallyConnected group.X.hom]

attribute [instance] AbelianVariety.comm AbelianVariety.smooth
  AbelianVariety.proper AbelianVariety.connected

variable {K : Type u} [Field K]

/-- Forget the group law and the structure morphism to obtain the actual scheme. -/
def underlyingScheme : GroupScheme K ⥤ Scheme :=
  Grp.forget _ ⋙ Over.forget _

/-- Finite and surjective as a morphism of schemes, not merely on K-points. -/
def IsIsogeny {G H : GroupScheme K} (f : G ⟶ H) : Prop :=
  IsFinite (underlyingScheme.map f) ∧ Surjective (underlyingScheme.map f)

/-- A group-scheme isomorphism is in particular an isogeny. -/
theorem isIsogeny_of_isIso {G H : GroupScheme K} (f : G ⟶ H) [IsIso f] :
    IsIsogeny f := by
  exact ⟨inferInstance, inferInstance⟩

theorem IsIsogeny.comp {G H J : GroupScheme K} {f : G ⟶ H} {h : H ⟶ J}
    (hf : IsIsogeny f) (hh : IsIsogeny h) : IsIsogeny (f ≫ h) := by
  let := hf.1
  let := hf.2
  let := hh.1
  let := hh.2
  unfold IsIsogeny
  rw [Functor.map_comp]
  exact ⟨inferInstance, inferInstance⟩

/-- The genuine finite product in the category of group schemes. -/
def ellipticProduct {g : ℕ} (E : Fin g → AbelianVariety K 1) : GroupScheme K :=
  ∏ᶜ fun i => (E i).group

namespace AbelianVariety
variable {g : ℕ}

/-- K-valued points, with the group structure induced by the scheme group law. -/
abbrev Points (A : AbelianVariety K g) :=
  Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.group.X

open scoped CategoryTheory.MonObj

instance pointsCommGroup (A : AbelianVariety K g) : CommGroup A.Points := inferInstance

/-- Base change of the actual abelian variety along a field extension. -/
def baseChange (A : AbelianVariety K g) (L : Type u) [Field L] [Algebra K L] :
    AbelianVariety L g where
  group := ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapGrp).obj A.group
  comm := ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapCommMon.obj
    ⟨A.group.X⟩).comm
  smooth := by
    change SmoothOfRelativeDimension g (pullback.snd A.group.X.hom _)
    exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback A.group.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) A.smooth
  proper := by
    change IsProper (pullback.snd A.group.X.hom _)
    infer_instance
  connected := by
    change GeometricallyConnected (pullback.snd A.group.X.hom _)
    infer_instance

end AbelianVariety
end SupersingularCurves.Geometry
