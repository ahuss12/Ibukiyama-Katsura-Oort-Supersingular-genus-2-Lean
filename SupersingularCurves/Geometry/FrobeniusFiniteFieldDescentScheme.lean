/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentFixedGrading
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentSectionModel
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentFiniteSections
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentTensor

/-!
# The genuine underlying scheme over the finite Frobenius-fixed field

Zero Verschiebung cotangent constructs an actual invariant invertible bundle
and semilinear automorphism. Its full section ring recovers the original
scheme; the fixed graded subalgebra gives a scheme over the field with p²
elements whose scalar extension is the original scheme. This result does
not yet descend the group law, identity, or inverse.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry
namespace FrobeniusFiniteFieldDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FrobeniusDescent FrobeniusFiniteFieldDescentSectionProj

variable {K : Type u} [Field K] [IsAlgClosed K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K)) [IsProper c]
variable (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
variable (hfinite : M.FiniteBySections c)
variable (τ : X ≅ X) (eM : (Scheme.Modules.pullback τ.hom).obj M ≅ M)
variable (hτ : τ.hom ≫ c = c ≫ (SchemeFrobenius.baseMap p K ≫ SchemeFrobenius.baseMap p K))

include hM hfinite eM hτ in
/-- A proper scheme with the actual compatible invariant bundle has a genuine
model over the p²-element subfield, with a proved geometric base-change square. -/
theorem exists_fixedField_scheme_model :
    ∃ (X₀ : Scheme.{u}) (c₀ : X₀ ⟶ Spec (CommRingCat.of (fixedField K p 2)))
      (d : X ⟶ X₀),
      IsPullback d c c₀
        (Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K))) := by
  obtain ⟨R, _, _, 𝓡, _, ι, e, hR, he⟩ :=
    exists_sectionRing_model_of_finiteBySections c M hM hfinite
  let θ := sectionRingAction τ M eM c R 𝓡 ι hR
  have hθ : ∀ (a : K) (x : R), θ (a • x) = a ^ (p ^ 2) • θ x :=
    sectionRingAction_frobeniusSquare_smul τ M eM c R 𝓡 ι hR p hτ
  have hd : ∀ n, ∀ x ∈ 𝓡 n, θ x ∈ 𝓡 n :=
    sectionRingAction_mem τ M eM c R 𝓡 ι hR
  have hi : Function.Injective θ := sectionRingAction_injective τ M eM c R 𝓡 ι hR
  have hf : ∀ n, FiniteDimensional K (𝓡 n) := by
    intro n
    let := sectionsModule (M.tensorPow n) c
    let := finite_sections_of_isProper (M.tensorPow n) c (hM.tensorPow n)
    exact (sectionRingDegreeLinearEquiv M c R 𝓡 ι hR n).symm.finiteDimensional
  obtain ⟨X₀, c₀, d, hpb⟩ :=
    exists_fixedField_proj_model p 2 θ hθ 𝓡 hd (by decide) hi hf
  refine ⟨X₀, c₀, e.hom ≫ d, ?_⟩
  have hs : IsPullback e.hom c
      (Proj.toSpecZero 𝓡 ≫ Spec.map (CommRingCat.ofHom
        ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap K R))))
      (𝟙 (Spec (CommRingCat.of K))) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.assoc, Category.comp_id]
      using he.comp_toSpecZero⟩
  simpa only [Category.id_comp] using hs.paste_horiz hpb

end FrobeniusFiniteFieldDescent

namespace AbelianVariety
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FrobeniusDescent FrobeniusFiniteFieldDescent

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p]

local instance : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth g A.group.X.hom

/-- From zero actual Verschiebung cotangent, the underlying scheme descends
to the actual subfield with p² elements. No model or descent datum is assumed. -/
theorem exists_finiteField_scheme_model_of_verschiebungCotangent_eq_zero
    (hV : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0) :
    Finite (fixedField K p 2) ∧ Nat.card (fixedField K p 2) = p ^ 2 ∧
    ∃ (X₀ : Scheme.{u}) (c₀ : X₀ ⟶ Spec (CommRingCat.of (fixedField K p 2)))
      (d : A.group.X.left ⟶ X₀),
      IsPullback d A.group.X.hom c₀
        (Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K))) := by
  obtain ⟨τ, M, hτ, _hp, hM, hfinite, ⟨eM⟩⟩ :=
    A.exists_frobeniusSquare_automorphism_invariant_bundle p hV
  exact ⟨fixedField_finite K p 2 (by decide), fixedField_natCard K p 2 (by decide),
    exists_fixedField_scheme_model p A.group.X.hom M hM hfinite τ eM hτ⟩

end AbelianVariety
end SupersingularCurves.Geometry
