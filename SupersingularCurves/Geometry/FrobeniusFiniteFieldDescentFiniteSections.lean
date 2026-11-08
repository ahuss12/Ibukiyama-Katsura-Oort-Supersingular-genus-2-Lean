/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianVariety
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentSections
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentLinear
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_finite_sections_of_isProper

/-!
# Finite global sections and fixed section bases

Properness makes the genuine global sections of an invertible sheaf finite
dimensional over the base field. A Frobenius-square-compatible automorphism
preserving the sheaf therefore admits a fixed basis of these actual sections.
No projective embedding or finite-dimensionality assumption is needed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- Properness and invertibility imply finite-dimensionality for the scalar
action defined by the actual structure morphism. -/
theorem finite_sections_of_isProper
    (M : X.Modules) (c : X ⟶ Spec (CommRingCat.of K)) [IsProper c]
    (hM : Scheme.Modules.IsInvertible M) :
    letI := sectionsModule M c
    FiniteDimensional K Γ(M, ⊤) := by
  have h := Scheme.Modules.IsInvertible.finite_sections_of_isProper K c M hM
  change @Module.Finite K Γ(M, ⊤) _ _
    (Module.compHom _ ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ ⊤ le_top).hom) at h
  rw [show c.appLE ⊤ ⊤ le_top = c.appTop from c.appLE_eq_app] at h
  exact h

/-- Every invertible sheaf on an actual abelian variety has finite-dimensional
global sections, with the scalar action from the abelian variety's base map. -/
theorem abelianVariety_finite_sections {g : ℕ} (A : AbelianVariety K g)
    (M : A.group.X.left.Modules) (hM : Scheme.Modules.IsInvertible M) :
    letI := sectionsModule M A.group.X.hom
    FiniteDimensional K Γ(M, ⊤) :=
  finite_sections_of_isProper M A.group.X.hom hM

/-- An actual Frobenius-square automorphism preserving an invertible sheaf on
a proper scheme admits a fixed basis of genuine global sections. -/
theorem exists_fixedSectionBasis [IsAlgClosed K]
    (M : X.Modules) (c : X ⟶ Spec (CommRingCat.of K)) [IsProper c]
    (hM : Scheme.Modules.IsInvertible M) (τ : X ≅ X)
    (eM : (Scheme.Modules.pullback τ.hom).obj M ≅ M)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hτ : τ.hom ≫ c =
      c ≫ (SchemeFrobenius.baseMap p K ≫ SchemeFrobenius.baseMap p K)) :
    letI := sectionsModule M c
    ∃ b : Module.Basis (Fin (Module.finrank K Γ(M, ⊤))) K Γ(M, ⊤),
      ∀ i, actionAddHom τ M eM (b i) = b i := by
  let := sectionsModule M c
  let : FiniteDimensional K Γ(M, ⊤) := finite_sections_of_isProper M c hM
  exact FrobeniusFiniteFieldDescentLinear.exists_fixedBasis p 2 (by decide)
    (actionAddHom τ M eM)
    (actionAddHom_frobeniusSquare_smul τ M eM c p hτ)
    (actionAddHom_injective τ M eM)

end SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
