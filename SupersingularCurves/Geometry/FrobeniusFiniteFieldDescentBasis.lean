/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentFiniteSections

/-!
# Fixed actual sections for an abelian variety with zero Verschiebung cotangent

All the data are constructed from the actual abelian variety: the semilinear
scheme automorphism, its invariant invertible sheaf with a finite projective
presentation, and a fixed basis of the finite-dimensional global sections.
The induced action in these coordinates is p²-power Frobenius. A descended
scheme or a projective closed immersion is not assumed or asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory AlgebraicGeometry
open GoodReductionJacobian SchemeFrobenius FrobeniusFiniteFieldDescent

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p]

local instance : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth g A.group.X.hom

/-- Zero actual Verschiebung cotangent constructs fixed coordinates on the
actual global sections of an invariant invertible sheaf with finite
projective presentation. Every datum is derived from the abelian variety. -/
theorem exists_frobeniusSquare_invariant_section_basis
    (hV : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0) :
    ∃ (τ : A.group.X.left ≅ A.group.X.left) (M : A.group.X.left.Modules)
      (eM : (Scheme.Modules.pullback τ.hom).obj M ≅ M),
      τ.hom ≫ A.group.X.hom = A.group.X.hom ≫ baseMap p K ≫ baseMap p K ∧
      (GroupScheme.law A.group).schemeNsmul p ≫ τ.hom =
        absolute p A.group.X.hom ≫ absolute p A.group.X.hom ∧
      Scheme.Modules.IsInvertible M ∧
      M.FiniteBySections A.group.X.hom ∧
      (letI := sectionsModule M A.group.X.hom
       ∃ b : Module.Basis (Fin (Module.finrank K Γ(M, ⊤))) K Γ(M, ⊤),
         (∀ i, actionAddHom τ M eM (b i) = b i) ∧
         ∀ s, b.equivFun (actionAddHom τ M eM s) =
           fun i => (b.equivFun s i) ^ (p ^ 2)) := by
  obtain ⟨τ, M, hτ, hp, hM, hfinite, ⟨eM⟩⟩ :=
    A.exists_frobeniusSquare_automorphism_invariant_bundle p hV
  refine ⟨τ, M, eM, hτ, hp, hM, hfinite, ?_⟩
  let := sectionsModule M A.group.X.hom
  obtain ⟨b, hb⟩ := exists_fixedSectionBasis M A.group.X.hom hM τ eM p hτ
  refine ⟨b, hb, ?_⟩
  exact FrobeniusFiniteFieldDescentLinear.equivFun_apply_eq_pow p 2
    (actionAddHom τ M eM)
    (actionAddHom_frobeniusSquare_smul τ M eM A.group.X.hom p hτ) b hb

end SupersingularCurves.Geometry.AbelianVariety
