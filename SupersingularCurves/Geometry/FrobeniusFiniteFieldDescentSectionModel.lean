/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentSectionIso

/-!
# The actual abelian variety as Proj of the invariant bundle's section ring

The semilinear automorphism and invariant invertible sheaf are constructed
from zero actual Verschiebung cotangent. The full section ring then recovers
the original scheme itself as Proj, using only the proved finite projective
presentation. This model is over the original field; coefficient descent is
a separate step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian SchemeFrobenius FrobeniusFiniteFieldDescent
open FrobeniusFiniteFieldDescentSectionProj

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p]

local instance : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth g A.group.X.hom

/-- The actual abelian variety is the Proj of the full section ring of an
actually constructed invariant invertible sheaf. All data follow from dV=0. -/
theorem exists_frobeniusSquare_sectionRing_model
    (hV : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0) :
    ∃ (τ : A.group.X.left ≅ A.group.X.left) (M : A.group.X.left.Modules)
      (_ : (Scheme.Modules.pullback τ.hom).obj M ≅ M),
      τ.hom ≫ A.group.X.hom = A.group.X.hom ≫ baseMap p K ≫ baseMap p K ∧
      (GroupScheme.law A.group).schemeNsmul p ≫ τ.hom =
        absolute p A.group.X.hom ≫ absolute p A.group.X.hom ∧
      Scheme.Modules.IsInvertible M ∧ M.FiniteBySections A.group.X.hom ∧
      ∃ (R : Type u) (_ : CommRing R) (_ : Algebra K R)
        (𝓡 : ℕ → Submodule K R) (_ : GradedAlgebra 𝓡)
        (ι : ∀ n : ℕ, 𝓡 n → Γ(M.tensorPow n, ⊤))
        (e : A.group.X.left ≅ Proj 𝓡),
        GradedOAlgebra.IsSectionRing A.group.X.hom M R 𝓡 ι ∧
        GradedOAlgebra.IsCanonicalToProj A.group.X.hom M R 𝓡 ι e.hom := by
  obtain ⟨τ, M, hτ, hp, hM, hfinite, ⟨eM⟩⟩ :=
    A.exists_frobeniusSquare_automorphism_invariant_bundle p hV
  exact ⟨τ, M, eM, hτ, hp, hM, hfinite,
    exists_sectionRing_model_of_finiteBySections A.group.X.hom M hM hfinite⟩

end SupersingularCurves.Geometry.AbelianVariety
