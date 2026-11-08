/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentBasis
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentPresentation
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentEquivariance

/-!
# An actual finite Frobenius-equivariant projective presentation

For an abelian variety with zero actual Verschiebung cotangent, every datum
is constructed: the semilinear automorphism, invariant invertible sheaf,
fixed full section system, and its actual finite map to projective space.
Finiteness is distinguished from a closed immersion. The theorem does not
assert that a descended projective image is a model of the abelian variety.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian SchemeFrobenius FrobeniusFiniteFieldDescent

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p]

local instance : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth g A.group.X.hom

/-- The actual semilinear automorphism and an actual finite projective map
with a full system of fixed global sections, constructed from dV = 0. -/
theorem exists_frobeniusSquare_fixed_finite_projective_presentation
    (hV : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0) :
    ∃ (τ : A.group.X.left ≅ A.group.X.left) (M : A.group.X.left.Modules)
      (eM : (Scheme.Modules.pullback τ.hom).obj M ≅ M)
      (n : ℕ) (P : M.ProjPresentation A.group.X.hom n),
      τ.hom ≫ A.group.X.hom = A.group.X.hom ≫ baseMap p K ≫ baseMap p K ∧
      (GroupScheme.law A.group).schemeNsmul p ≫ τ.hom =
        absolute p A.group.X.hom ≫ absolute p A.group.X.hom ∧
      Scheme.Modules.IsInvertible M ∧ IsFinite P.toProj ∧
      Scheme.Modules.IsSectionBasis A.group.X.hom M P.σ ∧
      (∀ i, actionAddHom τ M eM (P.σ i) = P.σ i) := by
  obtain ⟨τ, M, eM, hτ, hp, hM, ⟨N, P, hP⟩, hb⟩ :=
    A.exists_frobeniusSquare_invariant_section_basis p hV
  let := sectionsModule M A.group.X.hom
  let : Module.Finite K Γ(M, ⊤) :=
    abelianVariety_finite_sections A M hM
  have : Nonempty A.group.X.left :=
    ⟨((GroupScheme.law A.group).one (𝟙 (Spec (CommRingCat.of K)))).1
      (IsLocalRing.closedPoint K)⟩
  have : IsFinite P.toProj := hP
  obtain ⟨b, hb, _⟩ := hb
  obtain ⟨n, Q, hQ, hsection, hfixed⟩ :=
    exists_finitePresentation_fixed A.group.X.hom M P (actionAddHom τ M eM) b hb
  exact ⟨τ, M, eM, n, Q, hτ, hp, hM, hQ, hsection, hfixed⟩

/-- The constructed finite map is equivariant for the actual semilinear
scheme automorphism and coefficient Frobenius squared on projective space. -/
theorem exists_frobeniusSquare_equivariant_finite_projective_presentation
    (hV : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0) :
    ∃ (τ : A.group.X.left ≅ A.group.X.left) (M : A.group.X.left.Modules)
      (eM : (Scheme.Modules.pullback τ.hom).obj M ≅ M)
      (n : ℕ) (P : M.ProjPresentation A.group.X.hom n),
      τ.hom ≫ A.group.X.hom = A.group.X.hom ≫ baseMap p K ≫ baseMap p K ∧
      (GroupScheme.law A.group).schemeNsmul p ≫ τ.hom =
        absolute p A.group.X.hom ≫ absolute p A.group.X.hom ∧
      Scheme.Modules.IsInvertible M ∧ IsFinite P.toProj ∧
      Scheme.Modules.IsSectionBasis A.group.X.hom M P.σ ∧
      (∀ i, actionAddHom τ M eM (P.σ i) = P.σ i) ∧
      τ.hom ≫ P.toProj = P.toProj ≫ coefficientFrobeniusSquare p K n := by
  obtain ⟨τ, M, eM, n, P, hτ, hp, hM, hP, hb, hfixed⟩ :=
    A.exists_frobeniusSquare_fixed_finite_projective_presentation p hV
  exact ⟨τ, M, eM, n, P, hτ, hp, hM, hP, hb, hfixed,
    toProj_frobeniusSquare_equivariant_of_fixed_sections τ M eM A.group.X.hom
      p hτ P hfixed⟩

end SupersingularCurves.Geometry.AbelianVariety
