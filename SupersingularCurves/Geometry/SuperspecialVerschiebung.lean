/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AlgebraicallyClosedBaseChange
import SupersingularCurves.Geometry.EllipticVerschiebungVanishing
import SupersingularCurves.Geometry.CartierVerschiebung

/-!
# Geometric superspeciality forces zero Verschiebung differential

The geometric product isomorphism is transported back from the algebraic
closure to the already algebraically closed ground field. Independently
supersingular elliptic factors have zero actual Verschiebung differential;
the actual product and isomorphism theorems then imply vanishing on the
abelian variety. The independently constructed Jacobian operator and its
Cartier comparison give the corresponding curve theorem in every genus.

The reverse product-isomorphism classification is not asserted here.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian

namespace AbelianVariety
variable {K : Type u} [Field K] [IsAlgClosed K]
variable (p : ℕ) [Fact p.Prime] [CharP K p] {g : ℕ}

/-- Independent geometric product-isomorphism superspeciality implies
vanishing of actual Verschiebung on the cotangent space, in every dimension. -/
theorem IsSuperspecial.verschiebungCotangent_eq_zero
    {A : AbelianVariety K g} (h : A.IsSuperspecial p) :
    GroupScheme.verschiebungCotangent p A.group
      (GroupScheme.law_commutative A.group) = 0 := by
  obtain ⟨E, hE, ⟨e⟩⟩ := (isSuperspecial_iff_isSuperspecialOver p A).mp h
  exact A.verschiebungCotangent_zero_of_product_iso p E e
    (fun i => IsSupersingularElliptic.verschiebungCotangent_eq_zero p (hE i))

end AbelianVariety

namespace Jacobian
variable {K : Type u} [Field K] [IsAlgClosed K]
variable {F : Type v} [Field F] [Algebra K F]
variable {M : CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The conclusion concerns the pre-existing, independently constructed
Jacobian Verschiebung cotangent map. -/
theorem IsSuperspecial.verschiebungCotangent_eq_zero
    {J : Jacobian M s} (h : J.IsSuperspecial p) :
    J.verschiebungCotangent p = 0 := by
  apply (J.groupScheme_verschiebungCotangent_eq_zero_iff p).mp
  exact AbelianVariety.IsSuperspecial.verschiebungCotangent_eq_zero p h

variable [Algebra.EssFiniteType K F] [IsCurveOver K F]
variable (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

/-- Geometric superspeciality forces the actual Cartier operator to
vanish on the entire global differential space of a supplied curve chart. -/
theorem IsSuperspecial.globalCartier_eq_zero
    {J : Jacobian M s} (h : J.IsSuperspecial p) (V : DifferentialChart M) :
    V.globalCartier p x = 0 :=
  (J.verschiebungCotangent_eq_zero_iff V p x).mp
    (IsSuperspecial.verschiebungCotangent_eq_zero p h)

end Jacobian
end SupersingularCurves.Geometry
