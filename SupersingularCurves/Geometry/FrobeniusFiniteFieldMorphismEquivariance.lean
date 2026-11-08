/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentEquivariantModel

/-!
# Equivariance of actual abelian-variety homomorphisms

Canonical semilinear Frobenius-square descent operators commute with all
actual group-scheme morphisms, by cancelling the finite faithfully flat
multiplication-by-p map. No arithmetic descent of homomorphisms or
elliptic-product classification is assumed here.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory AlgebraicGeometry GoodReductionJacobian SchemeFrobenius

variable {K : Type u} [Field K] [IsAlgClosed K] {g h : ℕ}
variable (A : AbelianVariety K g) (B : AbelianVariety K h)
variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Descent maps determined by F²=[p]τ are natural for every actual group homomorphism. -/
theorem frobeniusSquare_descent_natural
    (τA : A.group.X.left ⟶ A.group.X.left)
    (τB : B.group.X.left ⟶ B.group.X.left)
    (hA : (GroupScheme.law A.group).schemeNsmul p ≫ τA =
      absolute p A.group.X.hom ≫ absolute p A.group.X.hom)
    (hB : (GroupScheme.law B.group).schemeNsmul p ≫ τB =
      absolute p B.group.X.hom ≫ absolute p B.group.X.hom)
    (f : A.group ⟶ B.group) :
    τA ≫ f.hom.hom.left = f.hom.hom.left ≫ τB := by
  have hm := A.multiplication_finite_flat_degree p (Fact.out : p.Prime).ne_zero
  letI : IsFinite ((GroupScheme.law A.group).schemeNsmul p) := hm.2.2.1
  letI : Flat ((GroupScheme.law A.group).schemeNsmul p) := hm.2.2.2.1
  letI : Surjective ((GroupScheme.law A.group).schemeNsmul p) := ⟨hm.2.2.2.2.1⟩
  apply (cancel_epi ((GroupScheme.law A.group).schemeNsmul p)).mp
  have hF := Scheme.frobenius_comp f.hom.hom.left p 1 (Fact.out : p.Prime)
    (globalChar p A.group.X.hom) (globalChar p B.group.X.hom)
  change absolute p A.group.X.hom ≫ f.hom.hom.left =
    f.hom.hom.left ≫ absolute p B.group.X.hom at hF
  calc
    (GroupScheme.law A.group).schemeNsmul p ≫ τA ≫ f.hom.hom.left =
        (absolute p A.group.X.hom ≫ absolute p A.group.X.hom) ≫ f.hom.hom.left := by
          rw [← Category.assoc, hA]
    _ = f.hom.hom.left ≫ absolute p B.group.X.hom ≫ absolute p B.group.X.hom := by
          rw [Category.assoc, hF, ← Category.assoc, hF, Category.assoc]
    _ = f.hom.hom.left ≫ (GroupScheme.law B.group).schemeNsmul p ≫ τB := by
          simpa only [Category.assoc] using congrArg (fun t => f.hom.hom.left ≫ t) hB.symm
    _ = (GroupScheme.law A.group).schemeNsmul p ≫ f.hom.hom.left ≫ τB := by
          rw [← Category.assoc, ← GroupScheme.schemeNsmul_natural, Category.assoc]

/-- The Frobenius-square descent operator is unique as an actual scheme map. -/
theorem frobeniusSquare_descent_unique
    (τ₁ τ₂ : A.group.X.left ⟶ A.group.X.left)
    (h₁ : (GroupScheme.law A.group).schemeNsmul p ≫ τ₁ =
      absolute p A.group.X.hom ≫ absolute p A.group.X.hom)
    (h₂ : (GroupScheme.law A.group).schemeNsmul p ≫ τ₂ =
      absolute p A.group.X.hom ≫ absolute p A.group.X.hom) : τ₁ = τ₂ := by
  have hm := A.multiplication_finite_flat_degree p (Fact.out : p.Prime).ne_zero
  letI : IsFinite ((GroupScheme.law A.group).schemeNsmul p) := hm.2.2.1
  letI : Flat ((GroupScheme.law A.group).schemeNsmul p) := hm.2.2.2.1
  letI : Surjective ((GroupScheme.law A.group).schemeNsmul p) := ⟨hm.2.2.2.2.1⟩
  exact (cancel_epi ((GroupScheme.law A.group).schemeNsmul p)).mp (h₁.trans h₂.symm)

end SupersingularCurves.Geometry.AbelianVariety
