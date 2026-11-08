/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingImage

/-!
# Uniqueness of finite-level Verschiebung from actual torsion geometry

The actual projection A[p²]→A[p] is an epimorphism and the inclusion
A[p]→A[p²] is a monomorphism. These facts prove uniqueness from the two
Frobenius composition identities and the indicated level compatibilities.
The maps being compared can be semilinear scheme maps: they are not assumed
to be morphisms over the base field.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.TorsionLevels
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
  (A : AbelianVariety K g)

/-- Compare an ambient restriction with the Cartier-dual construction using
actual consecutive torsion schemes. No abstract image or descent datum is
supplied: cancellation uses the geometric maps constructed from A. -/
theorem eq_of_two_level_frobenius_identities (p : ℕ) (hp : p ≠ 0)
    (F V₁ W₁ : kernel A (p * p) ⟶ kernel A (p * p))
    (V₀ W₀ : kernel A p ⟶ kernel A p)
    (hV : V₀ ≫ smallerToLarger A p p = smallerToLarger A p p ≫ V₁)
    (hW : multiplication A p p ≫ W₀ = W₁ ≫ multiplication A p p)
    (hWF : W₁ ≫ F = squareMultiplication A p)
    (hFV : F ≫ V₁ = squareMultiplication A p) : V₀ = W₀ := by
  letI := multiplication_flat A p p hp
  letI := multiplication_surjective A p p hp
  letI : Epi (multiplication A p p) :=
    Flat.epi_of_flat_of_surjective (multiplication A p p)
  apply (cancel_epi (multiplication A p p)).mp
  apply (cancel_mono (smallerToLarger A p p)).mp
  calc
    (multiplication A p p ≫ V₀) ≫ smallerToLarger A p p =
        (multiplication A p p ≫ smallerToLarger A p p) ≫ V₁ := by
          rw [Category.assoc, hV, ← Category.assoc]
    _ = (W₁ ≫ F) ≫ V₁ := by rw [hWF]; rfl
    _ = W₁ ≫ squareMultiplication A p := by rw [Category.assoc, hFV]
    _ = (multiplication A p p ≫ W₀) ≫ smallerToLarger A p p := by
      rw [hW, Category.assoc]
      rfl

/-- The same comparison with the actual absolute Frobenius of A[p²]. -/
theorem eq_of_two_level_absoluteFrobenius (p : ℕ) [Fact p.Prime] [CharP K p]
    (V₁ W₁ : kernel A (p * p) ⟶ kernel A (p * p))
    (V₀ W₀ : kernel A p ⟶ kernel A p)
    (hV : V₀ ≫ smallerToLarger A p p = smallerToLarger A p p ≫ V₁)
    (hW : multiplication A p p ≫ W₀ = W₁ ≫ multiplication A p p)
    (hWF : W₁ ≫ SchemeFrobenius.absolute p (base A (p * p)) = squareMultiplication A p)
    (hFV : SchemeFrobenius.absolute p (base A (p * p)) ≫ V₁ = squareMultiplication A p) :
    V₀ = W₀ :=
  eq_of_two_level_frobenius_identities A p (Fact.out : p.Prime).ne_zero _
    V₁ W₁ V₀ W₀ hV hW hWF hFV

end SupersingularCurves.Geometry.TorsionLevels
