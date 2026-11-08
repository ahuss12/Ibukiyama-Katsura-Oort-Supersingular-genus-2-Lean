/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingProjection

/-!
# Actual finite and ambient Verschiebung agree

The canonical Cartier-dual Frobenius of the actual p-torsion agrees with
restriction of the independently constructed ambient Verschiebung. The proof
uses both actual p² and p torsion levels, not uniqueness on a killed-by-p
object. The scalar inverse Frobenius is retained over every algebraically
closed field of characteristic p.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.TorsionLevels.Presentation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GoodReductionJacobian SchemeFrobenius

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ} {A : AbelianVariety K g}
  (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Cartier-dual Verschiebung respects the actual projection A[p²]→A[p]. -/
theorem canonical_multiplication (H : Presentation A (p * p)) (H' : Presentation A p) :
    multiplication A p p ≫ H'.canonical p = H.canonical p ≫ multiplication A p p := by
  apply (cancel_epi H.specIso.hom).mp
  rw [← Category.assoc H.specIso.hom, ← multiplicationMap_spec,
    Category.assoc, canonical_spec,
    ← Category.assoc H.specIso.hom, canonical_spec, Category.assoc,
    ← multiplicationMap_spec]
  have he : (PerfectHopfVerschiebung.ringHom (K := K) p H.Coord).comp
      (multiplicationMap H H').toAlgHom.toRingHom =
      (multiplicationMap H H').toAlgHom.toRingHom.comp
        (PerfectHopfVerschiebung.ringHom (K := K) p H'.Coord) := by
    ext a
    exact (PerfectHopfVerschiebung.naturality p (multiplicationMap H H') a).symm
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, he]

/-- The canonical finite V satisfies VF=[p] on the whole actual p²-torsion. -/
theorem canonical_absolute_square (H : Presentation A (p * p)) :
    H.canonical p ≫ absolute p (base A (p * p)) = squareMultiplication A p := by
  apply (cancel_mono (inclusion A (p * p))).mp
  rw [Category.assoc, canonical_absolute_inclusion, squareMultiplication_inclusion]

/-- The actual ambient inverse-semilinear Verschiebung restricts to canonical
Cartier-dual Frobenius on actual p-torsion. No lifting or superspecial
classification assumption is used. -/
theorem ambientOnLevel_eq_canonical (H' : Presentation A p) :
    ambientOnLevel A p p = H'.canonical p := by
  let H := presentation A (p * p) (Nat.mul_ne_zero
    (Fact.out : p.Prime).ne_zero (Fact.out : p.Prime).ne_zero)
  exact ambientOnLevel_eq_of_canonical A p (H.canonical p) (H'.canonical p)
    (canonical_multiplication p H H') (canonical_absolute_square p H)

/-- A completely constructed presentation identifies ambient V with the
spectrum of canonical inverse-Frobenius semilinear Hopf Verschiebung. -/
theorem ambientOnLevel_eq_constructed :
    ambientOnLevel A p p =
      (presentation A p (Fact.out : p.Prime).ne_zero).canonical p :=
  ambientOnLevel_eq_canonical p _

end SupersingularCurves.Geometry.TorsionLevels.Presentation
