/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingAmbientComparison

/-!
# Arbitrary finite torsion maps respect actual ambient Verschiebung

A bialgebra map of the constructed actual p-torsion coordinate algebras
produces an actual scheme map respecting ambient Verschiebung. The finite
map is not required to come from an abelian-variety morphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.TorsionLevels.Presentation
open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K] [IsAlgClosed K] {g h n m : ℕ}
  {A : AbelianVariety K g} {B : AbelianVariety K h}

/-- Spectrum of an arbitrary finite torsion Hopf morphism, on the actual kernels. -/
def schemeMap (H : Presentation A n) (H' : Presentation B m)
    (φ : H'.Coord →ₐc[K] H.Coord) : kernel A n ⟶ kernel B m :=
  H.specIso.inv ≫ Spec.map (CommRingCat.ofHom φ.toAlgHom.toRingHom) ≫ H'.specIso.hom

@[reassoc]
theorem schemeMap_spec (H : Presentation A n) (H' : Presentation B m)
    (φ : H'.Coord →ₐc[K] H.Coord) :
    H.specIso.hom ≫ schemeMap H H' φ =
      Spec.map (CommRingCat.ofHom φ.toAlgHom.toRingHom) ≫ H'.specIso.hom := by
  simp only [schemeMap, Iso.hom_inv_id_assoc]

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Naturalness of canonical V for every finite Hopf morphism, on actual schemes. -/
theorem canonical_naturality (H : Presentation A n) (H' : Presentation B m)
    (φ : H'.Coord →ₐc[K] H.Coord) :
    schemeMap H H' φ ≫ H'.canonical p = H.canonical p ≫ schemeMap H H' φ := by
  apply (cancel_epi H.specIso.hom).mp
  rw [← Category.assoc H.specIso.hom, schemeMap_spec,
    Category.assoc, canonical_spec,
    ← Category.assoc H.specIso.hom, canonical_spec, Category.assoc, schemeMap_spec]
  have he : (PerfectHopfVerschiebung.ringHom (K := K) p H.Coord).comp
      φ.toAlgHom.toRingHom =
      φ.toAlgHom.toRingHom.comp (PerfectHopfVerschiebung.ringHom (K := K) p H'.Coord) := by
    ext a
    exact (PerfectHopfVerschiebung.naturality p φ a).symm
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, he]

/-- Every finite p-torsion Hopf morphism commutes with the independently
constructed actual ambient Verschiebung, even without an ambient lift. -/
theorem ambient_naturality (H : Presentation A p) (H' : Presentation B p)
    (φ : H'.Coord →ₐc[K] H.Coord) :
    schemeMap H H' φ ≫ ambientOnLevel B p p =
      ambientOnLevel A p p ≫ schemeMap H H' φ := by
  rw [ambientOnLevel_eq_canonical p H, ambientOnLevel_eq_canonical p H']
  exact canonical_naturality p H H' φ

/-- The same statement uses the actually constructed presentations, with no
presentation input. Only the finite torsion morphism is supplied. -/
theorem constructed_ambient_naturality
    (φ : (presentation B p (Fact.out : p.Prime).ne_zero).Coord →ₐc[K]
      (presentation A p (Fact.out : p.Prime).ne_zero).Coord) :
    schemeMap (presentation A p (Fact.out : p.Prime).ne_zero)
      (presentation B p (Fact.out : p.Prime).ne_zero) φ ≫ ambientOnLevel B p p =
    ambientOnLevel A p p ≫
      schemeMap (presentation A p (Fact.out : p.Prime).ne_zero)
        (presentation B p (Fact.out : p.Prime).ne_zero) φ :=
  ambient_naturality p _ _ φ

end SupersingularCurves.Geometry.TorsionLevels.Presentation
