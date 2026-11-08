/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentSectionIso
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_isPullback_projMap_of_isBaseChange

/-!
# Actual Proj scalar extension from degreewise scalar extension

Degreewise scalar extension implies the irrelevant-ideal condition needed
for the actual map on Proj. Its geometric base-change square transports
through the proved section-ring model of the original scheme. This is a
generic comparison: it does not assume or construct a fixed graded ring.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentSectionProj
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
variable (R : Type u) [CommRing R] [Algebra S R]
    (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
variable (R' : Type u) [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
variable (ϑ : R →ₐ[S] R') (hdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)

/-- The actual homogeneous map underlying the scalar-extension homomorphism. -/
def gradedMap : 𝓡 →+*ᵍ 𝓡' :=
  { ϑ.toRingHom with map_mem := fun h => hdeg _ _ h }

/-- Restriction of the genuine map to one homogeneous component. -/
def pieceMap (n : ℕ) : 𝓡 n →ₗ[S] (𝓡' n).restrictScalars S :=
  ϑ.toLinearMap.restrict (p := 𝓡 n) (q := (𝓡' n).restrictScalars S) (hdeg n)

variable (hbc : ∀ n, IsBaseChange S' (pieceMap S' R 𝓡 R' 𝓡' ϑ hdeg n))

include hbc in
/-- Degreewise scalar extension forces the full irrelevant ideal into the
image ideal, so the actual Proj morphism is defined everywhere. -/
theorem irrelevant_le_map_of_piece_baseChange :
    HomogeneousIdeal.irrelevant 𝓡' ≤
      (HomogeneousIdeal.irrelevant 𝓡).map (gradedMap S' R 𝓡 R' 𝓡' ϑ hdeg) := by
  apply (HomogeneousIdeal.irrelevant_le 𝓡').mpr
  intro n hn x hx
  let I := ((HomogeneousIdeal.irrelevant 𝓡).map (gradedMap S' R 𝓡 R' 𝓡' ϑ hdeg)).toIdeal
  change x ∈ I
  exact (hbc n).inductionOn (⟨x, hx⟩ : 𝓡' n)
    (fun z => (z : R') ∈ I) I.zero_mem
    (fun y => Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem 𝓡 hn y.2))
    (fun a z hz => by
      change a • (z : R') ∈ I
      rw [Algebra.smul_def]
      exact I.mul_mem_left _ hz)
    (fun z w hz hw => I.add_mem hz hw)

/-- The actual Proj scheme commutes with scalar extension when each
homogeneous component does; no separate irrelevant-ideal hypothesis remains. -/
theorem isPullback_projMap_of_piece_baseChange :
    IsPullback
      (Proj.map (gradedMap S' R 𝓡 R' 𝓡' ϑ hdeg)
        (irrelevant_le_map_of_piece_baseChange S' R 𝓡 R' 𝓡' ϑ hdeg hbc))
      (Proj.toSpecZero 𝓡' ≫ Spec.map (CommRingCat.ofHom
        ((GradedRing.projZeroRingHom' 𝓡').comp (algebraMap S' R'))))
      (Proj.toSpecZero 𝓡 ≫ Spec.map (CommRingCat.ofHom
        ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap S R))))
      (Spec.map (CommRingCat.ofHom (algebraMap S S'))) :=
  GradedOAlgebra.isPullback_projMap_of_isBaseChange S' R 𝓡 R' 𝓡' ϑ hdeg hbc
    (irrelevant_le_map_of_piece_baseChange S' R 𝓡 R' 𝓡' ϑ hdeg hbc)

/-- A genuine section-ring isomorphism transports the Proj scalar-extension
square to the original scheme itself. -/
theorem isPullback_sectionModel_of_piece_baseChange
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S')) (L : X.Modules)
    (ι : ∀ n : ℕ, 𝓡' n → Γ(L.tensorPow n, ⊤)) (e : X ≅ Proj 𝓡')
    (he : GradedOAlgebra.IsCanonicalToProj f L R' 𝓡' ι e.hom) :
    IsPullback
      (e.hom ≫ Proj.map (gradedMap S' R 𝓡 R' 𝓡' ϑ hdeg)
        (irrelevant_le_map_of_piece_baseChange S' R 𝓡 R' 𝓡' ϑ hdeg hbc)) f
      (Proj.toSpecZero 𝓡 ≫ Spec.map (CommRingCat.ofHom
        ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap S R))))
      (Spec.map (CommRingCat.ofHom (algebraMap S S'))) := by
  have hs : IsPullback e.hom f
      (Proj.toSpecZero 𝓡' ≫ Spec.map (CommRingCat.ofHom
        ((GradedRing.projZeroRingHom' 𝓡').comp (algebraMap S' R'))))
      (𝟙 (Spec (CommRingCat.of S'))) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.assoc, Category.comp_id]
      using he.comp_toSpecZero⟩
  simpa only [Category.id_comp] using
    hs.paste_horiz (isPullback_projMap_of_piece_baseChange S' R 𝓡 R' 𝓡' ϑ hdeg hbc)

end SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentSectionProj
