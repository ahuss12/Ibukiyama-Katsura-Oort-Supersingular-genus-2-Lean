/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PointBaseChange
import SupersingularCurves.Geometry.Superspecial

/-!
# Base change on points along a field isomorphism

When the structural field homomorphism is bijective, the actual pullback map
on abelian-variety points is a group isomorphism. Fullness of the pullback
functor supplies surjectivity; injectivity is the existing faithfully flat
descent theorem. Supersingularity of elliptic curves, defined by their actual
geometric p-torsion, is consequently invariant under this base change.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AbelianVariety
variable {K : Type u} [Field K] {g : ℕ}

/-- Pullback along an isomorphism of fields is surjective on actual points. -/
theorem pointsBaseChange_surjective (A : AbelianVariety K g)
    (L : Type u) [Field L] [Algebra K L]
    (h : Function.Bijective (algebraMap K L)) :
    Function.Surjective (A.pointsBaseChange L) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let : IsIso (CommRingCat.ofHom (algebraMap K L)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr h
  have : IsIso f := by dsimp [f]; infer_instance
  have : (Over.pullback f).IsEquivalence :=
    (Over.mapPullbackAdj f).isEquivalence_right_of_isEquivalence_left
  intro P
  let e := preservesTerminalIso (Over.pullback f)
  refine ⟨(Over.pullback f).preimage (e.hom ≫ P), ?_⟩
  change e.inv ≫ (Over.pullback f).map ((Over.pullback f).preimage (e.hom ≫ P)) = P
  rw [Functor.map_preimage, Iso.inv_hom_id_assoc]

/-- Base change along a field isomorphism is bijective on actual points. -/
theorem pointsBaseChange_bijective (A : AbelianVariety K g)
    (L : Type u) [Field L] [Algebra K L]
    (h : Function.Bijective (algebraMap K L)) :
    Function.Bijective (A.pointsBaseChange L) :=
  ⟨A.pointsBaseChange_injective L, A.pointsBaseChange_surjective L h⟩

/-- The group isomorphism is the existing scheme-theoretic pullback map. -/
def pointsBaseChangeMulEquiv (A : AbelianVariety K g)
    (L : Type u) [Field L] [Algebra K L]
    (h : Function.Bijective (algebraMap K L)) :
    A.Points ≃* (A.baseChange L).Points :=
  MulEquiv.ofBijective (A.pointsBaseChange L) (A.pointsBaseChange_bijective L h)

/-- Trivial geometric p-torsion of an elliptic curve is invariant under
base change along a bijective structural field homomorphism. -/
theorem isSupersingularElliptic_baseChange_iff [IsAlgClosed K]
    (E : AbelianVariety K 1) (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L]
    (h : Function.Bijective (algebraMap K L))
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p] :
    (E.baseChange L).IsSupersingularElliptic p ↔ E.IsSupersingularElliptic p := by
  let q := E.pointsBaseChangeMulEquiv L h
  constructor
  · intro hE P hP
    apply q.injective
    simpa using hE (q P) (by rw [← map_pow, hP, map_one])
  · intro hE P hP
    apply q.symm.injective
    simpa using hE (q.symm P) (by rw [← map_pow, hP, map_one])

end AbelianVariety
end SupersingularCurves.Geometry
