/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianVariety

/-!
# Faithful base change on actual abelian-variety points

The point map is induced by pullback of schemes. Its injectivity follows from
faithfully flat descent along a field extension. The group laws are the
scheme-group laws transported by the monoidal pullback functor.
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

/-- Extension of scalars on the actual group of points. -/
def pointsBaseChange (A : AbelianVariety K g) (L : Type u) [Field L] [Algebra K L] :
    A.Points →* (A.baseChange L).Points where
  toFun P := (preservesTerminalIso
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))).inv ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map P
  map_one' := by
    simp only [Functor.map_one, MonObj.comp_one]
  map_mul' P Q := by
    rw [Functor.map_mul, MonObj.comp_mul]

theorem pointsBaseChange_injective (A : AbelianVariety K g)
    (L : Type u) [Field L] [Algebra K L] : Function.Injective (A.pointsBaseChange L) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have hff : (algebraMap K L).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have hf : Flat f ∧ Surjective f :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap K L))).mpr hff
  let : Flat f := hf.1
  let : Surjective f := hf.2
  have : (Over.pullback f).Faithful := inferInstance
  intro P Q h
  apply (Over.pullback f).map_injective
  exact (cancel_epi (preservesTerminalIso (Over.pullback f)).inv).mp h

end AbelianVariety
end SupersingularCurves.Geometry
