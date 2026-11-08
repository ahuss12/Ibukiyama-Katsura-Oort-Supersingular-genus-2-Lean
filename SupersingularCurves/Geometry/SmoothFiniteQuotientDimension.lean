/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth
import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isFinite_of_surjective
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le

/-!
# Dimension of an actual smooth finite quotient

A finite surjective morphism preserves topological dimension. Consequently,
when its source is smooth of relative dimension `g` over a field and its
target is a smooth group scheme, the target has the same relative dimension.
The quotient morphism itself is not required to be smooth.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FiniteQuotientGeometry
open CategoryTheory AlgebraicGeometry GoodReductionJacobian

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
variable (c : X ⟶ Spec (CommRingCat.of K)) (d : Y ⟶ Spec (CommRingCat.of K))
variable (q : X ⟶ Y) (hq : q ≫ d = c)

include hq in
/-- Equality of actual topological dimensions under a finite surjective morphism. -/
theorem topologicalKrullDim_eq_of_finite_surjective [IsFinite q] [Surjective q] :
    topologicalKrullDim Y = topologicalKrullDim X := by
  let s : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have h := topologicalKrullDim_preimage_eq_of_isFinite_of_surjective c d q hq s
  have hd : d.base ⁻¹' {s} = Set.univ :=
    Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
  have hc : c.base ⁻¹' {s} = Set.univ :=
    Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
  rw [hd, hc,
    IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph,
    IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph] at h
  exact h

include hq in
/-- A smooth group scheme receiving an actual finite surjection from a smooth
scheme has the same relative dimension as that source. -/
theorem smoothOfRelativeDimension_of_finite_surjective
    (g : ℕ) [SmoothOfRelativeDimension g c] [IsFinite q] [Surjective q] [Smooth d]
    (L : RelativeGroupLaw K d) : SmoothOfRelativeDimension g d := by
  let s : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  let y : Y := ((L.one (𝟙 _)).1) s
  let : Nonempty Y := ⟨y⟩
  obtain ⟨x, _⟩ := q.surjective y
  let : Nonempty X := ⟨x⟩
  obtain ⟨n, hn⟩ := L.exists_smoothOfRelativeDimension_of_smooth
  let : SmoothOfRelativeDimension n d := hn
  have hX : topologicalKrullDim X = (g : WithBot ℕ∞) :=
    le_antisymm (SmoothOfRelativeDimension.topologicalKrullDim_le c g)
      (SmoothOfRelativeDimension.le_topologicalKrullDim c g)
  have hY : topologicalKrullDim Y = (n : WithBot ℕ∞) :=
    le_antisymm (SmoothOfRelativeDimension.topologicalKrullDim_le d n)
      (SmoothOfRelativeDimension.le_topologicalKrullDim d n)
  have hng : (n : WithBot ℕ∞) = (g : WithBot ℕ∞) :=
    hY.symm.trans ((topologicalKrullDim_eq_of_finite_surjective c d q hq).trans hX)
  have hn' : n = g := by exact_mod_cast hng
  simpa only [hn'] using hn

end SupersingularCurves.Geometry.FiniteQuotientGeometry
