/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Mathlib

/-! # Saturated integral intersections of rational subspaces -/
set_option autoImplicit false
noncomputable section
universe u v w
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate.SymplecticLattice
open LinearMap
open scoped nonZeroDivisors

section Kernel
variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.IsTorsionFree R N]

/-- Over a PID, the kernel of a map from a finite module to a torsion-free
module is a direct summand. The complement is constructed by projectivity of
the actual finite torsion-free image. -/
theorem exists_complement_kernel (f : M →ₗ[R] N) :
    ∃ P : Submodule R M, IsCompl (LinearMap.ker f) P := by
  obtain ⟨g, hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective
    f.range_rangeRestrict
  have hg' (y : LinearMap.range f) : f (g y) = (y : N) :=
    congrArg Subtype.val (LinearMap.congr_fun hg y)
  let π : M →ₗ[R] LinearMap.ker f :=
    (LinearMap.id - g.comp f.rangeRestrict).codRestrict (LinearMap.ker f) (by
      intro x
      change f (x - g (f.rangeRestrict x)) = 0
      rw [map_sub, hg']
      exact sub_self _)
  refine ⟨LinearMap.ker π, LinearMap.isCompl_of_proj ?_⟩
  intro x
  apply Subtype.ext
  change (x : M) - g (f.rangeRestrict x) = x
  have hx : f.rangeRestrict x = 0 := Subtype.ext x.2
  rw [hx, map_zero, sub_zero]

end Kernel

section Intersection
variable {R : Type u} [CommRing R] [IsDomain R]
variable {Q : Type u} [Field Q] [Algebra R Q] [IsFractionRing R Q]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {V : Type w} [AddCommGroup V] [Module R V] [Module Q V]
variable [IsScalarTower R Q V]
variable (j : M →ₗ[R] V) (U : Submodule Q V)

/-- The actual integral intersection with a rational subspace. -/
def intersection : Submodule R M := (U.restrictScalars R).comap j

omit [IsDomain R] [IsFractionRing R Q] in
@[simp] theorem mem_intersection (x : M) : x ∈ intersection j U ↔ j x ∈ U := Iff.rfl

/-- The integral intersection is saturated for every nonzero base scalar. -/
theorem saturated (r : R) (hr : r ≠ 0) (x : M) :
    r • x ∈ intersection j U ↔ x ∈ intersection j U := by
  change j (r • x) ∈ U ↔ j x ∈ U
  rw [map_smul, ← algebraMap_smul Q]
  have hrQ : algebraMap R Q r ≠ 0 := by
    intro h
    apply hr
    apply IsFractionRing.injective R Q
    simpa using h
  exact U.smul_mem_iff hrQ

variable [IsLocalizedModule R⁰ j]

omit [IsDomain R] in
/-- Clearing denominators shows that the actual intersection spans the whole
prescribed rational subspace. -/
theorem localized_intersection : (intersection j U).localized' Q R⁰ j = U :=
  (Submodule.localized'gi Q R⁰ j).l_u_eq U

/-- The integral intersection has exactly the rational dimension. -/
theorem finrank_intersection : Module.finrank R (intersection j U) = Module.finrank Q U := by
  calc
    Module.finrank R (intersection j U) =
        Module.finrank R ((intersection j U).localized' Q R⁰ j) :=
      (IsLocalizedModule.finrank_eq R⁰ ((intersection j U).toLocalized' Q R⁰ j)
        le_rfl).symm
    _ = Module.finrank Q ((intersection j U).localized' Q R⁰ j) :=
      (IsFractionRing.finrank_right_eq (R := R) (S := Q)
        (N := (intersection j U).localized' Q R⁰ j)).symm
    _ = Module.finrank Q U := by rw [localized_intersection]

variable [IsPrincipalIdealRing R] [Module.Finite R M]

/-- A rational subspace intersects a finite integral module in a direct
summand over the PID. -/
theorem exists_complement_intersection :
    ∃ P : Submodule R M, IsCompl (intersection j U) P := by
  have : Module.IsTorsionFree R (V ⧸ U) :=
    Module.IsTorsionFree.trans Q
  let f : M →ₗ[R] V ⧸ U := (U.mkQ.restrictScalars R).comp j
  have hf : LinearMap.ker f = intersection j U := by
    ext x
    change U.mkQ (j x) = 0 ↔ j x ∈ U
    exact Submodule.Quotient.mk_eq_zero _
  rw [← hf]
  exact exists_complement_kernel f

end Intersection

end SupersingularCurves.Geometry.ScalarFrobeniusTate.SymplecticLattice
