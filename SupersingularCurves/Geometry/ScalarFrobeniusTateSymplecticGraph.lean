/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateSymplectic
import SupersingularCurves.Geometry.ScalarFrobeniusTateSymplecticLattice

/-! # The saturated integral graph of a rational anti-isometry -/
set_option autoImplicit false
noncomputable section
universe u v
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate.SymplecticLattice
open LinearMap
open scoped nonZeroDivisors TensorProduct

section Graph
variable {Q : Type u} [Field Q]
variable {V W : Type v} [AddCommGroup V] [Module Q V] [AddCommGroup W] [Module Q W]

/-- The graph retains precisely the source dimension. -/
def graphEquiv (e : V ≃ₗ[Q] W) : V ≃ₗ[Q] e.toLinearMap.graph :=
  LinearEquiv.ofBijective
    ((LinearMap.id.prod e.toLinearMap).codRestrict e.toLinearMap.graph (fun _ => rfl))
    ⟨fun _ _ h => congrArg (fun z : e.toLinearMap.graph => z.1.1) h,
      fun z => ⟨z.1.1, Subtype.ext (Prod.ext rfl z.2.symm)⟩⟩

theorem finrank_graph (e : V ≃ₗ[Q] W) :
    Module.finrank Q e.toLinearMap.graph = Module.finrank Q V :=
  (graphEquiv e).finrank_eq.symm

end Graph

section IntegralGraph
variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {Q : Type u} [Field Q] [Algebra R Q] [IsFractionRing R Q]
variable {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The canonical rationalization of an integral product. -/
def productRationalization : (M × N) →ₗ[R] (Q ⊗[R] M) × (Q ⊗[R] N) :=
  (TensorProduct.mk R Q M 1).prodMap (TensorProduct.mk R Q N 1)

instance productRationalization_isLocalizedModule :
    IsLocalizedModule R⁰ (productRationalization (R := R) (Q := Q) (M := M) (N := N)) := by
  have h := IsLocalizedModule.of_linearEquiv R⁰
    (TensorProduct.mk R Q (M × N) 1)
    ((TensorProduct.prodRight R Q Q M N).restrictScalars R)
  exact h

/-- Intersect the actual integral product with the graph in its scalar extension. -/
def integralGraph (e : (Q ⊗[R] M) ≃ₗ[Q] (Q ⊗[R] N)) : Submodule R (M × N) :=
  intersection (productRationalization (R := R) (Q := Q)) e.toLinearMap.graph

@[simp] theorem mem_integralGraph (e : (Q ⊗[R] M) ≃ₗ[Q] (Q ⊗[R] N)) (x : M × N) :
    x ∈ integralGraph e ↔ (1 : Q) ⊗ₜ[R] x.2 = e ((1 : Q) ⊗ₜ[R] x.1) := Iff.rfl

theorem integralGraph_saturated (e : (Q ⊗[R] M) ≃ₗ[Q] (Q ⊗[R] N))
    (r : R) (hr : r ≠ 0) (x : M × N) :
    r • x ∈ integralGraph e ↔ x ∈ integralGraph e :=
  saturated _ _ r hr x

theorem integralGraph_spans (e : (Q ⊗[R] M) ≃ₗ[Q] (Q ⊗[R] N)) :
    (integralGraph e).localized' Q R⁰ productRationalization = e.toLinearMap.graph :=
  localized_intersection _ _

theorem finrank_integralGraph (e : (Q ⊗[R] M) ≃ₗ[Q] (Q ⊗[R] N)) :
    Module.finrank R (integralGraph e) = Module.finrank Q (Q ⊗[R] M) := by
  rw [integralGraph, finrank_intersection, finrank_graph]

variable [Module.Finite R M] [Module.Finite R N]

theorem exists_complement_integralGraph (e : (Q ⊗[R] M) ≃ₗ[Q] (Q ⊗[R] N)) :
    ∃ P : Submodule R (M × N), IsCompl (integralGraph e) P :=
  exists_complement_intersection _ _

/-- Rational anti-isotropy gives exact vanishing of the original integral
product pairing on the actual intersection. -/
theorem integralGraph_isotropic (b : LinearMap.BilinForm R M) (c : LinearMap.BilinForm R N)
    (e : (Q ⊗[R] M) ≃ₗ[Q] (Q ⊗[R] N))
    (he : ∀ x y, (c.baseChange Q) (e x) (e y) = -(b.baseChange Q) x y)
    (x y : M × N) (hx : x ∈ integralGraph e) (hy : y ∈ integralGraph e) :
    b x.1 y.1 + c x.2 y.2 = 0 := by
  have H := he ((1 : Q) ⊗ₜ[R] x.1) ((1 : Q) ⊗ₜ[R] y.1)
  rw [← (mem_integralGraph e x).mp hx, ← (mem_integralGraph e y).mp hy] at H
  simp only [LinearMap.BilinForm.baseChange_tmul, one_mul, Algebra.smul_def, mul_one] at H
  apply IsFractionRing.injective R Q
  rw [map_add, map_zero, H, add_neg_cancel]

/-- Construct a rank-four saturated direct summand isotropic for the actual
integral product form, from genuine nondegenerate alternating rationalizations. -/
theorem exists_isotropic_integralGraph_four
    (b : LinearMap.BilinForm R M) (c : LinearMap.BilinForm R N)
    (hbalt : (b.baseChange Q).IsAlt) (hcalt : (c.baseChange Q).IsAlt)
    (hb : (b.baseChange Q).Nondegenerate) (hc : (c.baseChange Q).Nondegenerate)
    (hM : Module.finrank Q (Q ⊗[R] M) = 4)
    (hN : Module.finrank Q (Q ⊗[R] N) = 4) :
    ∃ e : (Q ⊗[R] M) ≃ₗ[Q] (Q ⊗[R] N),
      (∀ x y, (c.baseChange Q) (e x) (e y) = -(b.baseChange Q) x y) ∧
      Module.finrank R (integralGraph e) = 4 ∧
      (∃ P : Submodule R (M × N), IsCompl (integralGraph e) P) ∧
      ∀ x ∈ integralGraph e, ∀ y ∈ integralGraph e, b x.1 y.1 + c x.2 y.2 = 0 := by
  obtain ⟨e, he⟩ := Symplectic.exists_antiIsometry_four (b.baseChange Q) (c.baseChange Q)
    hbalt hcalt hb hc hM hN
  exact ⟨e, he, (finrank_integralGraph e).trans hM,
    exists_complement_integralGraph e, fun x hx y hy => integralGraph_isotropic b c e he x y hx hy⟩

end IntegralGraph
end SupersingularCurves.Geometry.ScalarFrobeniusTate.SymplecticLattice
