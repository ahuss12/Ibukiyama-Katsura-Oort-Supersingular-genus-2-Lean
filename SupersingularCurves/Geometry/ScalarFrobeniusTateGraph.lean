/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Mathlib

/-!
# Extracting a nonzero cross morphism from Tate's graph argument

If a nonzero operator in the scalar span of actual endomorphisms has image
inside the graph of an isomorphism between two factors, some actual
endomorphism has a nonzero cross component. This avoids the full
bicommutant theorem in the surface-specific product-isogeny argument.

The input family is an arbitrary family of linearized actual morphisms;
constructing the geometric family and its limiting graph operator is
separate from this elementary extraction lemma.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
variable {k X Y : Type*} [Field k]
  [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]

/-- Operators preserving the two summands, as a genuine linear subspace. -/
def blockDiagonal : Submodule k (Module.End k (X × Y)) where
  carrier := {u | (∀ x : X, (u (x, 0)).2 = 0) ∧ (∀ y : Y, (u (0, y)).1 = 0)}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    rintro a b ⟨ha₁, ha₂⟩ ⟨hb₁, hb₂⟩
    constructor
    · intro x
      change (a (x, 0)).2 + (b (x, 0)).2 = 0
      rw [ha₁, hb₁, add_zero]
    · intro y
      change (a (0, y)).1 + (b (0, y)).1 = 0
      rw [ha₂, hb₂, add_zero]
  smul_mem' := by
    rintro c a ⟨ha₁, ha₂⟩
    constructor
    · intro x
      change c • (a (x, 0)).2 = 0
      rw [ha₁, smul_zero]
    · intro y
      change c • (a (0, y)).1 = 0
      rw [ha₂, smul_zero]

/-- A block diagonal operator whose image lies in an isomorphism graph
must vanish. -/
theorem eq_zero_of_blockDiagonal_of_range_in_graph
    (e : X ≃ₗ[k] Y) (u : Module.End k (X × Y))
    (hu : u ∈ blockDiagonal (k := k) (X := X) (Y := Y))
    (hgraph : ∀ z : X × Y, (u z).2 = e ((u z).1)) : u = 0 := by
  have h₁ : ∀ x : X, u (x, 0) = 0 := by
    intro x
    apply Prod.ext
    · apply e.injective
      change e ((u (x, 0)).1) = e 0
      rw [map_zero, ← hgraph, hu.1]
    · exact hu.1 x
  have h₂ : ∀ y : Y, u (0, y) = 0 := by
    intro y
    apply Prod.ext
    · exact hu.2 y
    · change (u (0, y)).2 = 0
      rw [hgraph, hu.2, map_zero]
  apply LinearMap.ext
  intro z
  have hz : z = (z.1, 0) + (0, z.2) := by ext <;> simp
  rw [hz, map_add, h₁, h₂, add_zero]
  rfl

/-- A graph operator in the scalar span forces an actual generator with
a nonzero component between the two factors. -/
theorem exists_cross_component_of_mem_span_of_range_in_graph
    {I : Type*} (ρ : I → Module.End k (X × Y))
    (e : X ≃ₗ[k] Y) (u : Module.End k (X × Y))
    (hu : u ∈ Submodule.span k (Set.range ρ)) (hne : u ≠ 0)
    (hgraph : ∀ z : X × Y, (u z).2 = e ((u z).1)) :
    ∃ i : I, (∃ x : X, (ρ i (x, 0)).2 ≠ 0) ∨ (∃ y : Y, (ρ i (0, y)).1 ≠ 0) := by
  classical
  by_contra h
  push Not at h
  have hρ : Set.range ρ ⊆ blockDiagonal (k := k) (X := X) (Y := Y) := by
    rintro _ ⟨i, rfl⟩
    exact h i
  have hspan : Submodule.span k (Set.range ρ) ≤ blockDiagonal := Submodule.span_le.mpr hρ
  exact hne (eq_zero_of_blockDiagonal_of_range_in_graph e u (hspan hu) hgraph)

end SupersingularCurves.Geometry.ScalarFrobeniusTate
