/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateLatticeImage

/-! # Reduction of an integral Tate submodule at finite torsion level -/
set_option autoImplicit false
noncomputable section
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open IsLocalRing
variable (ℓ : ℕ) [Fact ℓ.Prime] {M : Type} [AddCommGroup M]

/-- The actual finite-level image of an integral Tate submodule. -/
def reducedSubgroup (n : ℕ) (U : Submodule ℤ_[ℓ] (TateModule ℓ M)) : AddSubgroup M :=
  U.toAddSubgroup.map (TateModule.proj ℓ M n)

theorem reducedSubgroup_killed (n : ℕ) (U : Submodule ℤ_[ℓ] (TateModule ℓ M)) :
    ∀ x ∈ reducedSubgroup ℓ n U, (ℓ ^ n) • x = 0 := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := hx
  simpa only [natCast_zsmul] using TateModule.torsionBy_proj n y

/-- Its inverse image is exactly U plus the nth power of the maximal ideal.
This proves the desired Tate lattice formula before any geometric construction. -/
theorem proj_mem_reducedSubgroup_iff (n : ℕ) (U : Submodule ℤ_[ℓ] (TateModule ℓ M))
    (x : TateModule ℓ M) :
    TateModule.proj ℓ M n x ∈ reducedSubgroup ℓ n U ↔
      x ∈ U ⊔ (maximalIdeal ℤ_[ℓ] ^ n) • (⊤ : Submodule ℤ_[ℓ] (TateModule ℓ M)) := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    apply Submodule.mem_sup.mpr
    refine ⟨y, hy, x - y, (TateModule.proj_eq_zero_iff n _).mp ?_, ?_⟩
    · rw [map_sub, hxy, sub_self]
    · exact add_sub_cancel _ _
  · intro hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨y, hy, ?_⟩
    rw [map_add, (TateModule.proj_eq_zero_iff n z).mpr hz, add_zero]

end SupersingularCurves.Geometry.ScalarFrobeniusTate
