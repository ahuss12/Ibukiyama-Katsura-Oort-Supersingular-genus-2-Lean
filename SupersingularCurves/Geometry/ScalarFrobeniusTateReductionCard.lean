/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateLatticeReduction
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Cardinality of reduction of a direct summand in an actual Tate module -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
variable (ℓ : ℕ) [Fact ℓ.Prime] {M : Type} [AddCommGroup M]

/-- The actual level projection, with its actual image as codomain. -/
def reducedProjection (n : ℕ) (U : Submodule ℤ_[ℓ] (TateModule ℓ M)) :
    U →+ reducedSubgroup ℓ n U where
  toFun x := ⟨TateModule.proj ℓ M n x, ⟨x, x.property, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

theorem reducedProjection_surjective (n : ℕ)
    (U : Submodule ℤ_[ℓ] (TateModule ℓ M)) :
    Function.Surjective (reducedProjection ℓ n U) := by
  rintro ⟨x, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

/-- In a split submodule the projection kernel consists of its own ℓ^n multiples. -/
theorem reducedProjection_eq_zero_iff (n : ℕ)
    (U : Submodule ℤ_[ℓ] (TateModule ℓ M))
    (r : TateModule ℓ M →ₗ[ℤ_[ℓ]] U) (hr : ∀ x : U, r x = x) (x : U) :
    reducedProjection ℓ n U x = 0 ↔ ∃ y : U, (ℓ : ℤ_[ℓ]) ^ n • y = x := by
  constructor
  · intro hx
    have hz : TateModule.proj ℓ M n x = 0 := congrArg Subtype.val hx
    refine ⟨r (TateModule.shiftOfProjEqZero n x hz), ?_⟩
    rw [← map_smul, TateModule.pow_smul_shiftOfProjEqZero, hr]
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    change (((ℓ : ℤ_[ℓ]) ^ n • (y : TateModule ℓ M) : TateModule ℓ M) : ℕ → M) n = 0
    rw [← Nat.cast_pow, TateModule.natCast_padicInt_smul_apply]
    exact TateModule.torsion (y : TateModule ℓ M) n

/-- Coordinate reduction of a finite free ℓ-adic lattice. -/
def basisReduction {V : Type} [AddCommGroup V] [Module ℤ_[ℓ] V]
    {r : ℕ} (b : Module.Basis (Fin r) ℤ_[ℓ] V) (n : ℕ) :
    V →+ (Fin r → ZMod (ℓ ^ n)) where
  toFun x i := PadicInt.toZModPow n (b.equivFun x i)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

theorem basisReduction_surjective {V : Type} [AddCommGroup V] [Module ℤ_[ℓ] V]
    {r : ℕ} (b : Module.Basis (Fin r) ℤ_[ℓ] V) (n : ℕ) :
    Function.Surjective (basisReduction ℓ b n) := by
  intro x
  have hsurj := ZMod.ringHom_surjective (PadicInt.toZModPow n : ℤ_[ℓ] →+* ZMod (ℓ ^ n))
  choose y hy using fun i => hsurj (x i)
  refine ⟨b.equivFun.symm y, ?_⟩
  ext i
  change PadicInt.toZModPow n (b.equivFun (b.equivFun.symm y) i) = x i
  rw [b.equivFun.apply_symm_apply]
  exact hy i

theorem basisReduction_eq_zero_iff {V : Type} [AddCommGroup V] [Module ℤ_[ℓ] V]
    {r : ℕ} (b : Module.Basis (Fin r) ℤ_[ℓ] V) (n : ℕ) (x : V) :
    basisReduction ℓ b n x = 0 ↔ ∃ y : V, (ℓ : ℤ_[ℓ]) ^ n • y = x := by
  constructor
  · intro hx
    have hc : ∀ i, ∃ c : ℤ_[ℓ], b.equivFun x i = (ℓ : ℤ_[ℓ]) ^ n * c := by
      intro i
      have hi : b.equivFun x i ∈ RingHom.ker (PadicInt.toZModPow n) :=
        congrFun hx i
      rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hi
      exact hi
    choose c hc using hc
    refine ⟨b.equivFun.symm c, b.equivFun.injective ?_⟩
    ext i
    simp only [map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]
    exact (hc i).symm
  · rintro ⟨y, rfl⟩
    ext i
    change PadicInt.toZModPow n (b.equivFun ((ℓ : ℤ_[ℓ]) ^ n • y) i) = 0
    apply (show b.equivFun ((ℓ : ℤ_[ℓ]) ^ n • y) i ∈
      RingHom.ker (PadicInt.toZModPow n) from ?_)
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    exact ⟨b.equivFun y i, by simp only [map_smul, Pi.smul_apply, smul_eq_mul]⟩

/-- A rank-r split submodule has exactly ℓ^(r*n) actual level-n points. -/
theorem natCard_reducedSubgroup_of_basis_retraction (n : ℕ)
    (U : Submodule ℤ_[ℓ] (TateModule ℓ M)) {r : ℕ}
    (b : Module.Basis (Fin r) ℤ_[ℓ] U)
    (q : TateModule ℓ M →ₗ[ℤ_[ℓ]] U) (hq : ∀ x : U, q x = x) :
    Nat.card (reducedSubgroup ℓ n U) = ℓ ^ (r * n) := by
  have hk : (reducedProjection ℓ n U).ker = (basisReduction ℓ b n).ker := by
    ext x
    exact (reducedProjection_eq_zero_iff ℓ n U q hq x).trans
      (basisReduction_eq_zero_iff ℓ b n x).symm
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective
    (reducedProjection ℓ n U) (reducedProjection_surjective ℓ n U)).toEquiv,
    hk, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective
      (basisReduction ℓ b n) (basisReduction_surjective ℓ b n)).toEquiv]
  simp [Nat.card_fun, Nat.card_zmod, ← pow_mul, Nat.mul_comm]

theorem natCard_reducedSubgroup_of_isCompl (n : ℕ)
    (U P : Submodule ℤ_[ℓ] (TateModule ℓ M)) (hUP : IsCompl U P)
    [Module.Free ℤ_[ℓ] U] [Module.Finite ℤ_[ℓ] U] :
    Nat.card (reducedSubgroup ℓ n U) = ℓ ^ (Module.finrank ℤ_[ℓ] U * n) := by
  exact natCard_reducedSubgroup_of_basis_retraction ℓ n U (Module.finBasis ℤ_[ℓ] U)
    (U.projectionOnto P hUP) (Submodule.projectionOnto_apply_left hUP)

end SupersingularCurves.Geometry.ScalarFrobeniusTate
