/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Definitions.Def_EllipticCurve_TateModule

/-!
# Exact integral image for complementary Tate maps

If two maps compose in both directions to multiplication by ℓ^n, then the
image of one integral Tate map is exactly the inverse image of the other's
level-n point kernel. This uses the actual compatible-torsion inverse limit:
its division map is obtained by shifting a sequence whose nth component
vanishes. No quotient-image assertion is an input.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
variable (ℓ : ℕ) [Fact ℓ.Prime]
variable {M N : Type} [AddCommGroup M] [AddCommGroup N]

/-- A Tate module has no ℓ-power torsion, directly from compatibility. -/
theorem pow_smul_injective (n : ℕ) :
    Function.Injective (fun x : TateModule ℓ M => (ℓ : ℤ_[ℓ]) ^ n • x) := by
  intro x y h
  apply Subtype.ext
  funext m
  have hz := congrArg (fun z : TateModule ℓ M => (z : ℕ → M) (m + n)) h
  rw [← Nat.cast_pow, TateModule.natCast_padicInt_smul_apply,
    TateModule.natCast_padicInt_smul_apply, TateModule.compat_pow, TateModule.compat_pow] at hz
  exact hz

/-- Exact image of a Tate map admitting a complementary ℓ^n map. -/
theorem mem_range_iff_level_kernel
    (f : TateModule ℓ N →ₗ[ℤ_[ℓ]] TateModule ℓ M)
    (q : TateModule ℓ M →ₗ[ℤ_[ℓ]] TateModule ℓ N)
    (n : ℕ)
    (h₁ : ∀ x, q (f x) = (ℓ : ℤ_[ℓ]) ^ n • x)
    (h₂ : ∀ x, f (q x) = (ℓ : ℤ_[ℓ]) ^ n • x)
    (q₀ : M →+ N)
    (hproj : ∀ x, TateModule.proj ℓ N n (q x) = q₀ (TateModule.proj ℓ M n x))
    (x : TateModule ℓ M) :
    x ∈ LinearMap.range f ↔ q₀ (TateModule.proj ℓ M n x) = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← hproj, h₁]
    change (((ℓ : ℤ_[ℓ]) ^ n • y : TateModule ℓ N) : ℕ → N) n = 0
    rw [← Nat.cast_pow, TateModule.natCast_padicInt_smul_apply]
    exact TateModule.torsion y n
  · intro hx
    have hz : TateModule.proj ℓ N n (q x) = 0 := (hproj x).trans hx
    refine ⟨TateModule.shiftOfProjEqZero n (q x) hz, ?_⟩
    apply pow_smul_injective ℓ n
    change (ℓ : ℤ_[ℓ]) ^ n • f (TateModule.shiftOfProjEqZero n (q x) hz) =
      (ℓ : ℤ_[ℓ]) ^ n • x
    rw [← map_smul, TateModule.pow_smul_shiftOfProjEqZero, h₂]

end SupersingularCurves.Geometry.ScalarFrobeniusTate
