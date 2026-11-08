/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateQuotientDegree
import SupersingularCurves.Geometry.VerschiebungPrimeToCharacteristicIsogeny

/-! # Degree, divisibility and zero dV for actual quotient families -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory AlgebraicGeometry GoodReductionJacobian AbelianTate
section Linear
variable (ℓ : ℕ) [Fact ℓ.Prime]
  {T : Type} [AddCommGroup T] [Module ℤ_[ℓ] T]

/-- A bilinear form vanishing on U is divisible by ell^n on U + ell^n T. -/
theorem pairing_dvd_of_mem_isotropic_lattice
    (e : LinearMap.BilinForm ℤ_[ℓ] T) (U : Submodule ℤ_[ℓ] T)
    (hU : ∀ x ∈ U, ∀ y ∈ U, e x y = 0) (n : ℕ)
    (x y : T)
    (hx : x ∈ U ⊔ (IsLocalRing.maximalIdeal ℤ_[ℓ] ^ n) • (⊤ : Submodule ℤ_[ℓ] T))
    (hy : y ∈ U ⊔ (IsLocalRing.maximalIdeal ℤ_[ℓ] ^ n) • (⊤ : Submodule ℤ_[ℓ] T)) :
    (ℓ : ℤ_[ℓ]) ^ n ∣ e x y := by
  obtain ⟨u, hu, a, ha, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨v, hv, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul] at ha hb
  obtain ⟨a, _, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp ha
  obtain ⟨b, _, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hb
  refine ⟨e u b + e a v + (ℓ : ℤ_[ℓ]) ^ n * e a b, ?_⟩
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hU u hu v hv]
  ring
end Linear

variable {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}
  (ℓ : ℕ) [Fact ℓ.Prime]

local instance (A : AbelianVariety K g) : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth g A.group.X.hom

/-- Divisibility holds on the actual Tate image of every constructed quotient. -/
theorem PrescribedLatticeQuotients.pairing_dvd
    {A : AbelianVariety K g} {U : Submodule ℤ_[ℓ] (Integral ℓ A)}
    (F : PrescribedLatticeQuotients ℓ A U)
    (e : LinearMap.BilinForm ℤ_[ℓ] (Integral ℓ A))
    (hU : ∀ x ∈ U, ∀ y ∈ U, e x y = 0) (n : ℕ)
    (x y : Integral ℓ (F.quotient n).variety) :
    (ℓ : ℤ_[ℓ]) ^ n ∣
      e (integralMap ℓ ((F.quotient n).multiplicationFactor (ℓ ^ n) (F.killed n)) x)
        (integralMap ℓ ((F.quotient n).multiplicationFactor (ℓ ^ n) (F.killed n)) y) := by
  apply pairing_dvd_of_mem_isotropic_lattice ℓ e U hU n
  · rw [← F.image n]
    exact ⟨x, rfl⟩
  · rw [← F.image n]
    exact ⟨y, rfl⟩

/-- The degree-controlled quotient family consists of genuine zero-dV varieties.
The vanishing is derived from the source via the actual multiplication factors. -/
theorem exists_prescribedLatticeQuotients_with_degree_and_zeroDV
    (A : AbelianVariety K g) (hℓ : (ℓ : K) ≠ 0)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hV : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0)
    (U P : Submodule ℤ_[ℓ] (Integral ℓ A)) (hUP : IsCompl U P)
    [Module.Free ℤ_[ℓ] U] [Module.Finite ℤ_[ℓ] U]
    (hU : Module.finrank ℤ_[ℓ] U = g) :
    ∃ F : PrescribedLatticeQuotients ℓ A U,
      (∀ n x, (underlyingScheme.map
        ((F.quotient n).multiplicationFactor (ℓ ^ n) (F.killed n))).finrank x = (ℓ ^ n) ^ g) ∧
      ∀ n, GroupScheme.verschiebungCotangent p (F.quotient n).variety.group
        (F.quotient n).variety.groupScheme_law_commutative = 0 := by
  obtain ⟨F, hdegree⟩ := exists_prescribedLatticeQuotients_with_degree A ℓ U P hUP hU
  refine ⟨F, hdegree, ?_⟩
  intro n
  exact (F.quotient n).verschiebungCotangent_zero p (ℓ ^ n)
    (by simpa only [Nat.cast_pow] using pow_ne_zero n hℓ) (F.killed n) hV

end SupersingularCurves.Geometry.ScalarFrobeniusTate
