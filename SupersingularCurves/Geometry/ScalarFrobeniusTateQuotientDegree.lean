/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateFiniteModels
import SupersingularCurves.Geometry.ScalarFrobeniusTateReductionCard

/-!
# Degree of actual half-rank Tate quotients

For a rank-g direct summand in the rank-2g Tate module, the quotient and its
residual multiplication factor both have degree ell^(g*n). The latter is the
factor which pulls back the fixed polarization in the boundedness argument.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory AlgebraicGeometry GoodReductionJacobian AbelianTate
variable {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}

/-- Equal half-degree of the two actual factors of multiplication. -/
theorem Quotient.multiplicationFactor_finrank_of_half_rank
    {A : AbelianVariety K g} {H : FiniteSubgroup A} (D : Quotient A H)
    (m : ℕ) (hm : m ≠ 0)
    (hk : H.inclusion ≫ (GroupScheme.law A.group).schemeNsmul m =
      (H.inclusion ≫ A.group.X.hom) ≫ ((GroupScheme.law A.group).one (𝟙 _)).1)
    (hrank : (H.inclusion ≫ A.group.X.hom).finrank (IsLocalRing.closedPoint K) = m ^ g)
    (x : A.group.X.left) :
    (underlyingScheme.map (D.multiplicationFactor m hk)).finrank x = m ^ g := by
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hm) g)
  calc
    m ^ g * (underlyingScheme.map (D.multiplicationFactor m hk)).finrank x = m ^ (2 * g) := by
      rw [← hrank]
      exact D.subgroup_rank_mul_multiplicationFactor_finrank m hk hm x
    _ = m ^ g * m ^ g := by rw [two_mul, pow_add]

/-- The prescribed-lattice quotient can be chosen with its exact finite-flat degree. -/
theorem exists_quotient_with_prescribed_lattice_and_degree
    (A : AbelianVariety K g) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    (U P : Submodule ℤ_[ℓ] (Integral ℓ A)) (hUP : IsCompl U P)
    [Module.Free ℤ_[ℓ] U] [Module.Finite ℤ_[ℓ] U]
    (hU : Module.finrank ℤ_[ℓ] U = g) :
    ∃ H : FiniteSubgroup A, ∃ D : Quotient A H,
      ∃ hk : H.inclusion ≫ (GroupScheme.law A.group).schemeNsmul (ℓ ^ n) =
        (H.inclusion ≫ A.group.X.hom) ≫ ((GroupScheme.law A.group).one (𝟙 _)).1,
      IsIsogeny (D.multiplicationFactor (ℓ ^ n) hk) ∧
      LinearMap.range (integralMap ℓ (D.multiplicationFactor (ℓ ^ n) hk)) =
        U ⊔ (IsLocalRing.maximalIdeal ℤ_[ℓ] ^ n) •
          (⊤ : Submodule ℤ_[ℓ] (Integral ℓ A)) ∧
      ∀ x, (underlyingScheme.map (D.multiplicationFactor (ℓ ^ n) hk)).finrank x =
        (ℓ ^ n) ^ g := by
  obtain ⟨H, D, hk, hrank, hisog, himage⟩ := exists_quotient_with_prescribed_lattice A ℓ n U
  refine ⟨H, D, hk, hisog, himage, ?_⟩
  have hd : (H.inclusion ≫ A.group.X.hom).finrank (IsLocalRing.closedPoint K) =
      (ℓ ^ n) ^ g := by
    rw [hrank, natCard_reducedSubgroup_of_isCompl ℓ n U P hUP, hU, ← pow_mul, Nat.mul_comm g n]
  exact D.multiplicationFactor_finrank_of_half_rank (ℓ ^ n)
    (pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero) hk hd

/-- A whole genuine quotient family, retaining the uniform degree formula
needed by the polarization-root numerical argument. -/
theorem exists_prescribedLatticeQuotients_with_degree
    (A : AbelianVariety K g) (ℓ : ℕ) [Fact ℓ.Prime]
    (U P : Submodule ℤ_[ℓ] (Integral ℓ A)) (hUP : IsCompl U P)
    [Module.Free ℤ_[ℓ] U] [Module.Finite ℤ_[ℓ] U]
    (hU : Module.finrank ℤ_[ℓ] U = g) :
    ∃ F : PrescribedLatticeQuotients ℓ A U, ∀ n x,
      (underlyingScheme.map ((F.quotient n).multiplicationFactor (ℓ ^ n) (F.killed n))).finrank x =
        (ℓ ^ n) ^ g := by
  choose H D hk _ himage hdegree using fun n =>
    exists_quotient_with_prescribed_lattice_and_degree A ℓ n U P hUP hU
  exact ⟨⟨H, D, hk, himage⟩, hdegree⟩

end SupersingularCurves.Geometry.ScalarFrobeniusTate
