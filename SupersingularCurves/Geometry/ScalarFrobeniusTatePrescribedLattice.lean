/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTatePrescribedQuotient
import SupersingularCurves.Geometry.ScalarFrobeniusTateLatticeReduction

/-! # Actual isogenies realizing integral Tate lattices -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory AlgebraicGeometry GoodReductionJacobian AbelianTate
open IsLocalRing
variable {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}

/-- Every lattice U + ℓ^n T in the genuine Tate module is realized by the
actual multiplication factor of an actual finite subgroup quotient. -/
theorem exists_quotient_with_prescribed_lattice (A : AbelianVariety K g)
    (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (U : Submodule ℤ_[ℓ] (Integral ℓ A)) :
    ∃ H : FiniteSubgroup A, ∃ D : Quotient A H,
      ∃ hk : H.inclusion ≫ (GroupScheme.law A.group).schemeNsmul (ℓ ^ n) =
        (H.inclusion ≫ A.group.X.hom) ≫ ((GroupScheme.law A.group).one (𝟙 _)).1,
      (H.inclusion ≫ A.group.X.hom).finrank (IsLocalRing.closedPoint K) =
        Nat.card (reducedSubgroup ℓ n U) ∧
      IsIsogeny (D.multiplicationFactor (ℓ ^ n) hk) ∧
      LinearMap.range (integralMap ℓ (D.multiplicationFactor (ℓ ^ n) hk)) =
        U ⊔ (maximalIdeal ℤ_[ℓ] ^ n) • (⊤ : Submodule ℤ_[ℓ] (Integral ℓ A)) := by
  obtain ⟨H, D, hk, hrank, himage⟩ := exists_quotient_with_tate_image A ℓ n
    (reducedSubgroup ℓ n U) (reducedSubgroup_killed ℓ n U)
  refine ⟨H, D, hk, hrank,
    D.multiplicationFactor_isIsogeny (ℓ ^ n) hk
      (pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero), ?_⟩
  ext x
  exact (himage x).trans (proj_mem_reducedSubgroup_iff ℓ n U x)

end SupersingularCurves.Geometry.ScalarFrobeniusTate
