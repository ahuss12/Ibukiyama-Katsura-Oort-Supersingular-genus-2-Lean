/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateQuotientPairing
import SupersingularCurves.Geometry.ScalarFrobeniusTateSymplecticGraph

/-!
# Actual graph quotient families with exact degree and zero dV

The rational graph supplies the required integral direct summand and half-rank.
Thus neither its complement nor its rank is an additional geometric assumption.
These families are precisely those used in the finite-model elliptic-map theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory AlgebraicGeometry GoodReductionJacobian AbelianTate
open scoped TensorProduct nonZeroDivisors
variable {K : Type} [Field K] [IsAlgClosed K] {g h : ℕ}
  (ℓ : ℕ) [Fact ℓ.Prime]

local instance {d : ℕ} (A : AbelianVariety K d) : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth d A.group.X.hom

/-- The actual integral intersection with any rational subspace has a complement. -/
theorem exists_complement_integralIntersection
    (A : AbelianVariety K g) (hℓ : (ℓ : K) ≠ 0)
    (W : Submodule ℚ_[ℓ] (Rational ℓ A)) :
    ∃ P : Submodule ℤ_[ℓ] (Integral ℓ A), IsCompl (integralIntersection ℓ A W) P := by
  letI := (finite_free_finrank ℓ A hℓ).1
  exact SymplecticLattice.exists_complement_intersection
    (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (Integral ℓ A) 1) W

/-- The graph's actual integral intersection has the source Tate rank. -/
theorem finrank_integralIntersection_productGraph
    (A : AbelianVariety K g) (B : AbelianVariety K h) (hℓ : (ℓ : K) ≠ 0)
    (e : Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ B) :
    Module.finrank ℤ_[ℓ]
      (integralIntersection ℓ (A.prod B) (productGraph ℓ A B e)) = 2 * g := by
  change Module.finrank ℤ_[ℓ]
    (SymplecticLattice.intersection
      (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (Integral ℓ (A.prod B)) 1)
      (productGraph ℓ A B e)) = 2 * g
  rw [SymplecticLattice.finrank_intersection]
  have hc : e.toLinearMap.graph ≤ LinearMap.range (rationalProdEquiv ℓ A B).toLinearMap := by
    rw [LinearMap.range_eq_top.mpr (rationalProdEquiv ℓ A B).surjective]
    exact le_top
  have hr := (Submodule.comap_equiv_self_of_inj_of_le
    (rationalProdEquiv ℓ A B).injective hc).finrank_eq
  change Module.finrank ℚ_[ℓ] (productGraph ℓ A B e) =
    Module.finrank ℚ_[ℓ] e.toLinearMap.graph at hr
  rw [hr, SymplecticLattice.finrank_graph]
  exact (finite_free_finrank ℓ A hℓ).2.2.2

/-- Rational isotropy descends to the original integral pairing, without
changing that pairing or supplying an integral isotropy assumption. -/
theorem integralIntersection_isotropic
    (A : AbelianVariety K g)
    (b : LinearMap.BilinForm ℤ_[ℓ] (Integral ℓ A))
    (W : Submodule ℚ_[ℓ] (Rational ℓ A))
    (hW : ∀ x ∈ W, ∀ y ∈ W, b.baseChange ℚ_[ℓ] x y = 0)
    (x y : Integral ℓ A)
    (hx : x ∈ integralIntersection ℓ A W) (hy : y ∈ integralIntersection ℓ A W) :
    b x y = 0 := by
  have H := hW ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x) hx ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] y) hy
  apply IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]
  simpa only [LinearMap.BilinForm.baseChange_tmul, one_mul, Algebra.smul_def,
    mul_one, map_zero] using H

/-- Construct the actual degree-controlled zero-dV graph quotient family.
Its complement, integral rank, and preservation of zero dV are conclusions. -/
theorem exists_prescribed_graph_quotients_with_degree_and_zeroDV
    (A B : AbelianVariety K g) (hℓ : (ℓ : K) ≠ 0)
    (e : Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ B)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hV : GroupScheme.verschiebungCotangent p (A.prod B).group
      (A.prod B).groupScheme_law_commutative = 0) :
    ∃ F : PrescribedLatticeQuotients ℓ (A.prod B)
        (integralIntersection ℓ (A.prod B) (productGraph ℓ A B e)),
      (∀ n x, (underlyingScheme.map
        ((F.quotient n).multiplicationFactor (ℓ ^ n) (F.killed n))).finrank x =
          (ℓ ^ n) ^ (g + g)) ∧
      ∀ n, GroupScheme.verschiebungCotangent p (F.quotient n).variety.group
        (F.quotient n).variety.groupScheme_law_commutative = 0 := by
  letI := (finite_free_finrank ℓ (A.prod B) hℓ).1
  letI := (finite_free_finrank ℓ (A.prod B) hℓ).2.1
  obtain ⟨P, hP⟩ := exists_complement_integralIntersection ℓ (A.prod B) hℓ
    (productGraph ℓ A B e)
  apply exists_prescribedLatticeQuotients_with_degree_and_zeroDV ℓ (A.prod B) hℓ p hV
    (integralIntersection ℓ (A.prod B) (productGraph ℓ A B e)) P hP
  simpa only [two_mul] using finrank_integralIntersection_productGraph ℓ A B hℓ e

end SupersingularCurves.Geometry.ScalarFrobeniusTate
