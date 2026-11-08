/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateGraphQuotients
import SupersingularCurves.Geometry.AbelianTateRiemannRational

/-!
# Constructing the actual isotropic graph from perfect alternating pairings

The rational anti-isometry is constructed from the pairings on two actual
abelian surfaces. Its graph is transported into the Tate module of their actual
product. Isotropy holds for the original integral product pairing, and hence
on the actual degree-controlled quotient family. No finite-model conclusion is
asserted here.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory AlgebraicGeometry GoodReductionJacobian AbelianTate
open scoped TensorProduct

variable {K : Type} [Field K] [IsAlgClosed K]
  (ℓ : ℕ) [Fact ℓ.Prime]

local instance {d : ℕ} (X : AbelianVariety K d) : Smooth X.group.X.hom :=
  SmoothOfRelativeDimension.smooth d X.group.X.hom

/-- The sum of the actual pullback pairings along the two product projections. -/
def integralProductPairing {g h : ℕ} (A : AbelianVariety K g) (B : AbelianVariety K h)
    (b : LinearMap.BilinForm ℤ_[ℓ] (Integral ℓ A))
    (c : LinearMap.BilinForm ℤ_[ℓ] (Integral ℓ B)) :
    LinearMap.BilinForm ℤ_[ℓ] (Integral ℓ (A.prod B)) :=
  b.compl₁₂ (integralMap ℓ (A.prodFst B)) (integralMap ℓ (A.prodFst B)) +
    c.compl₁₂ (integralMap ℓ (A.prodSnd B)) (integralMap ℓ (A.prodSnd B))

/-- The integral intersection with the actual rational graph has precisely the
componentwise graph membership condition. -/
theorem mem_integralIntersection_productGraph_iff {g h : ℕ}
    (A : AbelianVariety K g) (B : AbelianVariety K h)
    (e : Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ B)
    (x : Integral ℓ (A.prod B)) :
    x ∈ integralIntersection ℓ (A.prod B) (productGraph ℓ A B e) ↔
      (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] integralMap ℓ (A.prodSnd B) x =
        e ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] integralMap ℓ (A.prodFst B) x) := Iff.rfl

/-- A rational anti-isometry makes the graph isotropic for the original
integral pairing on the actual product. -/
theorem integralProductPairing_graph_isotropic {g h : ℕ}
    (A : AbelianVariety K g) (B : AbelianVariety K h)
    (b : LinearMap.BilinForm ℤ_[ℓ] (Integral ℓ A))
    (c : LinearMap.BilinForm ℤ_[ℓ] (Integral ℓ B))
    (e : Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ B)
    (he : ∀ x y, (c.baseChange ℚ_[ℓ]) (e x) (e y) = -(b.baseChange ℚ_[ℓ]) x y)
    (x y : Integral ℓ (A.prod B))
    (hx : x ∈ integralIntersection ℓ (A.prod B) (productGraph ℓ A B e))
    (hy : y ∈ integralIntersection ℓ (A.prod B) (productGraph ℓ A B e)) :
    integralProductPairing ℓ A B b c x y = 0 := by
  have H := he ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] integralMap ℓ (A.prodFst B) x)
    ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] integralMap ℓ (A.prodFst B) y)
  rw [← (mem_integralIntersection_productGraph_iff ℓ A B e x).mp hx,
    ← (mem_integralIntersection_productGraph_iff ℓ A B e y).mp hy] at H
  simp only [LinearMap.BilinForm.baseChange_tmul, one_mul, Algebra.smul_def, mul_one] at H
  change b (integralMap ℓ (A.prodFst B) x) (integralMap ℓ (A.prodFst B) y) +
    c (integralMap ℓ (A.prodSnd B) x) (integralMap ℓ (A.prodSnd B) y) = 0
  apply IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]
  rw [map_add, map_zero, H, add_neg_cancel]

/-- Perfect alternating integral pairings construct the rational anti-isometry,
and its rank-four isotropic direct summand in the actual product Tate module. -/
theorem exists_isotropic_productGraph_of_perfect_pairings
    (A B : AbelianVariety K 2) (hℓ : (ℓ : K) ≠ 0)
    (b : LinearMap.BilinForm ℤ_[ℓ] (Integral ℓ A))
    (c : LinearMap.BilinForm ℤ_[ℓ] (Integral ℓ B))
    (hb : b.IsAlt) (hc : c.IsAlt) [b.IsPerfPair] [c.IsPerfPair] :
    ∃ e : Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ B,
      (∀ x y, (c.baseChange ℚ_[ℓ]) (e x) (e y) = -(b.baseChange ℚ_[ℓ]) x y) ∧
      Module.finrank ℤ_[ℓ]
        (integralIntersection ℓ (A.prod B) (productGraph ℓ A B e)) = 4 ∧
      (∃ P : Submodule ℤ_[ℓ] (Integral ℓ (A.prod B)),
        IsCompl (integralIntersection ℓ (A.prod B) (productGraph ℓ A B e)) P) ∧
      ∀ x ∈ integralIntersection ℓ (A.prod B) (productGraph ℓ A B e),
        ∀ y ∈ integralIntersection ℓ (A.prod B) (productGraph ℓ A B e),
          integralProductPairing ℓ A B b c x y = 0 := by
  letI := (finite_free_finrank ℓ A hℓ).1
  letI := (finite_free_finrank ℓ A hℓ).2.1
  letI := (finite_free_finrank ℓ B hℓ).1
  letI := (finite_free_finrank ℓ B hℓ).2.1
  obtain ⟨e, he⟩ := Symplectic.exists_antiIsometry_four
    (b.baseChange ℚ_[ℓ]) (c.baseChange ℚ_[ℓ])
    (pairing_baseChange_isAlt b hb) (pairing_baseChange_isAlt c hc)
    (pairing_baseChange_nondegenerate b hb) (pairing_baseChange_nondegenerate c hc)
    (finite_free_finrank ℓ A hℓ).2.2.2 (finite_free_finrank ℓ B hℓ).2.2.2
  refine ⟨e, he, finrank_integralIntersection_productGraph ℓ A B hℓ e,
    exists_complement_integralIntersection ℓ (A.prod B) hℓ (productGraph ℓ A B e), ?_⟩
  intro x hx y hy
  exact integralProductPairing_graph_isotropic ℓ A B b c e he x y hx hy

/-- The pairings construct the graph and actual quotient family together.
Every quotient has the exact degree, inherits zero dV, and its actual Tate
image has the required pairing divisibility. -/
theorem exists_isotropic_graph_quotients_with_degree_and_zeroDV
    (A B : AbelianVariety K 2) (hℓ : (ℓ : K) ≠ 0)
    (b : LinearMap.BilinForm ℤ_[ℓ] (Integral ℓ A))
    (c : LinearMap.BilinForm ℤ_[ℓ] (Integral ℓ B))
    (hb : b.IsAlt) (hc : c.IsAlt) [b.IsPerfPair] [c.IsPerfPair]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hV : GroupScheme.verschiebungCotangent p (A.prod B).group
      (A.prod B).groupScheme_law_commutative = 0) :
    ∃ e : Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ B,
      ∃ F : PrescribedLatticeQuotients ℓ (A.prod B)
        (integralIntersection ℓ (A.prod B) (productGraph ℓ A B e)),
      (∀ n x, (underlyingScheme.map
        ((F.quotient n).multiplicationFactor (ℓ ^ n) (F.killed n))).finrank x =
          (ℓ ^ n) ^ 4) ∧
      (∀ n, GroupScheme.verschiebungCotangent p (F.quotient n).variety.group
        (F.quotient n).variety.groupScheme_law_commutative = 0) ∧
      ∀ n (x y : Integral ℓ (F.quotient n).variety),
        (ℓ : ℤ_[ℓ]) ^ n ∣ integralProductPairing ℓ A B b c
          (integralMap ℓ ((F.quotient n).multiplicationFactor (ℓ ^ n) (F.killed n)) x)
          (integralMap ℓ ((F.quotient n).multiplicationFactor (ℓ ^ n) (F.killed n)) y) := by
  obtain ⟨e, _, _, _, hiso⟩ :=
    exists_isotropic_productGraph_of_perfect_pairings ℓ A B hℓ b c hb hc
  obtain ⟨F, hdegree, hzero⟩ :=
    exists_prescribed_graph_quotients_with_degree_and_zeroDV ℓ A B hℓ e p hV
  exact ⟨e, F, hdegree, hzero, fun n x y =>
    F.pairing_dvd ℓ (integralProductPairing ℓ A B b c) hiso n x y⟩

end SupersingularCurves.Geometry.ScalarFrobeniusTate
