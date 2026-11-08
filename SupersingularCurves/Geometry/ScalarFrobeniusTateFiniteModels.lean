/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateRecurrence
import SupersingularCurves.Geometry.ScalarFrobeniusTatePrescribedLattice
import SupersingularCurves.Geometry.ScalarFrobeniusTateEllipticSubgroup

/-!
# Finite quotient models produce actual elliptic maps

This completes the recurrence and compactness portion of the geometric Tate
argument. All quotient domains, morphisms, lattices, and rational Tate maps
are the actual ones. The remaining moduli input is stated explicitly as
`HasFiniteModels`; this file does not prove it from zero dV.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory AlgebraicGeometry AbelianTate
open scoped TensorProduct
variable {K : Type} [Field K] [IsAlgClosed K] {g h : ℕ}
variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- A sequence of genuine finite-subgroup quotients realizing the specified
integral lattices. No finiteness of their isomorphism classes is included. -/
structure PrescribedLatticeQuotients (A : AbelianVariety K g)
    (U : Submodule ℤ_[ℓ] (Integral ℓ A)) where
  subgroup : ℕ → FiniteSubgroup A
  quotient : ∀ n, Quotient A (subgroup n)
  killed : ∀ n, (subgroup n).inclusion ≫ (GroupScheme.law A.group).schemeNsmul (ℓ ^ n) =
    ((subgroup n).inclusion ≫ A.group.X.hom) ≫ ((GroupScheme.law A.group).one (𝟙 _)).1
  image : ∀ n, LinearMap.range
    (integralMap ℓ ((quotient n).multiplicationFactor (ℓ ^ n) (killed n))) =
    U ⊔ (IsLocalRing.maximalIdeal ℤ_[ℓ] ^ n) •
      (⊤ : Submodule ℤ_[ℓ] (Integral ℓ A))

/-- These actual quotient sequences exist for every integral Tate submodule. -/
theorem nonempty_prescribedLatticeQuotients (A : AbelianVariety K g)
    (U : Submodule ℤ_[ℓ] (Integral ℓ A)) : Nonempty (PrescribedLatticeQuotients ℓ A U) := by
  choose H D hk _ _ him using fun n => exists_quotient_with_prescribed_lattice A ℓ n U
  exact ⟨⟨H, D, hk, him⟩⟩

/-- Finiteness of the actual geometric quotient domains, up to actual
group-scheme isomorphism. This is the unresolved geometric boundedness input. -/
def PrescribedLatticeQuotients.HasFiniteModels {A : AbelianVariety K g}
    {U : Submodule ℤ_[ℓ] (Integral ℓ A)} (F : PrescribedLatticeQuotients ℓ A U) : Prop :=
  ∃ s : Finset (AbelianVariety K g), ∀ n,
    ∃ B ∈ s, Nonempty (B.group ≅ (F.quotient n).variety.group)

/-- The integral intersection of a rational subspace in the actual Tate module. -/
def integralIntersection (A : AbelianVariety K g)
    (W : Submodule ℚ_[ℓ] (Rational ℓ A)) : Submodule ℤ_[ℓ] (Integral ℓ A) :=
  (W.restrictScalars ℤ_[ℓ]).comap (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (Integral ℓ A) 1)

theorem exists_actualEndSpan_operator_of_finite_models
    (A : AbelianVariety K g) (hℓ : (ℓ : K) ≠ 0)
    (W : Submodule ℚ_[ℓ] (Rational ℓ A)) (hW : W ≠ ⊥)
    (F : PrescribedLatticeQuotients ℓ A (integralIntersection ℓ A W))
    (hF : F.HasFiniteModels ℓ) :
    ∃ u ∈ actualEndSpan ℓ A, u ≠ 0 ∧ LinearMap.range u ≤ W := by
  obtain ⟨w, hwW, hwne⟩ := PadicLattice.exists_nonzero_integral_vector ℓ W hW
  obtain ⟨s, hs⟩ := hF
  exact exists_actualEndSpan_operator_of_finite_quotient_models ℓ A hℓ
    (integralIntersection ℓ A W) W (fun _ hw => hw) w hwW hwne
    F.subgroup F.quotient F.killed F.image s hs

/-- The rational graph inside the genuine Tate module of the geometric product. -/
def productGraph (A : AbelianVariety K g) (B : AbelianVariety K h)
    (e : Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ B) :
    Submodule ℚ_[ℓ] (Rational ℓ (A.prod B)) :=
  e.toLinearMap.graph.comap (rationalProdEquiv ℓ A B).toLinearMap

theorem productGraph_ne_bot (A : AbelianVariety K g) (B : AbelianVariety K h)
    (e : Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ B) (hℓ : (ℓ : K) ≠ 0) (hg : g ≠ 0) :
    productGraph ℓ A B e ≠ ⊥ := by
  have hd := (finite_free_finrank ℓ A hℓ).2.2.2
  have : Nontrivial (Rational ℓ A) := Module.nontrivial_of_finrank_pos
    (by rw [hd]; exact Nat.mul_pos (by decide) (Nat.pos_of_ne_zero hg))
  obtain ⟨x, hx⟩ := exists_ne (0 : Rational ℓ A)
  apply (productGraph ℓ A B e).ne_bot_iff.mpr
  refine ⟨(rationalProdEquiv ℓ A B).symm (x, e x), ?_, ?_⟩
  · change (rationalProdEquiv ℓ A B
      ((rationalProdEquiv ℓ A B).symm (x, e x))).2 =
        e ((rationalProdEquiv ℓ A B ((rationalProdEquiv ℓ A B).symm (x, e x))).1)
    rw [LinearEquiv.apply_symm_apply]
  · intro hz
    have h := congrArg (fun z => (rationalProdEquiv ℓ A B z).1) hz
    rw [LinearEquiv.apply_symm_apply] at h
    have hzero := (rationalProdEquiv ℓ A B).toLinearMap.map_zero
    change rationalProdEquiv ℓ A B 0 = (0 : Rational ℓ A × Rational ℓ B) at hzero
    rw [hzero] at h
    exact hx h

/-- Finitely many models for the actual graph quotients construct a genuine
elliptic morphism in one of the two directions, with nonzero actual Tate map. -/
theorem exists_elliptic_map_of_finite_graph_quotient_models
    (A : AbelianVariety K 2) (E : AbelianVariety K 1) (hℓ : (ℓ : K) ≠ 0)
    (e : Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ (E.prod E))
    (F : PrescribedLatticeQuotients ℓ (A.prod (E.prod E))
      (integralIntersection ℓ (A.prod (E.prod E)) (productGraph ℓ A (E.prod E) e)))
    (hF : F.HasFiniteModels ℓ) :
    (∃ f : A.group ⟶ E.group, rationalMap ℓ f ≠ 0) ∨
      (∃ f : E.group ⟶ A.group, rationalMap ℓ f ≠ 0) := by
  obtain ⟨u, hu, hune, hurange⟩ := exists_actualEndSpan_operator_of_finite_models ℓ
    (A.prod (E.prod E)) hℓ (productGraph ℓ A (E.prod E) e)
    (productGraph_ne_bot ℓ A (E.prod E) e hℓ (by decide)) F hF
  rcases exists_actual_crossHom_of_actualEndSpan ℓ A (E.prod E) e u hu hune
      (fun z => hurange ⟨z, rfl⟩) with ⟨f, hf⟩ | ⟨f, hf⟩
  · exact Or.inl (exists_factor_map_of_prod_target ℓ E A f hf)
  · exact Or.inr (exists_factor_map_of_prod_domain ℓ E A f hf)

/-- The same finite-model input gives actual supersingular elliptic-product
isogenies in both directions. No elliptic subgroup or graph operator is assumed. -/
theorem exists_supersingular_product_isogenies_of_finite_graph_quotient_models
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (A : AbelianVariety K 2) (hA : A.HasPRankOver p 0)
    (E : AbelianVariety K 1) (hℓ : (ℓ : K) ≠ 0)
    (e : Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ (E.prod E))
    (F : PrescribedLatticeQuotients ℓ (A.prod (E.prod E))
      (integralIntersection ℓ (A.prod (E.prod E)) (productGraph ℓ A (E.prod E) e)))
    (hF : F.HasFiniteModels ℓ) :
    ∃ E₁ E₂ : AbelianVariety K 1,
      E₁.IsSupersingularElliptic p ∧ E₂.IsSupersingularElliptic p ∧
      (∃ f : (E₁.prod E₂).group ⟶ A.group, IsIsogeny f) ∧
      (∃ q : A.group ⟶ (E₁.prod E₂).group, IsIsogeny q) := by
  obtain ⟨u, hu, hune, hurange⟩ := exists_actualEndSpan_operator_of_finite_models ℓ
    (A.prod (E.prod E)) hℓ (productGraph ℓ A (E.prod E) e)
    (productGraph_ne_bot ℓ A (E.prod E) e hℓ (by decide)) F hF
  exact exists_supersingular_product_isogenies_of_actualEndSpan_graph p ℓ A hA E e
    u hu hune (fun z => hurange ⟨z, rfl⟩)

end SupersingularCurves.Geometry.ScalarFrobeniusTate
