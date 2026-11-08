/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianTateProductMaps
import SupersingularCurves.Geometry.ScalarFrobeniusTateGraph
import SupersingularCurves.Geometry.ScalarFrobeniusTateEndSpan

/-! # Genuine cross morphisms from a Tate graph operator -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory AlgebraicGeometry GoodReductionJacobian AbelianTate
open scoped CategoryTheory.MonObj
variable {K : Type} [Field K] {g h : ℕ} (ℓ : ℕ) [Fact ℓ.Prime]

/-- Actual product endomorphisms expressed in the true Tate product coordinates. -/
def actualProductOperator (A : AbelianVariety K g) (B : AbelianVariety K h)
    (f : (A.prod B).group ⟶ (A.prod B).group) :
    Module.End ℚ_[ℓ] (Rational ℓ A × Rational ℓ B) :=
  (rationalProdEquiv ℓ A B).toLinearMap.comp
    ((rationalMap ℓ f).comp (rationalProdEquiv ℓ A B).symm.toLinearMap)

/-- Change from the actual product Tate module to its two-factor coordinates. -/
def productOperatorCoordinates (A : AbelianVariety K g) (B : AbelianVariety K h) :
    Module.End ℚ_[ℓ] (Rational ℓ (A.prod B)) →ₗ[ℚ_[ℓ]]
      Module.End ℚ_[ℓ] (Rational ℓ A × Rational ℓ B) where
  toFun v := (rationalProdEquiv ℓ A B).toLinearMap.comp
    (v.comp (rationalProdEquiv ℓ A B).symm.toLinearMap)
  map_add' v w := by
    apply LinearMap.ext
    intro z
    exact map_add (rationalProdEquiv ℓ A B) _ _
  map_smul' c v := by
    apply LinearMap.ext
    intro z
    exact map_smul (rationalProdEquiv ℓ A B) c _

theorem productOperatorCoordinates_mem_span (A : AbelianVariety K g)
    (B : AbelianVariety K h) (v : Module.End ℚ_[ℓ] (Rational ℓ (A.prod B)))
    (hv : v ∈ actualEndSpan ℓ (A.prod B)) :
    productOperatorCoordinates ℓ A B v ∈
      Submodule.span ℚ_[ℓ] (Set.range (actualProductOperator ℓ A B)) := by
  have hs : actualEndSpan ℓ (A.prod B) ≤
      (Submodule.span ℚ_[ℓ] (Set.range (actualProductOperator ℓ A B))).comap
        (productOperatorCoordinates ℓ A B) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl⟩
    exact Submodule.subset_span ⟨f, rfl⟩
  exact hs hv

theorem actualProductOperator_cross_left (A : AbelianVariety K g) (B : AbelianVariety K h)
    (f : (A.prod B).group ⟶ (A.prod B).group) (x : Rational ℓ A) :
    (actualProductOperator ℓ A B f (x, 0)).2 =
      rationalMap ℓ (A.prodInl B ≫ f ≫ A.prodSnd B) x := by
  have hx : (rationalProdEquiv ℓ A B).symm (x, 0) = rationalMap ℓ (A.prodInl B) x :=
    (rationalProdEquiv ℓ A B).symm_apply_eq.mpr (rationalProdEquiv_inl ℓ A B x).symm
  change (rationalProdEquiv ℓ A B (rationalMap ℓ f
    ((rationalProdEquiv ℓ A B).symm (x, 0)))).2 = _
  rw [hx, rationalProdEquiv_snd, rationalMap_comp, rationalMap_comp]
  rfl

theorem actualProductOperator_cross_right (A : AbelianVariety K g) (B : AbelianVariety K h)
    (f : (A.prod B).group ⟶ (A.prod B).group) (y : Rational ℓ B) :
    (actualProductOperator ℓ A B f (0, y)).1 =
      rationalMap ℓ (A.prodInr B ≫ f ≫ A.prodFst B) y := by
  have hy : (rationalProdEquiv ℓ A B).symm (0, y) = rationalMap ℓ (A.prodInr B) y :=
    (rationalProdEquiv ℓ A B).symm_apply_eq.mpr (rationalProdEquiv_inr ℓ A B y).symm
  change (rationalProdEquiv ℓ A B (rationalMap ℓ f
    ((rationalProdEquiv ℓ A B).symm (0, y)))).1 = _
  rw [hy, rationalProdEquiv_fst, rationalMap_comp, rationalMap_comp]
  rfl

/-- The graph argument produces a genuine geometric morphism in one direction,
whose genuine rational Tate map is nonzero. -/
theorem exists_actual_crossHom_of_graph_operator
    (A : AbelianVariety K g) (B : AbelianVariety K h)
    (e : Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ B)
    (u : Module.End ℚ_[ℓ] (Rational ℓ A × Rational ℓ B))
    (hu : u ∈ Submodule.span ℚ_[ℓ] (Set.range (actualProductOperator ℓ A B)))
    (hne : u ≠ 0)
    (hgraph : ∀ z, (u z).2 = e ((u z).1)) :
    (∃ f : A.group ⟶ B.group, rationalMap ℓ f ≠ 0) ∨
      (∃ f : B.group ⟶ A.group, rationalMap ℓ f ≠ 0) := by
  obtain ⟨f, h⟩ := exists_cross_component_of_mem_span_of_range_in_graph
    (actualProductOperator ℓ A B) e u hu hne hgraph
  rcases h with ⟨x, hx⟩ | ⟨y, hy⟩
  · left
    refine ⟨A.prodInl B ≫ f ≫ A.prodSnd B, ?_⟩
    intro hf
    rw [actualProductOperator_cross_left, hf, LinearMap.zero_apply] at hx
    exact hx rfl
  · right
    refine ⟨A.prodInr B ≫ f ≫ A.prodFst B, ?_⟩
    intro hf
    rw [actualProductOperator_cross_right, hf, LinearMap.zero_apply] at hy
    exact hy rfl

/-- The same extraction directly from the true rational endomorphism span,
without assuming a preselected family of cross morphisms. -/
theorem exists_actual_crossHom_of_actualEndSpan
    (A : AbelianVariety K g) (B : AbelianVariety K h)
    (e : Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ B)
    (u : Module.End ℚ_[ℓ] (Rational ℓ (A.prod B)))
    (hu : u ∈ actualEndSpan ℓ (A.prod B)) (hne : u ≠ 0)
    (hgraph : ∀ z, (rationalProdEquiv ℓ A B (u z)).2 =
      e ((rationalProdEquiv ℓ A B (u z)).1)) :
    (∃ f : A.group ⟶ B.group, rationalMap ℓ f ≠ 0) ∨
      (∃ f : B.group ⟶ A.group, rationalMap ℓ f ≠ 0) := by
  apply exists_actual_crossHom_of_graph_operator ℓ A B e
    (productOperatorCoordinates ℓ A B u) (productOperatorCoordinates_mem_span ℓ A B u hu)
  · intro hz
    apply hne
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun v : Module.End ℚ_[ℓ] (Rational ℓ A × Rational ℓ B) =>
      v (rationalProdEquiv ℓ A B x)) hz
    change rationalProdEquiv ℓ A B
      (u ((rationalProdEquiv ℓ A B).symm (rationalProdEquiv ℓ A B x))) = 0 at hx
    rw [LinearEquiv.symm_apply_apply] at hx
    exact (rationalProdEquiv ℓ A B).injective
      (hx.trans ((rationalProdEquiv ℓ A B).toLinearMap.map_zero).symm)
  · intro z
    exact hgraph ((rationalProdEquiv ℓ A B).symm z)

/-- A genuine map out of an actual square product is detected on one factor. -/
theorem exists_factor_map_of_prod_domain {d : ℕ}
    (E : AbelianVariety K g) (A : AbelianVariety K d)
    (f : (E.prod E).group ⟶ A.group) (hf : rationalMap ℓ f ≠ 0) :
    ∃ q : E.group ⟶ A.group, rationalMap ℓ q ≠ 0 := by
  by_contra h
  push_neg at h
  apply hf
  apply LinearMap.ext
  intro x
  have hx : x = rationalMap ℓ (E.prodInl E) (rationalProdEquiv ℓ E E x).1 +
      rationalMap ℓ (E.prodInr E) (rationalProdEquiv ℓ E E x).2 := by
    apply (rationalProdEquiv ℓ E E).injective
    rw [map_add, rationalProdEquiv_inl, rationalProdEquiv_inr]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  rw [hx, map_add]
  have h1 := LinearMap.congr_fun (h (E.prodInl E ≫ f)) (rationalProdEquiv ℓ E E x).1
  have h2 := LinearMap.congr_fun (h (E.prodInr E ≫ f)) (rationalProdEquiv ℓ E E x).2
  rw [rationalMap_comp] at h1 h2
  exact (congrArg₂ (· + ·) h1 h2).trans (zero_add 0)

/-- A genuine map into an actual square product is detected by one projection. -/
theorem exists_factor_map_of_prod_target {d : ℕ}
    (E : AbelianVariety K g) (A : AbelianVariety K d)
    (f : A.group ⟶ (E.prod E).group) (hf : rationalMap ℓ f ≠ 0) :
    ∃ q : A.group ⟶ E.group, rationalMap ℓ q ≠ 0 := by
  by_contra h
  push_neg at h
  apply hf
  apply LinearMap.ext
  intro x
  apply (rationalProdEquiv ℓ E E).injective
  change (rationalProdEquiv ℓ E E) (rationalMap ℓ f x) =
    (rationalProdEquiv ℓ E E) (0 : Rational ℓ (E.prod E))
  have hz : (rationalProdEquiv ℓ E E) (0 : Rational ℓ (E.prod E)) = 0 :=
    (rationalProdEquiv ℓ E E).toLinearMap.map_zero
  rw [hz]
  apply Prod.ext
  · rw [rationalProdEquiv_fst]
    exact LinearMap.congr_fun (by
      simpa only [rationalMap_comp] using h (f ≫ E.prodFst E)) x
  · rw [rationalProdEquiv_snd]
    exact LinearMap.congr_fun (by
      simpa only [rationalMap_comp] using h (f ≫ E.prodSnd E)) x

end SupersingularCurves.Geometry.ScalarFrobeniusTate
