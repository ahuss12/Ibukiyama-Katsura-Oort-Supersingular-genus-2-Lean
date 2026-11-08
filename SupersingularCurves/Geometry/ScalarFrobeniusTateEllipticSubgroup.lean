/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianSurfaceEllipticKernel
import SupersingularCurves.Geometry.ScalarFrobeniusTateActualGraph
import SupersingularCurves.Geometry.ScalarFrobeniusSurfaceProductIsogeny

/-! # From a realized Tate graph operator to geometric supersingularity

Both possible directions of the cross morphism are handled. The construction
does not assume an elliptic subgroup. Its remaining input is the nonzero graph
operator in the span of actual geometric endomorphisms; constructing that
operator globally remains a separate theorem.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory AlgebraicGeometry
variable {K : Type} [Field K] [IsAlgClosed K]

/-- The constructed subgroup feeds the existing geometric product-isogeny
theorem, meeting the original definition of supersingularity. -/
theorem isSupersingularOver_of_elliptic_rationalMap_ne_zero
    (p ℓ : ℕ) [Fact p.Prime] [CharP K p] [Fact ℓ.Prime]
    (A : AbelianVariety K 2) (hA : A.HasPRankOver p 0)
    (E : AbelianVariety K 1) (f : E.group ⟶ A.group)
    (hf : AbelianTate.rationalMap ℓ f ≠ 0) : A.IsSupersingularOver p := by
  obtain ⟨X, j, L, hj, hc, hs, hmul, -⟩ :=
    E.exists_closed_elliptic_subgroup_of_rationalMap_ne_zero ℓ A f hf
  letI := hj
  letI := hc
  letI := hs
  exact ScalarFrobeniusTate.isSupersingularOver_of_closed_elliptic_subgroup p A hA j L hmul


theorem isSupersingularOver_of_to_elliptic_rationalMap_ne_zero
    (p ℓ : ℕ) [Fact p.Prime] [CharP K p] [Fact ℓ.Prime]
    (A : AbelianVariety K 2) (hA : A.HasPRankOver p 0)
    (E : AbelianVariety K 1) (f : A.group ⟶ E.group)
    (hf : AbelianTate.rationalMap ℓ f ≠ 0) : A.IsSupersingularOver p := by
  obtain ⟨X, j, L, hj, hc, hs, hmul⟩ :=
    A.exists_closed_elliptic_subgroup_of_to_elliptic_rationalMap_ne_zero ℓ E f hf
  letI := hj
  letI := hc
  letI := hs
  exact ScalarFrobeniusTate.isSupersingularOver_of_closed_elliptic_subgroup p A hA j L hmul


end SupersingularCurves.Geometry.AbelianVariety

namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory AlgebraicGeometry GoodReductionJacobian AbelianTate
open FrobeniusFactorGroup
variable {K : Type} [Field K] [IsAlgClosed K]

theorem exists_closed_elliptic_subgroup_of_actualEndSpan_graph
    (ℓ : ℕ) [Fact ℓ.Prime] (A : AbelianVariety K 2) (E : AbelianVariety K 1)
    (e : Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ (E.prod E))
    (u : Module.End ℚ_[ℓ] (Rational ℓ (A.prod (E.prod E))))
    (hu : u ∈ actualEndSpan ℓ (A.prod (E.prod E))) (hne : u ≠ 0)
    (hgraph : ∀ z, (rationalProdEquiv ℓ A (E.prod E) (u z)).2 =
      e ((rationalProdEquiv ℓ A (E.prod E) (u z)).1)) :
    ∃ (X : Scheme) (j : X ⟶ A.group.X.left)
      (L : RelativeGroupLaw K (j ≫ A.group.X.hom)),
      IsClosedImmersion j ∧ ConnectedSpace X ∧
      SmoothOfRelativeDimension 1 (j ≫ A.group.X.hom) ∧
      (∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of K))
        (x y : NeronModelInfra.SchemeHomOver t (j ≫ A.group.X.hom)),
        pointMap j rfl (L.mul t x y) =
          (GroupScheme.law A.group).mul t (pointMap j rfl x) (pointMap j rfl y)) := by
  rcases exists_actual_crossHom_of_actualEndSpan ℓ A (E.prod E) e u hu hne hgraph with
    ⟨f, hf⟩ | ⟨f, hf⟩
  · obtain ⟨q, hq⟩ := exists_factor_map_of_prod_target ℓ E A f hf
    exact A.exists_closed_elliptic_subgroup_of_to_elliptic_rationalMap_ne_zero ℓ E q hq
  · obtain ⟨q, hq⟩ := exists_factor_map_of_prod_domain ℓ E A f hf
    obtain ⟨X, j, L, hj, hc, hs, hmul, -⟩ :=
      E.exists_closed_elliptic_subgroup_of_rationalMap_ne_zero ℓ A q hq
    exact ⟨X, j, L, hj, hc, hs, hmul⟩

/-- The actual graph operator yields actual product isogenies in both
directions, with both elliptic factors proved supersingular. -/
theorem exists_supersingular_product_isogenies_of_actualEndSpan_graph
    (p ℓ : ℕ) [Fact p.Prime] [CharP K p] [Fact ℓ.Prime]
    (A : AbelianVariety K 2) (hA : A.HasPRankOver p 0) (E : AbelianVariety K 1)
    (e : Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ (E.prod E))
    (u : Module.End ℚ_[ℓ] (Rational ℓ (A.prod (E.prod E))))
    (hu : u ∈ actualEndSpan ℓ (A.prod (E.prod E))) (hne : u ≠ 0)
    (hgraph : ∀ z, (rationalProdEquiv ℓ A (E.prod E) (u z)).2 =
      e ((rationalProdEquiv ℓ A (E.prod E) (u z)).1)) :
    ∃ E₁ E₂ : AbelianVariety K 1,
      E₁.IsSupersingularElliptic p ∧ E₂.IsSupersingularElliptic p ∧
      (∃ f : (E₁.prod E₂).group ⟶ A.group, IsIsogeny f) ∧
      (∃ q : A.group ⟶ (E₁.prod E₂).group, IsIsogeny q) := by
  obtain ⟨X, j, L, hj, hc, hs, hmul⟩ :=
    exists_closed_elliptic_subgroup_of_actualEndSpan_graph ℓ A E e u hu hne hgraph
  letI := hj
  letI := hc
  letI := hs
  exact exists_supersingular_elliptic_product_isogeny_of_closed_subgroup p A hA j L hmul

theorem isSupersingularOver_of_actualEndSpan_graph
    (p ℓ : ℕ) [Fact p.Prime] [CharP K p] [Fact ℓ.Prime]
    (A : AbelianVariety K 2) (hA : A.HasPRankOver p 0) (E : AbelianVariety K 1)
    (e : Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ (E.prod E))
    (u : Module.End ℚ_[ℓ] (Rational ℓ (A.prod (E.prod E))))
    (hu : u ∈ actualEndSpan ℓ (A.prod (E.prod E))) (hne : u ≠ 0)
    (hgraph : ∀ z, (rationalProdEquiv ℓ A (E.prod E) (u z)).2 =
      e ((rationalProdEquiv ℓ A (E.prod E) (u z)).1)) : A.IsSupersingularOver p := by
  obtain ⟨X, j, L, hj, hc, hs, hmul⟩ :=
    exists_closed_elliptic_subgroup_of_actualEndSpan_graph ℓ A E e u hu hne hgraph
  letI := hj
  letI := hc
  letI := hs
  exact isSupersingularOver_of_closed_elliptic_subgroup p A hA j L hmul

end SupersingularCurves.Geometry.ScalarFrobeniusTate
