/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianTateFunctor

/-! # The rational span of genuine geometric endomorphisms -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory AlgebraicGeometry AbelianTate
variable {K : Type} [Field K] {g h : ℕ} (ℓ : ℕ) [Fact ℓ.Prime]

/-- The actual rational Tate operators coming from genuine endomorphisms,
closed under arbitrary rational ℓ-adic linear combinations. -/
def actualEndSpan (A : AbelianVariety K g) :
    Submodule ℚ_[ℓ] (Module.End ℚ_[ℓ] (Rational ℓ A)) :=
  Submodule.span ℚ_[ℓ] (Set.range (fun f : A.group ⟶ A.group => rationalMap ℓ f))

theorem rationalMap_mem_actualEndSpan (A : AbelianVariety K g) (f : A.group ⟶ A.group) :
    rationalMap ℓ f ∈ actualEndSpan ℓ A :=
  Submodule.subset_span ⟨f, rfl⟩

/-- Normalizing a geometric map B→A by a fixed geometric quasi-inverse A→B
produces an operator in the actual endomorphism span. This is the precise
span condition needed in Tate's compactness argument. -/
theorem normalized_map_mem_actualEndSpan
    (A : AbelianVariety K g) (B : AbelianVariety K h)
    (f : B.group ⟶ A.group) (q : A.group ⟶ B.group) (c : ℚ_[ℓ]) :
    (rationalMap ℓ f).comp (c • rationalMap ℓ q) ∈ actualEndSpan ℓ A := by
  have heq : (rationalMap ℓ f).comp (c • rationalMap ℓ q) =
      c • rationalMap ℓ (q ≫ f) := by
    apply LinearMap.ext
    intro x
    change rationalMap ℓ f (c • rationalMap ℓ q x) = c • rationalMap ℓ (q ≫ f) x
    rw [map_smul, rationalMap_comp]
    rfl
  rw [heq]
  exact (actualEndSpan ℓ A).smul_mem c (rationalMap_mem_actualEndSpan ℓ A (q ≫ f))

/-- A genuine group-scheme isomorphism preserves the actual integral Tate
lattice in both directions. -/
def integralEquivOfIso (A : AbelianVariety K g) (B : AbelianVariety K h)
    (e : A.group ≅ B.group) : Integral ℓ A ≃ₗ[ℤ_[ℓ]] Integral ℓ B :=
  LinearEquiv.ofLinearMap (integralMap ℓ e.hom) (integralMap ℓ e.inv)
    (by rw [← integralMap_comp, e.inv_hom_id, integralMap_id])
    (by rw [← integralMap_comp, e.hom_inv_id, integralMap_id])

@[simp] theorem integralEquivOfIso_apply (A : AbelianVariety K g)
    (B : AbelianVariety K h) (e : A.group ≅ B.group) (x : Integral ℓ A) :
    integralEquivOfIso ℓ A B e x = integralMap ℓ e.hom x := rfl

end SupersingularCurves.Geometry.ScalarFrobeniusTate
