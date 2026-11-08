/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentScheme
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_map_eq_comp

/-!
# Equivariance of the actual finite-field scheme model

The coherent section-ring action intertwines the genuine scheme automorphism
with its map on Proj. The fixed graded subalgebra is fixed pointwise, so its
Proj projection is invariant. This strengthens the finite-field model theorem
by retaining both the actual automorphism and the proved projection identity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.GradedOAlgebra
open FrobeniusDescent FrobeniusFiniteFieldDescentSectionProj

section Naturality
variable {K R : Type u} [Field K] [CommRing R] [Algebra K R]
variable {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K))
  (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
  (𝓡 : ℕ → Submodule K R) [GradedAlgebra 𝓡]
  (ι : ∀ n, 𝓡 n → Γ(M.tensorPow n, ⊤)) (hR : IsSectionRing c M R 𝓡 ι)
  (e : X ≅ Proj 𝓡) (he : IsCanonicalToProj c M R 𝓡 ι e.hom)
  (τ : X ≅ X) (eM : (Scheme.Modules.pullback τ.hom).obj M ≅ M)
  (σ : K →+* K) (hτ : τ.hom ≫ c = c ≫ Spec.map (CommRingCat.ofHom σ))

/-- The coherent section action as a genuinely degree preserving ring map. -/
def sectionRingGradedAction : 𝓡 →+*ᵍ 𝓡 where
  __ := sectionRingAction τ M eM c R 𝓡 ι hR
  map_mem := sectionRingAction_mem τ M eM c R 𝓡 ι hR _ _

theorem sectionRingGradedAction_irrelevant :
    HomogeneousIdeal.irrelevant 𝓡 ≤ (HomogeneousIdeal.irrelevant 𝓡).map
      (sectionRingGradedAction c M 𝓡 ι hR τ eM) := by
  apply (HomogeneousIdeal.irrelevant_le 𝓡).mpr
  intro n hn x hx
  obtain ⟨y, hy⟩ := (sectionRingDegreeAction_bijective τ M eM c R 𝓡 ι hR n).2 ⟨x,hx⟩
  have hy' : sectionRingGradedAction c M 𝓡 ι hR τ eM (y : R) = x := by
    change sectionRingAction τ M eM c R 𝓡 ι hR (y : R) = x
    rw [sectionRingAction_homogeneous]
    exact congrArg Subtype.val hy
  rw [← hy']
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem 𝓡 hn y.2)

include hM he hτ in
/-- Canonical reconstruction intertwines the actual scheme and section actions. -/
theorem sectionRingModel_equivariant [IsIso (Spec.map (CommRingCat.ofHom σ))] :
    e.hom ≫ Proj.map (sectionRingGradedAction c M 𝓡 ι hR τ eM)
      (sectionRingGradedAction_irrelevant c M 𝓡 ι hR τ eM) = τ.hom ≫ e.hom := by
  have ht : @IsScalarTower K K R σ.toAlgebra.toSMul inferInstance
      (((algebraMap K R).comp σ).toAlgebra.toSMul) := by
    refine @IsScalarTower.mk K K R σ.toAlgebra.toSMul inferInstance
      (((algebraMap K R).comp σ).toAlgebra.toSMul) ?_
    intro x y z
    simp only [Algebra.smul_def]
    change (algebraMap K R) (σ x * y) * z =
      (algebraMap K R) (σ x) * ((algebraMap K R) y * z)
    rw [map_mul, mul_assoc]
  let ϑ : @AlgHom K R R _ _ _ inferInstance ((algebraMap K R).comp σ).toAlgebra :=
    @AlgHom.mk K R R _ _ _ inferInstance ((algebraMap K R).comp σ).toAlgebra
      (sectionRingAction τ M eM c R 𝓡 ι hR)
      (sectionRingAction_algebraMap τ M eM c R 𝓡 ι hR σ hτ)
  have hp : IsPullback τ.hom c c (Spec.map (CommRingCat.ofHom σ)) :=
    IsPullback.of_horiz_isIso ⟨hτ⟩
  exact @IsCanonicalToProj.comp_map_eq_comp K _ K _ σ.toAlgebra X X c c τ.hom hp
    M hM M eM R _ inferInstance 𝓡 inferInstance ι hR
    R _ inferInstance ((algebraMap K R).comp σ).toAlgebra ht 𝓡 inferInstance ι hR ϑ
    (sectionRingAction_mem τ M eM c R 𝓡 ι hR)
    (sectionRingAction_formula τ M eM c R 𝓡 ι hR)
    (sectionRingGradedAction_irrelevant c M 𝓡 ι hR τ eM) e.hom he e.hom he

end Naturality

section FixedModel
variable {K : Type u} [Field K] [IsAlgClosed K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K)) [IsProper c]
variable (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
variable (hfinite : M.FiniteBySections c)
variable (τ : X ≅ X) (eM : (Scheme.Modules.pullback τ.hom).obj M ≅ M)
variable (hτ : τ.hom ≫ c = c ≫ (SchemeFrobenius.baseMap p K ≫ SchemeFrobenius.baseMap p K))

include hM hfinite eM hτ in
/-- The actual fixed section-ring model has invariant descent projection. -/
theorem exists_fixedField_equivariant_scheme_model :
    ∃ (X₀ : Scheme.{u}) (c₀ : X₀ ⟶ Spec (CommRingCat.of (fixedField K p 2)))
      (d : X ⟶ X₀),
      IsPullback d c c₀
        (Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K))) ∧
      τ.hom ≫ d = d := by
  obtain ⟨R, _, _, 𝓡, _, ι, e, hR, he⟩ :=
    exists_sectionRing_model_of_finiteBySections c M hM hfinite
  let θ := sectionRingAction τ M eM c R 𝓡 ι hR
  have hθ : ∀ (a : K) (x : R), θ (a • x) = a ^ (p ^ 2) • θ x :=
    sectionRingAction_frobeniusSquare_smul τ M eM c R 𝓡 ι hR p hτ
  have hd : ∀ n, ∀ x ∈ 𝓡 n, θ x ∈ 𝓡 n :=
    sectionRingAction_mem τ M eM c R 𝓡 ι hR
  have hi : Function.Injective θ := sectionRingAction_injective τ M eM c R 𝓡 ι hR
  have hf : ∀ n, FiniteDimensional K (𝓡 n) := by
    intro n
    let := sectionsModule (M.tensorPow n) c
    let := finite_sections_of_isProper (M.tensorPow n) c (hM.tensorPow n)
    exact (sectionRingDegreeLinearEquiv M c R 𝓡 ι hR n).symm.finiteDimensional
  let R₀ := fixedAlgebra p 2 θ hθ
  let 𝓡₀ := fixedGrading p 2 θ hθ 𝓡
  let := fixedGradedAlgebra p 2 θ hθ 𝓡 hd
  let ϑ : R₀ →ₐ[fixedField K p 2] R := (fixedAlgebra p 2 θ hθ).val
  have hd₀ : ∀ n, ∀ x ∈ 𝓡₀ n, ϑ x ∈ 𝓡 n := fun _ _ hx => hx
  have hbc : ∀ n, IsBaseChange K (pieceMap K R₀ 𝓡₀ R 𝓡 ϑ hd₀ n) := by
    intro n
    let := hf n
    change IsBaseChange K (fixedComponentMap p 2 θ hθ 𝓡 n)
    exact fixedComponent_isBaseChange p 2 θ hθ 𝓡 hd (by decide) hi n
  let γ := gradedMap K R₀ 𝓡₀ R 𝓡 ϑ hd₀
  have hγ : HomogeneousIdeal.irrelevant 𝓡 ≤ (HomogeneousIdeal.irrelevant 𝓡₀).map γ :=
    irrelevant_le_map_of_piece_baseChange K R₀ 𝓡₀ R 𝓡 ϑ hd₀ hbc
  let θg := sectionRingGradedAction c M 𝓡 ι hR τ eM
  have hθg : HomogeneousIdeal.irrelevant 𝓡 ≤ (HomogeneousIdeal.irrelevant 𝓡).map θg :=
    sectionRingGradedAction_irrelevant c M 𝓡 ι hR τ eM
  have hcomp : θg.comp γ = γ := by
    ext x
    exact x.property
  have hmap : Proj.map θg hθg ≫ Proj.map γ hγ = Proj.map γ hγ := by
    rw [← Proj.map_comp]
    congr 1
  have hτ' : τ.hom ≫ c = c ≫ Spec.map (CommRingCat.ofHom
      ((frobenius K p).comp (frobenius K p))) := by
    rw [← baseMap_square]
    exact hτ
  let : IsIso (Spec.map (CommRingCat.ofHom
      ((frobenius K p).comp (frobenius K p)))) := by
    rw [← baseMap_square]
    infer_instance
  have heq := sectionRingModel_equivariant c M hM 𝓡 ι hR e he τ eM _ hτ'
  refine ⟨Proj 𝓡₀, _, e.hom ≫ Proj.map γ hγ,
    isPullback_sectionModel_of_piece_baseChange K R₀ 𝓡₀ R 𝓡 ϑ hd₀ hbc c M ι e he, ?_⟩
  rw [← Category.assoc, ← heq, Category.assoc, hmap]

end FixedModel
end SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent

namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FrobeniusDescent FrobeniusFiniteFieldDescent SchemeFrobenius
variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p]
local instance : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth g A.group.X.hom

/-- Zero actual Verschiebung cotangent produces an equivariant finite-field
model with the actual residual Frobenius automorphism retained. -/
theorem exists_finiteField_equivariant_scheme_model_of_verschiebungCotangent_eq_zero
    (hV : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0) :
    ∃ (τ : A.group.X.left ≅ A.group.X.left),
      τ.hom ≫ A.group.X.hom = A.group.X.hom ≫ baseMap p K ≫ baseMap p K ∧
      (GroupScheme.law A.group).schemeNsmul p ≫ τ.hom =
        absolute p A.group.X.hom ≫ absolute p A.group.X.hom ∧
      ∃ (X₀ : Scheme.{u}) (c₀ : X₀ ⟶ Spec (CommRingCat.of (fixedField K p 2)))
        (d : A.group.X.left ⟶ X₀),
        IsPullback d A.group.X.hom c₀
          (Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K))) ∧
        τ.hom ≫ d = d := by
  obtain ⟨τ, M, hτ, hp, hM, hfinite, ⟨eM⟩⟩ :=
    A.exists_frobeniusSquare_automorphism_invariant_bundle p hV
  exact ⟨τ, hτ, hp,
    exists_fixedField_equivariant_scheme_model p A.group.X.hom M hM hfinite τ eM hτ⟩
end SupersingularCurves.Geometry.AbelianVariety
