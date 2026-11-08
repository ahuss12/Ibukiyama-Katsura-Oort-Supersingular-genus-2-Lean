/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_toProj_eq_comp_map_of_algebraMap
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_sigma_eq_smul

/-!
# Equivariance from actual fixed projective coordinates

Fixed sections in a genuine projective presentation make its scheme morphism
equivariant for the scheme automorphism and the coefficient action on projective
space. The proof compares actual pullback and scalar-restricted presentations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K]

/-- The actual morphism of projective space induced by a coefficient map. -/
def coefficientMap (σ : K →+* K) (N : ℕ) :
    Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) :=
  letI : Algebra K K := σ.toAlgebra
  ProjSpace.map K K N

/-- The actual projective coefficient morphism for the square of Frobenius. -/
def coefficientFrobeniusSquare (p : ℕ) (K : Type u) [Field K]
    [Fact p.Prime] [CharP K p] (N : ℕ) :
    Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) :=
  coefficientMap ((frobenius K p).comp (frobenius K p)) N

variable {X : Scheme.{u}} (τ : X ≅ X) (M : X.Modules)
  (eM : (Scheme.Modules.pullback τ.hom).obj M ≅ M)
  (c : X ⟶ Spec (CommRingCat.of K))

/-- A projective presentation by fixed sections is genuinely equivariant. -/
theorem toProj_equivariant_of_fixed_sections (σ : K →+* K)
    (hτ : τ.hom ≫ c = c ≫ Spec.map (CommRingCat.ofHom σ))
    {N : ℕ} (P : M.ProjPresentation c N)
    (hfixed : ∀ i, actionAddHom τ M eM (P.σ i) = P.σ i) :
    τ.hom ≫ P.toProj = P.toProj ≫ coefficientMap σ N := by
  obtain ⟨Ppb, hPpbσ, hPpb⟩ :=
    P.exists_projPresentation_pullback_sigma_eq_toProj_eq τ.hom
  obtain ⟨Pτ, hPτ, hPτσ⟩ := Ppb.exists_of_iso eM
  let Pτ' : M.ProjPresentation (c ≫ Spec.map (CommRingCat.ofHom σ)) N :=
    { Pτ with toProj_π := Pτ.toProj_π.trans hτ }
  have hPτ'σ (i : Fin (N + 1)) : Pτ'.σ i = P.σ i := by
    change Pτ.σ i = P.σ i
    rw [hPτσ, hPpbσ]
    exact hfixed i
  let : Algebra K K := σ.toAlgebra
  obtain ⟨Pσ, hPσσ, hPσ⟩ :=
    P.exists_sigma_eq_toProj_eq_comp_map_of_algebraMap (R := K)
  have heq : Pτ'.toProj = Pσ.toProj := by
    apply Pσ.toProj_eq_of_sigma_eq_smul Pτ' (1 : Γ(X, ⊤)) isUnit_one
    intro i
    rw [one_smul, hPτ'σ, hPσσ]
  calc
    τ.hom ≫ P.toProj = Pτ'.toProj := (hPτ.trans hPpb).symm
    _ = Pσ.toProj := heq
    _ = P.toProj ≫ coefficientMap σ N := hPσ

/-- Fixed projective coordinates intertwine a Frobenius-square-compatible
automorphism with the actual p² coefficient morphism of projective space. -/
theorem toProj_frobeniusSquare_equivariant_of_fixed_sections
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hτ : τ.hom ≫ c =
      c ≫ (SchemeFrobenius.baseMap p K ≫ SchemeFrobenius.baseMap p K))
    {N : ℕ} (P : M.ProjPresentation c N)
    (hfixed : ∀ i, actionAddHom τ M eM (P.σ i) = P.σ i) :
    τ.hom ≫ P.toProj =
      P.toProj ≫ coefficientFrobeniusSquare p K N := by
  apply toProj_equivariant_of_fixed_sections τ M eM c _ _ P hfixed
  rw [← baseMap_square]
  exact hτ

end SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
