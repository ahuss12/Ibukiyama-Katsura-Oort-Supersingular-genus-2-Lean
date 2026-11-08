/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_smul_map_pow_eq_map_of_section

/-!
# Actual section fractions from a finite projective presentation

A finite projective presentation supplies a finite affine cover of the actual
canonical map to the full section ring. Local fractions can consequently be
cleared and glued using the genuine section-ring multiplication. This requires
only finiteness of the presentation, with no closed immersion hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.GradedOAlgebra HomogeneousLocalization

open P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_preimage_basicOpen_eq_preimage_of_projPresentation_of_isClosedImmersion.ChartSol
  (mem_preimage_X_of_isFrameOn mem_preimage_basicOpen_of_isFrameOn_pow)
open P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_smul_map_pow_eq_map_of_section.F2SurjSol
  (ChartData nonempty_chartData preimage_inf_eq_basicOpen
    preimage_inf_preimage_eq_basicOpen main)

attribute [local instance] MvPolynomial.gradedAlgebra

variable {S : Type u} [CommRing S] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
  (R : Type u) [CommRing R] [Algebra S R]
  (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
  (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤))
  (hR : IsSectionRing f L R 𝓡 ι)
  (θ : X ⟶ Proj 𝓡) (hθ : IsCanonicalToProj f L R 𝓡 ι θ)

include hR hθ

/-- The degree-one canonical chart equals the corresponding chart of an
actual finite presentation, and is therefore affine. -/
theorem finitePresentation_preimage_basicOpen
    {N : ℕ} (P : ProjPresentation L f N) [IsFinite P.toProj]
    (i : Fin (N + 1)) (τ : 𝓡 1)
    (hτ : (λ_ L).hom.app ⊤ (ι 1 τ) = P.σ i) :
    θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) =
        P.toProj ⁻¹ᵁ Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i) ∧
      IsAffineOpen (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S
  have hfrσ : IsFrameOn (P.σ i) (P.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X i)) :=
    fun W _ hWV => P.frame i W hWV
  have hιτ : ι 1 τ = (λ_ L).inv.app ⊤ (P.σ i) := by
    rw [← hτ]
    change ι 1 τ = ((λ_ L).hom.app ⊤ ≫ (λ_ L).inv.app ⊤) (ι 1 τ)
    rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app]
    rfl
  have hfrτV : IsFrameOn (ι 1 τ)
      (P.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X i)) := by
    rw [hιτ]
    exact hfrσ.map_iso (λ_ L).symm
  have hfrτ : IsFrameOn (ι 1 τ) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) :=
    hθ.isFrameOn 1 one_pos τ
  have hfrσ' : IsFrameOn (P.σ i) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) := by
    rw [← hτ]
    exact hfrτ.map_iso (λ_ L)
  have heq : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) =
      P.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X i) :=
    le_antisymm
      (fun x hx => mem_preimage_X_of_isFrameOn P i hfrσ' x hx)
      (fun x hx => mem_preimage_basicOpen_of_isFrameOn_pow hR hθ τ hfrτV x hx)
  refine ⟨heq, ?_⟩
  rw [heq]
  exact (Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X i)
    (ProjSpace.X_mem_one S N i) one_pos).preimage P.toProj

/-- A finite presentation gives finitely many affine canonical charts covering
the original scheme. -/
theorem finiteSectionRing_affineCover (hfinite : FiniteBySections L f) :
    ∃ (N : ℕ) (τ : Fin (N + 1) → 𝓡 1),
      (⨆ i, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) = ⊤ ∧
      ∀ i, IsAffineOpen (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) := by
  obtain ⟨N, P, hP⟩ := hfinite
  have : IsFinite P.toProj := hP
  have hsurj : ∀ i : Fin (N + 1), ∃ t : 𝓡 1,
      ι 1 t = (tensorPowOneIso L).symm.hom.app ⊤ (P.σ i) :=
    fun i => (hR.bijective 1).2 _
  choose τ hτ using hsurj
  have hτ' : ∀ i, (λ_ L).hom.app ⊤ (ι 1 (τ i)) = P.σ i := by
    intro i
    rw [hτ i]
    change ((tensorPowOneIso L).inv ≫ (tensorPowOneIso L).hom).app ⊤ (P.σ i) = P.σ i
    rw [Iso.inv_hom_id, Scheme.Modules.Hom.id_app]
    rfl
  have hchart := fun i => finitePresentation_preimage_basicOpen
    f L R 𝓡 ι hR θ hθ P i (τ i) (hτ' i)
  refine ⟨N, τ, ?_, fun i => (hchart i).2⟩
  calc
    (⨆ i, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) =
        ⨆ i, P.toProj ⁻¹ᵁ Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i) :=
      iSup_congr fun i => (hchart i).1
    _ = ⊤ := P.toProj.iSup_preimage_eq_top
      (Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)
        (fun j => MvPolynomial.X j) (ProjSpace.irrelevant_le_span_X S N))

/-- Every actual function on a canonical basic chart is a homogeneous section
fraction, obtained by clearing powers and gluing over a finite affine cover. -/
theorem finiteSectionRing_sectionFractions (hfinite : FiniteBySections L f)
    (n : ℕ) (hn : 0 < n) (σ : 𝓡 n)
    (g : Γ(X, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))) :
    ∃ (k : ℕ) (t : 𝓡 (k • n)),
      g • (L.tensorPow (k • n)).presheaf.map
          (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤)).op
          (ι (k • n) ⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩) =
        (L.tensorPow (k • n)).presheaf.map
          (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤)).op (ι (k • n) t) := by
  obtain ⟨N, τ, hcov, haff⟩ := finiteSectionRing_affineCover f L R 𝓡 ι hR θ hθ hfinite
  let C : ∀ i, ChartData L R 𝓡 ι
      (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) (τ i) :=
    fun i => (nonempty_chartData f L R 𝓡 ι hR _ (τ i)
      (hθ.isFrameOn 1 one_pos (τ i))).some
  have hD : ∀ i,
      θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R) ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) =
        X.basicOpen ((C i).φ (σ : R)) :=
    fun i => preimage_inf_eq_basicOpen hθ (C i) hn σ
  have hVV : ∀ i j, IsCompact ((θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R) ⊓
      θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ j : R) : X.Opens) : Set X) := by
    intro i j
    rw [preimage_inf_preimage_eq_basicOpen hθ (C i) (τ j)]
    exact ((haff i).basicOpen _).isCompact
  obtain ⟨k, d, hd, t, h⟩ := main hR hcov haff C hVV n σ _ hD g
  subst hd
  exact ⟨k, t, h⟩

end SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
