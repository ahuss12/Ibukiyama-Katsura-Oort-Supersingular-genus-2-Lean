/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_isCanonicalToProj

/-!
# The canonical map from a finite projective presentation to the section ring

The canonical-map construction needs a finite collection of generating
sections, not an embedding. We supply its frame cover from the actual finite
presentation. The gluing argument is adapted from the pinned upstream
`S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_isCanonicalToProj`;
all geometric inputs are proved here from the stated finite presentation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentSectionProj
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules HomogeneousLocalization
open P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_isCanonicalToProj
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_frame_cover_of_finiteBySections
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hfinite : Scheme.Modules.FiniteBySections L f) :
    ∃ (N : ℕ) (τ : Fin (N + 1) → 𝓡 1) (V : Fin (N + 1) → X.Opens),
      (⨆ i, V i) = ⊤ ∧ ∀ i, AlgebraicGeometry.Scheme.Modules.IsFrameOn (ι 1 (τ i)) (V i) := by
  obtain ⟨N, 𝔓, -⟩ := hfinite
  have hsurj : ∀ i : Fin (N + 1), ∃ t : 𝓡 1, ι 1 t = (tensorPowOneIso L).symm.hom.app ⊤ (𝔓.σ i) :=
    fun i => (hR.bijective 1).2 _
  choose τ hτ using hsurj
  refine ⟨N, τ, fun i => 𝔓.toProj ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i), ?_, ?_⟩
  · exact 𝔓.toProj.iSup_preimage_eq_top
      (Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)
        (fun j => MvPolynomial.X j) (ProjSpace.irrelevant_le_span_X S N))
  · intro i
    rw [hτ i]
    have hfr : IsFrameOn (𝔓.σ i) (𝔓.toProj ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i)) :=
      fun W hWU hWV => 𝔓.frame i W hWV
    exact hfr.map_iso (tensorPowOneIso L).symm

open K10F2 Opposite in
theorem exists_canonicalToProj_of_finiteBySections
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (_hL : Scheme.Modules.IsInvertible L) (hfinite : Scheme.Modules.FiniteBySections L f) :
    ∃ θ : X ⟶ Proj 𝓡, AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ := by
  classical

  obtain ⟨N, τ, V, hV, hτV⟩ :=
    exists_frame_cover_of_finiteBySections
      f L R 𝓡 ι hR hfinite
  have dh := fun i =>
    AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_ringHom_smul_map_pow_eq f L R 𝓡 ι hR (τ i) (V i) (hτV i)
  choose φ hφa hφb hφc using dh

  have hφτ : ∀ i, φ i (τ i) = 1 := by
    intro i
    have h1 := hφc i 1 ⟨(τ i : R) ^ 1, SetLike.pow_mem_graded 1 (τ i).2⟩
    have hinj := ((hφb i 1) (le_top : V i ≤ ⊤) le_rfl).1
    have h2 : φ i ((τ i : R) ^ 1) = 1 := hinj (h1.trans (one_smul _ _).symm)
    simpa using h2

  have hunit : ∀ i j, IsUnit (X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (φ j (τ i))) := by
    intro i j
    have hc := hφc j 1 ⟨(τ i : R) ^ 1, SetLike.pow_mem_graded 1 (τ i).2⟩
    have hc' := congrArg ((L.tensorPow (1 • 1)).presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op) hc
    simp only [Scheme.Modules.map_smul] at hc'
    rw [Mmap_comp _ _ _ (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op,
      Mmap_comp _ _ _ (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op] at hc'
    have hfr : IsFrameOn ((L.tensorPow (1 • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
        (ι (1 • 1) ⟨(τ i : R) ^ 1, SetLike.pow_mem_graded 1 (τ i).2⟩)) (V i ⊓ V j) :=
      ((hφb i 1).mono inf_le_left).map (homOfLE (le_top : V i ⊓ V j ≤ ⊤))
    rw [← hc'] at hfr
    have key := AlgebraicGeometry.Scheme.Modules.IsFrameOn.isUnit_of_isFrameOn_smul
      (ι (1 • 1) ⟨(τ j : R) ^ 1, SetLike.pow_mem_graded 1 (τ j).2⟩) (hφb j 1)
      (le_top : V i ⊓ V j ≤ ⊤) inf_le_right _ hfr
    simpa using key

  have hkey : ∀ i j (k : ℕ) (s : R) (hs : s ∈ 𝓡 (k • 1)),
      X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (φ i s) *
        X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (φ j (τ i)) ^ k =
      X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (φ j s) := by
    intro i j k s hs
    apply ((hφb j k) (le_top : V i ⊓ V j ≤ ⊤) inf_le_right).1
    simp only

    have cj : ∀ t : 𝓡 (k • 1), X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (φ j t) •
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
          (ι (k • 1) ⟨(τ j : R) ^ k, SetLike.pow_mem_graded k (τ j).2⟩) =
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op (ι (k • 1) t) := by
      intro t
      have := congrArg ((L.tensorPow (k • 1)).presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op) (hφc j k t)
      simp only [Scheme.Modules.map_smul] at this
      rw [Mmap_comp _ _ _ (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op,
        Mmap_comp _ _ _ (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op] at this
      exact this
    have ci : ∀ t : 𝓡 (k • 1), X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (φ i t) •
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
          (ι (k • 1) ⟨(τ i : R) ^ k, SetLike.pow_mem_graded k (τ i).2⟩) =
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op (ι (k • 1) t) := by
      intro t
      have := congrArg ((L.tensorPow (k • 1)).presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op) (hφc i k t)
      simp only [Scheme.Modules.map_smul] at this
      rw [Mmap_comp _ _ _ (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op,
        Mmap_comp _ _ _ (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op] at this
      exact this
    have cjs : X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (φ j s) •
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
          (ι (k • 1) ⟨(τ j : R) ^ k, SetLike.pow_mem_graded k (τ j).2⟩) =
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op (ι (k • 1) ⟨s, hs⟩) := cj ⟨s, hs⟩
    have cjτ : X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (φ j ((τ i : R) ^ k)) •
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
          (ι (k • 1) ⟨(τ j : R) ^ k, SetLike.pow_mem_graded k (τ j).2⟩) =
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
          (ι (k • 1) ⟨(τ i : R) ^ k, SetLike.pow_mem_graded k (τ i).2⟩) :=
      cj ⟨(τ i : R) ^ k, SetLike.pow_mem_graded k (τ i).2⟩
    have cis : X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (φ i s) •
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
          (ι (k • 1) ⟨(τ i : R) ^ k, SetLike.pow_mem_graded k (τ i).2⟩) =
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op (ι (k • 1) ⟨s, hs⟩) := ci ⟨s, hs⟩
    rw [cjs, mul_smul, ← map_pow, ← map_pow, cjτ, cis]

  let θV : ∀ i, ((V i : X.Opens) : Scheme.{u}) ⟶ Proj 𝓡 := fun i => θOf R 𝓡 (V i) (φ i) (τ i) (hφτ i)
  have hcompat : ∀ i j, X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i =
      X.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ θV j := by
    intro i j
    apply AlgebraicGeometry.Proj.hom_ext_of_forall_exists_basicOpen 𝓡
    intro w
    have hpa : (X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R) = ⊤ := by
      rw [Scheme.Hom.comp_preimage, θOf_preimage (V i) (φ i) (τ i) (hφτ i) _ rfl one_pos (τ i), gOf_apply, hφτ i,
        map_one, Scheme.basicOpen_one, Scheme.Hom.preimage_top]
    have hpb : (X.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ θV j) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R) = ⊤ := by
      rw [Scheme.Hom.comp_preimage, θOf_preimage (V j) (φ j) (τ j) (hφτ j) _ rfl one_pos (τ i),
        Scheme.preimage_basicOpen_top]
      apply Scheme.basicOpen_of_isUnit
      rw [gOf_apply, homOfLE_appTop_topIso_inv _ ((homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op ≫
        (homOfLE ((V i ⊓ V j).ι_image_le ⊤)).op), Functor.map_comp, CategoryTheory.comp_apply]
      exact (hunit i j).map _
    refine ⟨1, (τ i : R), one_pos, (τ i).2, hpa.trans hpb.symm, by rw [hpa]; trivial, ?_⟩
    intro x
    obtain ⟨k, s, hs, rfl⟩ := Away.mk_surjective 𝓡 (τ i).2 x

    erw [← Scheme.Hom.appLE_comp_appLE (X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i)) (θV i)
        (Proj.basicOpen 𝓡 (τ i : R)) ((θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R))
        ((X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) le_rfl le_rfl]
    erw [← Scheme.Hom.appLE_comp_appLE (X.homOfLE (inf_le_right : V i ⊓ V j ≤ V j)) (θV j)
        (Proj.basicOpen 𝓡 (τ i : R)) ((θV j) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R))
        ((X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) le_rfl
        (hpa.trans hpb.symm).le]
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, Scheme.homOfLE_appLE, Scheme.homOfLE_appLE]
    have hΩle : (V i ⊓ V j).ι ''ᵁ ((X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) ≤
        V i ⊓ V j := (V i ⊓ V j).ι_image_le _
    have key2 : ∀ (m₁ : op ((V i).ι ''ᵁ ((θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R))) ⟶
          op ((V i ⊓ V j).ι ''ᵁ ((X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R))))
        (m₂ : op ((V j).ι ''ᵁ ((θV j) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R))) ⟶
          op ((V i ⊓ V j).ι ''ᵁ ((X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)))),
        X.presheaf.map m₁ ((θV i).appLE (Proj.basicOpen 𝓡 (τ i : R)) ((θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) le_rfl
          (Proj.awayToSection 𝓡 (τ i : R) (Away.mk 𝓡 (τ i).2 k s hs))) =
        X.presheaf.map m₂ ((θV j).appLE (Proj.basicOpen 𝓡 (τ i : R)) ((θV j) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) le_rfl
          (Proj.awayToSection 𝓡 (τ i : R) (Away.mk 𝓡 (τ i).2 k s hs))) := by
      intro m₁ m₂
      have vi := θOf_value (V i) (φ i) (τ i) (hφτ i) (θV i) rfl one_pos (τ i) k s hs
        ((θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) le_rfl m₁ (homOfLE (hΩle.trans inf_le_left)).op
      rw [hφτ i, map_one, one_pow, mul_one] at vi
      have vj := θOf_value (V j) (φ j) (τ j) (hφτ j) (θV j) rfl one_pos (τ i) k s hs
        ((θV j) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) le_rfl m₂ (homOfLE (hΩle.trans inf_le_right)).op
      have hk := congrArg (X.presheaf.map (homOfLE hΩle).op) (hkey i j k s hs)
      rw [map_mul, map_pow, Xmap_comp _ _ (homOfLE (hΩle.trans inf_le_left)).op,
        Xmap_comp _ _ (homOfLE (hΩle.trans inf_le_right)).op, Xmap_comp _ _ (homOfLE (hΩle.trans inf_le_right)).op,
        ← vi, ← vj] at hk
      have hu : IsUnit (X.presheaf.map (homOfLE (hΩle.trans inf_le_right)).op (φ j (τ i)) ^ k) := by
        have := ((hunit i j).map (ConcreteCategory.hom (X.presheaf.map (homOfLE hΩle).op))).pow k
        rwa [Xmap_comp _ _ (homOfLE (hΩle.trans inf_le_right)).op] at this
      exact hu.mul_left_inj.mp hk
    exact key2 _ _

  let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover V hV
  have hglue : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ θV i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ θV j := by
    intro i j
    have P := isPullback_opens_inf (V i) (V j)
    change pullback.fst (V i).ι (V j).ι ≫ θV i = pullback.snd (V i).ι (V j).ι ≫ θV j
    rw [← cancel_epi P.isoPullback.hom, P.isoPullback_hom_fst_assoc, P.isoPullback_hom_snd_assoc]
    exact hcompat i j
  let θ : X ⟶ Proj 𝓡 := 𝒰.glueMorphisms θV hglue
  have hθV : ∀ i, (V i).ι ≫ θ = θV i := fun i => 𝒰.ι_glueMorphisms θV hglue i

  have hVW : ∀ {n : ℕ} (hn : 0 < n) (σ : 𝓡 n) (i),
      V i ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = X.basicOpen (φ i σ) := by
    intro n hn σ i
    rw [← image_θOf_preimage (V i) (φ i) (τ i) (hφτ i) ((V i).ι ≫ θ) (hθV i) hn σ, Scheme.Hom.comp_preimage,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hcovσ : ∀ {n : ℕ} (hn : 0 < n) (σ : 𝓡 n),
      θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = ⨆ i, X.basicOpen (φ i σ) := by
    intro n hn σ
    calc θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = (⨆ i, V i) ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) := by rw [hV, top_inf_eq]
      _ = ⨆ i, (V i ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) := iSup_inf_eq _ _
      _ = ⨆ i, X.basicOpen (φ i σ) := by simp_rw [hVW hn σ]
  refine ⟨θ, ⟨?_, ?_, ?_⟩⟩
  ·
    apply 𝒰.hom_ext
    intro i
    change (V i).ι ≫ θ ≫ Proj.toSpecZero 𝓡 ≫ _ = (V i).ι ≫ f
    rw [← Category.assoc, hθV i]
    change Proj.fromOfGlobalSections 𝓡 (gOf R (V i) (φ i)) _ ≫ Proj.toSpecZero 𝓡 ≫ _ = (V i).ι ≫ f
    rw [Proj.fromOfGlobalSections_toSpecZero_assoc, ← Spec.map_comp]
    have hr : (V i).ι ≫ f = ((V i : X.Opens) : Scheme.{u}).toSpecΓ ≫
        Spec.map ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ ((V i).ι ≫ f).appTop) := by
      rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    rw [hr]
    congr 2
    apply CommRingCat.hom_ext
    ext a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
      Scheme.Hom.comp_appTop]
    have ha0 : algebraMap S R a ∈ 𝓡 0 := by
      rw [Algebra.algebraMap_eq_smul_one]; exact Submodule.smul_mem _ a SetLike.GradedOne.one_mem
    have e1 : (GradedRing.projZeroRingHom' 𝓡) (algebraMap S R a) = ⟨algebraMap S R a, ha0⟩ :=
      GradedRing.projZeroRingHom'_apply_coe 𝓡 ⟨algebraMap S R a, ha0⟩
    rw [e1]
    change gOf R (V i) (φ i) (algebraMap S R a) = (V i).ι.appTop (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of S)).inv a))
    rw [gOf_apply, hφa i a, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
    exact Xmap_comp _ _ _ _
  ·
    intro n hn σ
    rw [hcovσ hn σ]
    apply AlgebraicGeometry.Scheme.Modules.IsFrameOn.of_iSup_monoidalV2
    intro i
    have hn1 : n = n • 1 := by simp
    rw [isFrameOn_transport L 𝓡 ι hn1 σ]
    have hBV : X.basicOpen (φ i σ) ≤ V i := X.basicOpen_le _
    apply isFrameOn_of_restrict _ (hBV.trans le_top)
    have hc := hφc i n ⟨(σ : R), hn1 ▸ σ.2⟩
    have hc' := congrArg ((L.tensorPow (n • 1)).presheaf.map (homOfLE hBV).op) hc
    simp only [Scheme.Modules.map_smul] at hc'
    rw [Mmap_comp _ _ _ (homOfLE (hBV.trans le_top)).op, Mmap_comp _ _ _ (homOfLE (hBV.trans le_top)).op] at hc'
    rw [← hc']
    exact isFrameOn_smul_of_isUnit _ (hφb i n) le_top hBV _ (RingedSpace.isUnit_res_basicOpen _ (φ i σ))
  ·
    intro n hn σ k s
    have hkn : k • n = (k • n) • 1 := by simp
    apply sections_ext V hV
    intro i
    simp only [Scheme.Modules.map_smul]
    rw [Mmap_comp _ _ _ (homOfLE le_top).op, Mmap_comp _ _ _ (homOfLE le_top).op]

    have hWle : V i ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ V i := inf_le_left
    have cσ := hφc i (k • n) ⟨((⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩ : 𝓡 (k • n)) : R),
      hkn ▸ (⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩ : 𝓡 (k • n)).2⟩
    have cs := hφc i (k • n) ⟨(s : R), hkn ▸ s.2⟩
    rw [smul_eq_transport L 𝓡 ι hkn ⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩ s]
    have cσ' := congrArg ((L.tensorPow ((k • n) • 1)).presheaf.map (homOfLE hWle).op) cσ
    have cs' := congrArg ((L.tensorPow ((k • n) • 1)).presheaf.map (homOfLE hWle).op) cs
    simp only [Scheme.Modules.map_smul] at cσ' cs'
    rw [Mmap_comp _ _ _ (homOfLE le_top).op, Mmap_comp _ _ _ (homOfLE le_top).op] at cσ' cs'
    rw [← cσ', ← cs', smul_smul]
    congr 1

    have v := θOf_value (V i) (φ i) (τ i) (hφτ i) ((V i).ι ≫ θ) (hθV i) hn σ k (s : R) s.2
      (((V i).ι ≫ θ) ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) le_rfl
      (W₀ := V i ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))
      (homOfLE (by rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι])).op (homOfLE hWle).op
    rw [map_pow, map_pow, ← v]
    congr 1
    rw [← Scheme.Hom.appLE_comp_appLE ((V i).ι) θ (Proj.basicOpen 𝓡 (σ : R)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))
        (((V i).ι ≫ θ) ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) le_rfl le_rfl, CategoryTheory.comp_apply, Scheme.Opens.ι_appLE]
    exact (Xmap_comp _ _ _ _).symm

end SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentSectionProj
