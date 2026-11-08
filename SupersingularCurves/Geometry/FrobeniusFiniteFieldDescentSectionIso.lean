/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentSectionMap
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentSectionFractions
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_isIso
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing

/-!
# Affine section-ring reconstruction from a finite presentation

The section-ring reconstruction arguments use affineness, compactness, and
properness supplied by the finite projective presentation. These finite
versions reuse the generic local arguments in the corresponding pinned
upstream `IsCanonicalToProj` proofs; they assume no projective embedding.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentSectionProj
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules HomogeneousLocalization
open SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
open P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero
open P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_eq_zero_of_preimage_basicOpen_eq_bot
attribute [local instance] MvPolynomial.gradedAlgebra

open InjSol in
theorem exists_pow_mul_eq_zero_of_finiteBySections
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (_hL : Scheme.Modules.IsInvertible L) (hfinite : Scheme.Modules.FiniteBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ)
    (n : ℕ) (hn : 0 < n) (σ : 𝓡 n) (m : ℕ) (t : 𝓡 m)
    (ht : (L.tensorPow m).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤)).op (ι m t) = 0) :
    ∃ k : ℕ, (σ : R) ^ k * (t : R) = 0 := by
  obtain ⟨N, 𝔓, hci⟩ := hfinite
  have hcov : (⨆ i : Fin (N + 1), 𝔓.toProj ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i)) = ⊤ :=
    𝔓.toProj.iSup_preimage_eq_top
      (Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)
        (fun j => MvPolynomial.X j) (ProjSpace.irrelevant_le_span_X S N))
  have hWc : ∀ i : Fin (N + 1), IsCompact ((𝔓.toProj ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i) : X.Opens) : Set X) :=
    fun i => ((Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)
      (MvPolynomial.X i) (ProjSpace.X_mem_one S N i) one_pos).preimage 𝔓.toProj).isCompact
  have hsurj : ∀ i : Fin (N + 1), ∃ τ : 𝓡 1, ι 1 τ = (tensorPowOneIso L).symm.hom.app ⊤ (𝔓.σ i) :=
    fun i => (hR.bijective 1).2 _
  choose τs hτs using hsurj
  have hfr : ∀ i, IsFrameOn (ι 1 (τs i)) (𝔓.toProj ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i)) := fun i => by
    rw [hτs i]
    have hfr0 : IsFrameOn (𝔓.σ i) (𝔓.toProj ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i)) :=
      fun W hWU hWV => 𝔓.frame i W hWV
    exact hfr0.map_iso (tensorPowOneIso L).symm
  exact main_of_charts hR hθ _ hcov hWc τs hfr hn σ t ht


theorem exists_pow_eq_zero_of_finiteBySections
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (_hL : Scheme.Modules.IsInvertible L) (hfinite : Scheme.Modules.FiniteBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ)
    (n : ℕ) (hn : 0 < n) (σ : 𝓡 n) (hσ : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = ⊥) :
    ∃ k : ℕ, (σ : R) ^ k = 0 := by
  classical
  open NilpSol in

  obtain ⟨N, 𝔓, hci⟩ := hfinite
  have : CompactSpace X := by
    have : QuasiCompact (𝔓.toProj ≫ ProjSpace.π S N) := inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace (𝔓.toProj ≫ ProjSpace.π S N)

  have haff : ∀ x : X, ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧
      ∃ (m : ℕ) (hm : 0 < m) (τ : 𝓡 m), W ≤ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) := by
    intro x
    obtain ⟨m, hm, τ, hτ⟩ := NilpSol.exists_mem_basicOpen (𝓡 := 𝓡) (θ.base x)
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (a := x) (show x ∈ (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) : X.Opens) from hτ)
        (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)).2
    exact ⟨W, hW, hxW, m, hm, τ, hWV⟩
  choose W hWaff hxW hWch using haff

  have hloc : ∀ x : X, ∃ e : ℕ, ∀ E : ℕ, e ≤ E →
      NilpSol.rs L (E • n) (W x) (ι (E • n) ⟨(σ : R) ^ E, SetLike.pow_mem_graded E σ.2⟩) = 0 := by
    intro x
    obtain ⟨m, hm, τ, hWV⟩ := hWch x
    obtain ⟨g, hσm, hkey, hle⟩ := NilpSol.exists_chartFun hθ hn σ hm τ (W x) hWV
    have hbot : X.basicOpen g = ⊥ := le_bot_iff.mp (hle.trans_eq hσ)
    obtain ⟨k, hk⟩ := NilpSol.isNilpotent_of_basicOpen_eq_bot (hWaff x) g hbot
    obtain ⟨dk, ak, yk, hak, hdk, hrs⟩ := NilpSol.rs_pow hR (W x) (n • m) ⟨(σ : R) ^ m, hσm⟩ g _ hkey k
    rw [hk, zero_smul] at hrs
    refine ⟨m * k, fun E hE => ?_⟩
    refine NilpSol.rs_eq_zero_of_factor hR (W x) (E • n) _ dk ((E - m * k) • n) ak
      ⟨(σ : R) ^ (E - m * k), SetLike.pow_mem_graded (E - m * k) σ.2⟩ ?_ ?_ hrs
    · obtain ⟨E', rfl⟩ : ∃ E', E = m * k + E' := ⟨E - m * k, (Nat.add_sub_cancel' hE).symm⟩
      rw [hdk, Nat.add_sub_cancel_left]
      simp only [smul_eq_mul]
      ring
    · change (ak : R) * (σ : R) ^ (E - m * k) = (σ : R) ^ E
      rw [hak, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hE]
  choose e he using hloc

  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => ((W x : X.Opens) : Set X))
    (fun x => (W x).2) (fun y _ => Set.mem_iUnion.mpr ⟨y, hxW y⟩)

  let E : ℕ := ∑ x ∈ t, e x
  have hEe : ∀ x ∈ t, e x ≤ E := fun x hx => Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
  set s : Γ(L.tensorPow (E • n), ⊤) := ι (E • n) ⟨(σ : R) ^ E, SetLike.pow_mem_graded E σ.2⟩ with hs
  have hsW : ∀ x ∈ t, NilpSol.rs L (E • n) (W x) s = 0 := fun x hx => he x E (hEe x hx)

  have hs0 : s = 0 := by
    let F : TopCat.Sheaf Ab X := ⟨(L.tensorPow (E • n)).presheaf, Scheme.Modules.isSheaf _⟩
    refine F.eq_of_locally_eq' (fun j : t => W j.1) ⊤ (fun j => homOfLE le_top) ?_ s 0 ?_
    · intro y _
      obtain ⟨j, hj, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨j, hj⟩, hy⟩
    · intro j
      change NilpSol.rs L (E • n) (W j.1) s = NilpSol.rs L (E • n) (W j.1) 0
      rw [hsW j.1 j.2]
      simp
  exact ⟨E, NilpSol.coe_eq_zero_of_ι_eq_zero hR (E • n) ⟨(σ : R) ^ E, SetLike.pow_mem_graded E σ.2⟩
    (hs ▸ hs0)⟩


theorem denseRange_of_finiteBySections
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hL : Scheme.Modules.IsInvertible L) (hfinite : Scheme.Modules.FiniteBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ) :
    DenseRange θ.base := by
  classical
  refine dense_iff_inter_open.mpr fun O hO hOne => ?_
  obtain ⟨p, hp⟩ := hOne

  have hpO : p ∈ (⟨O, hO⟩ : (Proj 𝓡).Opens) := hp
  obtain ⟨W, ⟨f₀, rfl⟩, hpf, hfO⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Proj.isBasis_basicOpen 𝓡)) hpO
  have hf₀p : f₀ ∉ p.asHomogeneousIdeal := (Proj.mem_basicOpen 𝓡 f₀ p).mp hpf

  have hcomp : ∃ i : ℕ, (DirectSum.decompose 𝓡 f₀ i : R) ∉ p.asHomogeneousIdeal := by
    by_contra h
    push Not at h
    apply hf₀p
    rw [← DirectSum.sum_support_decompose 𝓡 f₀]
    exact Ideal.sum_mem _ fun i _ => h i
  obtain ⟨i, hi⟩ := hcomp

  have hrel : ∃ (j : ℕ) (h : R), 0 < j ∧ h ∈ 𝓡 j ∧ h ∉ p.asHomogeneousIdeal := by
    by_contra hcon
    push Not at hcon
    apply p.not_irrelevant_le
    intro a ha
    rw [← DirectSum.sum_support_decompose 𝓡 a]
    refine Ideal.sum_mem _ fun j _ => ?_
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have h0 : (DirectSum.decompose 𝓡 a 0 : R) = 0 := by
        rw [← GradedRing.proj_apply]; exact (HomogeneousIdeal.mem_irrelevant_iff 𝓡 a).mp ha
      rw [h0]; exact Ideal.zero_mem _
    · exact hcon j _ hj (SetLike.coe_mem _)

  obtain ⟨n, σ, hn, hσn, hσp, hσle⟩ : ∃ (n : ℕ) (σ : R), 0 < n ∧ σ ∈ 𝓡 n ∧ σ ∉ p.asHomogeneousIdeal ∧
      Proj.basicOpen 𝓡 σ ≤ Proj.basicOpen 𝓡 f₀ := by
    have hle_i : Proj.basicOpen 𝓡 (DirectSum.decompose 𝓡 f₀ i : R) ≤ Proj.basicOpen 𝓡 f₀ := by
      have := le_iSup (fun i : ℕ => Proj.basicOpen 𝓡 (GradedRing.proj 𝓡 i f₀)) i
      rw [← Proj.basicOpen_eq_iSup_proj 𝓡 f₀, GradedRing.proj_apply] at this
      exact this
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      obtain ⟨j, h, hj, hhj, hhp⟩ := hrel
      refine ⟨0 + j, (DirectSum.decompose 𝓡 f₀ 0 : R) * h, by omega, SetLike.mul_mem_graded (SetLike.coe_mem _) hhj,
        ?_, ?_⟩
      · intro hmem
        rcases p.isPrime.mem_or_mem hmem with h1 | h2
        · exact hi h1
        · exact hhp h2
      · rw [Proj.basicOpen_mul]
        exact inf_le_left.trans hle_i
    · exact ⟨i, _, hipos, SetLike.coe_mem _, hi, hle_i⟩

  have hne : θ ⁻¹ᵁ Proj.basicOpen 𝓡 σ ≠ ⊥ := by
    intro hbot
    obtain ⟨k, hk⟩ :=
      exists_pow_eq_zero_of_finiteBySections
        f L R 𝓡 ι hR hL hfinite θ hθ n hn ⟨σ, hσn⟩ hbot
    apply hσp
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [pow_zero] at hk
      have : σ = 0 := by rw [← mul_one σ, hk, mul_zero]
      rw [this]; exact Ideal.zero_mem _
    · exact p.isPrime.mem_of_pow_mem k (by rw [show ((⟨σ, hσn⟩ : 𝓡 n) : R) = σ from rfl] at hk; rw [hk]; exact Ideal.zero_mem _)
  obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne
  exact ⟨θ.base x, hfO (hσle hx), x, rfl⟩


theorem universallyClosed_of_finiteBySections
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (_hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (_hL : Scheme.Modules.IsInvertible L) (hfinite : Scheme.Modules.FiniteBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ) :
    UniversallyClosed θ := by
  obtain ⟨N, 𝔓, h𝔓⟩ := hfinite

  have : UniversallyClosed 𝔓.toProj := by have := h𝔓; infer_instance
  have : UniversallyClosed f := by
    rw [← 𝔓.toProj_π]; infer_instance

  have : UniversallyClosed (θ ≫ (Proj.toSpecZero 𝓡 ≫
      Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap S R))))) := by
    rw [hθ.comp_toSpecZero]; infer_instance
  exact UniversallyClosed.of_comp_of_isSeparated θ (Proj.toSpecZero 𝓡 ≫
      Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap S R))))


theorem isIso_basicOpen_of_finiteBySections
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hL : Scheme.Modules.IsInvertible L) (hfinite : Scheme.Modules.FiniteBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ)
    (m : ℕ) (hm : 0 < m) (τ : 𝓡 m) (haff : IsAffineOpen (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R))) :
    IsIso (θ ∣_ Proj.basicOpen 𝓡 (τ : R)) := by
  classical

  have : IsAffine (Proj.basicOpen 𝓡 (τ : R)) := Proj.isAffineOpen_basicOpen 𝓡 (τ : R) τ.2 hm
  have : IsAffine (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) := haff

  have hι : IsIso (Proj.awayToSection 𝓡 (τ : R)) := by
    rw [← Proj.basicOpenIsoAway_hom 𝓡 (τ : R) τ.2 hm]; infer_instance

  have hbij : Function.Bijective (Proj.awayToSection 𝓡 (τ : R) ≫
      θ.appLE (Proj.basicOpen 𝓡 (τ : R)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) le_rfl).hom := by

    have aux : ∀ (n k : ℕ) (σ : 𝓡 n), (σ : R) = (τ : R) ^ k → n = k • m →
        Function.Injective fun g : Γ(X, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) =>
          g • ((L.tensorPow n).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) ≤ ⊤)).op (ι n σ) :
            Γ(L.tensorPow n, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R))) := by
      intro n k σ hσ hn
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        have hn0 : n = 0 := by rw [hn, zero_smul]
        subst hn0
        have hσ1 : σ = ⟨1, SetLike.GradedOne.one_mem⟩ := Subtype.ext (by rw [hσ, pow_zero])
        subst hσ1
        rw [hR.map_one]
        change Function.Injective fun g : Γ(X, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) =>
          g • ((𝟙_ X.Modules).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) ≤ ⊤)).op
            (Scheme.Modules.unitSection ⊤) : Γ((𝟙_ X.Modules : X.Modules), θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)))
        rw [Scheme.Modules.map_unitSection]
        exact Scheme.Modules.smul_unitSection_bijective.1
      · have hnpos : 0 < n := by rw [hn, smul_eq_mul]; exact Nat.mul_pos hk hm
        have hfr := hθ.isFrameOn n hnpos σ
        have hle : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) ≤ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) := by
          rw [hσ, Proj.basicOpen_pow 𝓡 (τ : R) k hk]
        exact (hfr.bijective le_top hle).1

    have hρ : ∀ (k : ℕ) (s : 𝓡 (k • m)),
        ((Proj.awayToSection 𝓡 (τ : R) ≫
            θ.appLE (Proj.basicOpen 𝓡 (τ : R)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) le_rfl).hom
              (Away.mk 𝓡 τ.2 k (s : R) s.2)) •
          (L.tensorPow (k • m)).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) ≤ ⊤)).op
            (ι (k • m) ⟨(τ : R) ^ k, SetLike.pow_mem_graded k τ.2⟩) =
        (L.tensorPow (k • m)).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) ≤ ⊤)).op (ι (k • m) s) :=
      fun k s => hθ.appLE_awayToSection_smul m hm τ k s
    constructor
    ·
      rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨k, s, hs, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝓡 τ.2 z
      have h0 : (L.tensorPow (k • m)).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) ≤ ⊤)).op
          (ι (k • m) ⟨s, hs⟩) = 0 := by
        rw [← hρ k ⟨s, hs⟩, hz, zero_smul]
      obtain ⟨j, hj⟩ :=
        exists_pow_mul_eq_zero_of_finiteBySections
          f L R 𝓡 ι hR hL hfinite θ hθ m hm τ (k • m) ⟨s, hs⟩ h0
      apply HomogeneousLocalization.val_injective _
      rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_eq_mk',
        IsLocalization.mk'_eq_zero_iff]
      exact ⟨⟨(τ : R) ^ j, j, rfl⟩, hj⟩
    ·
      intro g
      obtain ⟨k, t, hkt⟩ :=
        finiteSectionRing_sectionFractions
          f L R 𝓡 ι hR θ hθ hfinite m hm τ g
      refine ⟨Away.mk 𝓡 τ.2 k (t : R) t.2, ?_⟩
      apply aux (k • m) k ⟨(τ : R) ^ k, SetLike.pow_mem_graded k τ.2⟩ rfl rfl
      show _ • _ = _ • _
      rw [hρ k t, hkt]
  have happLE : IsIso (θ.appLE (Proj.basicOpen 𝓡 (τ : R)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) le_rfl) := by
    have : IsIso (Proj.awayToSection 𝓡 (τ : R) ≫
        θ.appLE (Proj.basicOpen 𝓡 (τ : R)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) le_rfl) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hbij
    exact IsIso.of_isIso_comp_left (Proj.awayToSection 𝓡 (τ : R)) _

  have htop : IsIso ((θ ∣_ Proj.basicOpen 𝓡 (τ : R)).appTop) := by
    have main : ∀ (U' : (Proj 𝓡).Opens) (V' : X.Opens) (hU' : U' = Proj.basicOpen 𝓡 (τ : R))
        (hV' : V' = θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) (h : V' ≤ θ ⁻¹ᵁ U'), IsIso (θ.appLE U' V' h) := by
      rintro U' V' rfl rfl h
      exact happLE
    rw [Scheme.Hom.appTop, morphismRestrict_app']
    exact main _ _ (Scheme.Opens.ι_image_top _) (Scheme.Opens.ι_image_top _) _
  have key : (MorphismProperty.isomorphisms Scheme) (θ ∣_ Proj.basicOpen 𝓡 (τ : R)) :=
    (HasAffineProperty.iff_of_isAffine (P := MorphismProperty.isomorphisms Scheme)).mpr ⟨haff, htop⟩
  exact (MorphismProperty.isomorphisms.iff _).mp key


theorem isIso_canonicalToProj_of_finiteBySections
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hL : Scheme.Modules.IsInvertible L) (hfinite : Scheme.Modules.FiniteBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ) : IsIso θ := by
  classical
  obtain ⟨N, 𝔓, h𝔓⟩ := hfinite
  have : IsFinite 𝔓.toProj := h𝔓

  have hτ : ∀ i : Fin (N + 1), ∃ τ : 𝓡 1, (λ_ L).hom.app ⊤ (ι 1 τ) = 𝔓.σ i := by
    intro i
    obtain ⟨τ, hτ⟩ := (hR.bijective 1).2 ((λ_ L).inv.app ⊤ (𝔓.σ i))
    refine ⟨τ, ?_⟩
    rw [hτ]
    change ((λ_ L).inv ≫ (λ_ L).hom).app ⊤ (𝔓.σ i) = 𝔓.σ i
    rw [Iso.inv_hom_id]
    rfl
  choose τ hτ using hτ
  have hchart := fun i =>
    finitePresentation_preimage_basicOpen
      f L R 𝓡 ι hR θ hθ 𝔓 i (τ i) (hτ i)

  let U : Fin (N + 1) → (Proj 𝓡).Opens := fun i => Proj.basicOpen 𝓡 ((τ i : 𝓡 1) : R)

  have hiso : ∀ i, IsIso (θ ∣_ U i) := fun i =>
    isIso_basicOpen_of_finiteBySections
      f L R 𝓡 ι hR hL ⟨N, 𝔓, h𝔓⟩ θ hθ 1 one_pos (τ i) (hchart i).2

  have hpre : θ ⁻¹ᵁ (⨆ i, U i) = ⊤ := by
    rw [Scheme.Hom.preimage_iSup]
    have h1 : (⨆ i, θ ⁻¹ᵁ U i) = ⨆ i, 𝔓.toProj ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i) :=
      iSup_congr fun i => (hchart i).1
    rw [h1, ← Scheme.Hom.preimage_iSup,
      Proj.iSup_basicOpen_eq_top _ (fun i => MvPolynomial.X i) (ProjSpace.irrelevant_le_span_X S N),
      Scheme.Hom.preimage_top]

  have hsurj : Function.Surjective θ.base := by
    have := universallyClosed_of_finiteBySections f L R 𝓡 ι hR hL ⟨N, 𝔓, h𝔓⟩ θ hθ
    have hcl : IsClosed (Set.range θ.base) := θ.isClosedMap.isClosed_range
    have hd := denseRange_of_finiteBySections f L R 𝓡 ι hR hL ⟨N, 𝔓, h𝔓⟩ θ hθ
    rw [← Set.range_eq_univ, ← hcl.closure_eq, hd.closure_range]

  have hU : (⨆ i, U i) = ⊤ := by
    refine le_antisymm le_top fun p _ => ?_
    obtain ⟨x, rfl⟩ := hsurj p
    have hx : x ∈ θ ⁻¹ᵁ (⨆ i, U i) := by rw [hpre]; trivial
    exact hx

  have key : (MorphismProperty.isomorphisms Scheme) θ :=
    IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) U hU
      fun i => (MorphismProperty.isomorphisms.iff _).mpr (hiso i)
  exact (MorphismProperty.isomorphisms.iff _).mp key


/-- An actual invertible sheaf with finite projective presentation recovers
the original scheme as the Proj of its full, genuinely constructed section ring. -/
theorem exists_sectionRing_model_of_finiteBySections
    {S : Type u} [CommRing S] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (hfinite : L.FiniteBySections f) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra S R)
      (𝓡 : ℕ → Submodule S R) (_ : GradedAlgebra 𝓡)
      (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (e : X ≅ Proj 𝓡),
      GradedOAlgebra.IsSectionRing f L R 𝓡 ι ∧
      GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι e.hom := by
  obtain ⟨R, hRring, hRalg, 𝓡, hgrade, ι, hR⟩ :=
    GradedOAlgebra.exists_isSectionRing f L hL
  obtain ⟨θ, hθ⟩ := exists_canonicalToProj_of_finiteBySections
    f L R 𝓡 ι hR hL hfinite
  have : IsIso θ := isIso_canonicalToProj_of_finiteBySections
    f L R 𝓡 ι hR hL hfinite θ hθ
  exact ⟨R, hRring, hRalg, 𝓡, hgrade, ι, asIso θ, hR, hθ⟩

end SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentSectionProj
