/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateHopfPoints

/-! # Actual finite subgroups prescribed by geometric points -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian FrobeniusFactorGroup
open scoped CategoryTheory.MonObj
variable {K : Type} [Field K]

theorem scheme_factor_hopf_iff {B C : Type} [CommRing B] [CommRing C]
    [HopfAlgebra K B] [HopfAlgebra K C]
    (π : B →ₐc[K] C) (φ : B →ₐ[K] K) :
    (∃ a : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of C),
      a ≫ Spec.map (CommRingCat.ofHom (π : B →ₐ[K] C).toRingHom) =
        Spec.map (CommRingCat.ofHom φ.toRingHom)) ↔
    ∃ ψ : C →ₐ[K] K, ψ.comp (π : B →ₐ[K] C) = φ := by
  constructor
  · rintro ⟨a, ha⟩
    have hb : a ≫ (hopfGroup (K := K) C).X.hom =
        ((Spec (CommRingCat.of K)).asOver (Spec (CommRingCat.of K))).hom := by
      rw [← (hopfGroupMap π).hom.hom.w, ← Category.assoc]
      change (a ≫ Spec.map (CommRingCat.ofHom (π : B →ₐ[K] C).toRingHom)) ≫ _ = _
      rw [ha]
      exact (Spec.mapMulEquiv (.toConv φ)).w
    let a' : (Spec (CommRingCat.of K)).asOver (Spec (CommRingCat.of K)) ⟶
        (Spec (CommRingCat.of C)).asOver (Spec (CommRingCat.of K)) := Over.homMk a hb
    let ψ := (Spec.mapMulEquiv.symm a').ofConv
    have hψ : Spec.map (CommRingCat.ofHom ψ.toRingHom) = a :=
      congrArg Over.Hom.left (Spec.mapMulEquiv.apply_symm_apply a')
    refine ⟨ψ, ?_⟩
    have hs : Spec.map (CommRingCat.ofHom (ψ.comp (π : B →ₐ[K] C)).toRingHom) =
        Spec.map (CommRingCat.ofHom φ.toRingHom) := by
      change Spec.map (CommRingCat.ofHom (π : B →ₐ[K] C).toRingHom ≫
        CommRingCat.ofHom ψ.toRingHom) = _
      rw [Spec.map_comp, hψ, ha]
    exact AlgHom.ext fun b => congrArg
      (fun q : CommRingCat.of B ⟶ CommRingCat.of K => q b) (Spec.map_injective hs)
  · rintro ⟨ψ, hψ⟩
    refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom), ?_⟩
    rw [← Spec.map_comp]
    exact congrArg (fun q : B →ₐ[K] K => Spec.map (CommRingCat.ofHom q.toRingHom)) hψ

/-- A subgroup of the actual rational points of an actual finite closed
commutative group scheme is represented by an actual finite flat subgroup
of the abelian variety, with exactly its order. -/
theorem exists_finiteSubgroup_of_points {g : ℕ} (A : AbelianVariety K g)
    (G : GroupScheme K) [IsCommMonObj G.X] [IsFinite G.X.hom]
    (i : G ⟶ A.group) [IsClosedImmersion (underlyingScheme.map i)]
    (N : AddSubgroup (FiniteGroupPoints G)) :
    ∃ H : FiniteSubgroup A, ∃ jH : H.carrier ⟶ G.X.left,
      jH ≫ underlyingScheme.map i = H.inclusion ∧
      (H.inclusion ≫ A.group.X.hom).finrank (IsLocalRing.closedPoint K) = Nat.card N ∧
      ∀ x : FiniteGroupPoints G,
        (∃ a : Spec (CommRingCat.of K) ⟶ H.carrier,
          a ≫ H.inclusion = x.toMul.left ≫ underlyingScheme.map i) ↔ x ∈ N := by
  obtain ⟨B, hB, hH, hfin, ⟨e⟩⟩ := exists_finite_hopf_presentation G
  letI := hB
  letI := hH
  letI := hfin
  obtain ⟨C, hC, hHC, hfinC, hrank, π, hπ, hfactor⟩ :=
    exists_hopf_quotient_of_point_subgroup B (FiniteGroupPoints G)
      (hopfPointsEquiv e) (hopfPointsEquiv_mul e) N
  letI := hC
  letI := hHC
  letI := hfinC
  let j : hopfGroup (K := K) B ⟶ A.group := e.hom ≫ i
  letI : IsClosedImmersion (underlyingScheme.map j) := by
    dsimp [j]
    rw [Functor.map_comp]
    infer_instance
  let H := FiniteSubgroup.ofHopfQuotient A j π hπ
  refine ⟨H, underlyingScheme.map (hopfGroupMap π ≫ e.hom), ?_,
    (FiniteSubgroup.ofHopfQuotient_finrank A j π hπ _).trans hrank, ?_⟩
  · change underlyingScheme.map (hopfGroupMap π ≫ e.hom) ≫ underlyingScheme.map i =
      underlyingScheme.map (hopfGroupMap π ≫ (e.hom ≫ i))
    simp only [Functor.map_comp, Category.assoc]
  intro x
  obtain ⟨φ, rfl⟩ := (hopfPointsEquiv e).surjective x
  rw [← hfactor φ.ofConv]
  change (∃ a : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of C),
    a ≫ (Spec.map (CommRingCat.ofHom (π : B →ₐ[K] C).toRingHom) ≫ underlyingScheme.map j) =
      (Spec.map (CommRingCat.ofHom φ.ofConv.toRingHom) ≫ underlyingScheme.map e.hom) ≫
        underlyingScheme.map i) ↔ _
  have hj : underlyingScheme.map j = underlyingScheme.map e.hom ≫ underlyingScheme.map i :=
    Functor.map_comp _ _ _
  simp only [Category.assoc, ← hj]
  have hcancel : ∀ a : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of C),
      a ≫ Spec.map (CommRingCat.ofHom (π : B →ₐ[K] C).toRingHom) ≫ underlyingScheme.map j =
        Spec.map (CommRingCat.ofHom φ.ofConv.toRingHom) ≫ underlyingScheme.map j ↔
      a ≫ Spec.map (CommRingCat.ofHom (π : B →ₐ[K] C).toRingHom) =
        Spec.map (CommRingCat.ofHom φ.ofConv.toRingHom) := by
    intro a
    rw [← Category.assoc, cancel_mono]
  simp only [hcancel]
  exact scheme_factor_hopf_iff π φ.ofConv

end SupersingularCurves.Geometry.ScalarFrobeniusTate
