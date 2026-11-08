/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Theorems.Thm_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints

/-!
# Actual finite subgroup descent over finite fields

A Galois-stable subgroup of the geometric points of a finite Hopf algebra
is represented by an actual quotient Hopf algebra over the finite ground
field. Its spectrum is a closed subgroup scheme, and its scheme-theoretic
order is the cardinality of the prescribed subgroup of geometric points.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SupersingularCurves.Geometry.ScalarFrobeniusIsogenySubgroup
open CategoryTheory AlgebraicGeometry

/-- Galois-fixed elements of an algebraic closure of a finite field
already lie in the ground field. This verifies the descent hypothesis of
the generic Hopf-quotient construction in positive characteristic. -/
theorem fixed_fraction (F : Type) [Field F] [Finite F]
    (c : AlgebraicClosure F)
    (hc : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
      (∀ r : F, σ (algebraMap F (AlgebraicClosure F) r) =
        algebraMap F (AlgebraicClosure F) r) → σ c = c) :
    ∃ a b : F, algebraMap F (AlgebraicClosure F) b ≠ 0 ∧
      c * algebraMap F (AlgebraicClosure F) b = algebraMap F (AlgebraicClosure F) a := by
  have hfix : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, σ c = c :=
    fun σ => hc σ (fun r => σ.commutes r)
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed c).mpr hfix
  exact ⟨a, 1, by simp, by simpa using ha.symm⟩

/-- The actual closed subgroup scheme over the finite ground field
representing a Galois-stable subgroup of geometric points. The universal
factorization condition specifies precisely which points it represents. -/
theorem exists_hopf_quotient_of_stable
    (F : Type) [Field F] [Finite F]
    (H : Type) [CommRing H] [HopfAlgebra F H] [Module.Finite F H]
    [Coalgebra.IsCocomm F H]
    (M : Type) [AddCommGroup M] [Finite M]
    (e : WithConv (H →ₐ[F] AlgebraicClosure F) ≃ M)
    (he : ∀ f g, e (f * g) = e f + e g)
    (act : (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) → M → M)
    (hact : ∀ (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
      (f g : WithConv (H →ₐ[F] AlgebraicClosure F)),
      (∀ h : H, g h = σ (f h)) → e g = act σ (e f))
    (N : AddSubgroup M)
    (hN : ∀ (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (x : M),
      x ∈ N → act σ x ∈ N) :
    ∃ (B : Type) (_ : CommRing B) (_ : HopfAlgebra F B),
      Module.Finite F B ∧ Coalgebra.IsCocomm F B ∧
      Module.finrank F B = Nat.card N ∧
      IsFinite (Spec.map (CommRingCat.ofHom (algebraMap F B))) ∧
      Flat (Spec.map (CommRingCat.ofHom (algebraMap F B))) ∧
      LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap F B))) ∧
      (∀ x : Spec (CommRingCat.of F),
        (Spec.map (CommRingCat.ofHom (algebraMap F B))).finrank x = Nat.card N) ∧
      ∃ π : H →ₐc[F] B, Function.Surjective π ∧
        IsClosedImmersion (Spec.map (CommRingCat.ofHom (π : H →ₐ[F] B).toRingHom)) ∧
        (∀ f : H →ₐ[F] AlgebraicClosure F,
          (∃ g : B →ₐ[F] AlgebraicClosure F, g.comp (π : H →ₐ[F] B) = f) ↔
            e (WithConv.toConv f) ∈ N) := by
  classical
  let Ns : Fin (1 + 1) → AddSubgroup M := ![N, ⊤]
  have hmono : ∀ i : Fin 1, Ns i.castSucc ≤ Ns i.succ := by
    intro i
    fin_cases i
    exact le_top
  have htop : Ns (Fin.last 1) = ⊤ := rfl
  have hstab : ∀ (i : Fin (1 + 1))
      (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (x : M),
      x ∈ Ns i → act σ x ∈ Ns i := by
    intro i σ x hx
    fin_cases i
    · exact hN σ x hx
    · exact AddSubgroup.mem_top _
  obtain ⟨B, instB, instH, π, φ, hft, hflat, hsurj, hφsurj, hcomp,
      hlast, hfactor, hcocomm, hfin⟩ :=
    HopfAlgebra.exists_quotientFlag_of_galoisStableChain_of_fixedPoints
      (K := F) (L := AlgebraicClosure F) F
      (algebraMap F (AlgebraicClosure F)).injective (fixed_fraction F)
      H M e he act hact 1 Ns hmono htop hstab
  let := instB
  let := instH
  have hfinite := (hfin inferInstance 0).1
  have hrank : Module.finrank F (B 0) = Nat.card N :=
    (hfin inferInstance 0).2 (by decide)
  have hscheme : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap F (B 0)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr hfinite
  have hschemeRank : ∀ x : Spec (CommRingCat.of F),
      (Spec.map (CommRingCat.ofHom (algebraMap F (B 0)))).finrank x = Nat.card N := by
    intro x
    rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
    exact hrank
  exact ⟨B 0, inferInstance, inferInstance, hfinite, hcocomm inferInstance 0,
    hrank, hscheme, inferInstance, inferInstance, hschemeRank,
    π 0, hsurj 0, IsClosedImmersion.spec_of_surjective _ (hsurj 0), hfactor 0⟩

end SupersingularCurves.Geometry.ScalarFrobeniusIsogenySubgroup
