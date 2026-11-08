/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingHeightOne
import Theorems.Thm_HopfAlgebra_mem_ker_counit_sq_of_map_mem_sq_of_injective_of_forall_pow_prime_eq_zero
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq

/-!
# A height-one finite Hopf morphism with zero differential is zero

Factor the actual morphism through its Hopf image. Cotangent injectivity
into a height-one group makes the augmentation ideal of that image
idempotent. Its elements are nilpotent, so the image is trivial.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.HeightOneHopf
open Coalgebra

variable {K : Type u} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
  {H D : Type v} [CommRing H] [HopfAlgebra K H] [Module.Finite K H]
  [CommRing D] [HopfAlgebra K D] [Module.Finite K D]

/-- A Hopf morphism into a height-one coordinate algebra that kills
augmentation modulo its square is the actual unit-counit morphism. -/
theorem eq_counit_of_augmentation_mem_sq
    (hD : ∀ x : D, counit (R := K) x = 0 → x ^ p = 0)
    (φ : H →ₐc[K] D)
    (hφ : ∀ a : H, counit (R := K) a = 0 →
      φ a ∈ RingHom.ker (Bialgebra.counitAlgHom K D) ^ 2) :
    ∀ a : H, φ a = algebraMap K D (counit (R := K) a) := by
  obtain ⟨Q, hR, hH, hfin, hflat, π, ι, hπ, hι, he⟩ :=
    HopfAlgebra.exists_hopfAlgebra_surjective_injective_comp_eq φ
  letI := hR
  letI := hH
  letI := hfin
  letI := hflat
  letI : IsNoetherianRing Q := isNoetherian_of_tower K inferInstance
  let I : Ideal Q := RingHom.ker (Bialgebra.counitAlgHom K Q)
  have hQ : ∀ x : Q, counit (R := K) x = 0 → x ^ p = 0 := by
    intro x hx
    apply hι
    rw [map_pow, map_zero]
    exact hD _ ((CoalgHomClass.counit_comp_apply ι x).trans hx)
  have hIsq : I ≤ I ^ 2 := by
    intro x hx
    obtain ⟨a, rfl⟩ := hπ x
    have ha : counit (R := K) a = 0 := by
      exact (CoalgHomClass.counit_comp_apply π a).symm.trans hx
    apply HopfAlgebra.mem_ker_counit_sq_of_map_mem_sq_of_injective_of_forall_pow_prime_eq_zero
      K p D hD Q ι hι (π a) hx
    have hcomp : ι (π a) = φ a := congrArg (fun f : H →ₐc[K] D => f a) he
    rw [hcomp]
    exact hφ a ha
  have hnil : IsNilpotent I := by
    apply (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian I)).mpr
    intro x hx
    exact ⟨p, hQ x hx⟩
  have hI : I = 0 := by
    apply IsIdempotentElem.eq_zero_of_isNilpotent _ hnil
    change I * I = I
    rw [← pow_two]
    exact le_antisymm (Ideal.pow_le_self (by decide)) hIsq
  intro a
  have hz : π (a - algebraMap K H (counit (R := K) a)) = 0 := by
    have hm : π (a - algebraMap K H (counit (R := K) a)) ∈ I := by
      change counit (R := K) (π (a - algebraMap K H (counit (R := K) a))) = 0
      rw [CoalgHomClass.counit_comp_apply]
      change (Bialgebra.counitAlgHom K H) (a - algebraMap K H
        ((Bialgebra.counitAlgHom K H) a)) = 0
      simp
    rw [hI] at hm
    exact hm
  have heq : φ (a - algebraMap K H (counit (R := K) a)) = 0 := by
    rw [← he]
    change ι (π _) = 0
    rw [hz, map_zero]
  simpa only [map_sub, AlgHomClass.commutes, sub_eq_zero] using heq

/-- The actual coordinate cotangent map induced by a finite Hopf morphism. -/
def cotangentMap (φ : H →ₐc[K] D) :
    (RingHom.ker (Bialgebra.counitAlgHom K H)).Cotangent →ₗ[K]
      (RingHom.ker (Bialgebra.counitAlgHom K D)).Cotangent :=
  Ideal.mapCotangent _ _ φ.toAlgHom (by
    intro a ha
    change counit (R := K) (φ a) = 0
    exact (CoalgHomClass.counit_comp_apply φ a).trans ha)

/-- Vanishing of the induced cotangent linear map forces the original
height-one finite group morphism to be zero, on all test algebras. -/
theorem eq_counit_of_cotangentMap_eq_zero
    (hD : ∀ x : D, counit (R := K) x = 0 → x ^ p = 0)
    (φ : H →ₐc[K] D) (hφ : cotangentMap φ = 0) :
    ∀ a : H, φ a = algebraMap K D (counit (R := K) a) := by
  apply eq_counit_of_augmentation_mem_sq p hD φ
  intro a ha
  let x : RingHom.ker (Bialgebra.counitAlgHom K H) := ⟨a, ha⟩
  have hz := LinearMap.congr_fun hφ
    ((RingHom.ker (Bialgebra.counitAlgHom K H)).toCotangent x)
  change (RingHom.ker (Bialgebra.counitAlgHom K D)).toCotangent
    ⟨φ a, _⟩ = 0 at hz
  exact (Ideal.toCotangent_eq_zero _ _).mp hz

end SupersingularCurves.Geometry.HeightOneHopf

namespace SupersingularCurves.Geometry.EllipticTorsionRealization.FrobeniusKernelHopf
open Coalgebra
variable {K : Type u} [Field K] [IsAlgClosed K]
  {p : ℕ} [Fact p.Prime] [CharP K p] {E : AbelianVariety K 1}
  (HF : FrobeniusKernelHopf p E)

/-- The actual Frobenius kernel has one-dimensional coordinate cotangent. -/
theorem cotangent_finrank :
    Module.finrank K
      (RingHom.ker (Bialgebra.counitAlgHom K HF.Coord)).Cotangent = 1 := by
  apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
  have h := HopfAlgebra.finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero
    K p HF.Coord HF.pow_eq_zero_of_counit_eq_zero
  rw [HF.finrank_eq_prime] at h
  simpa only [pow_one] using h.symm

/-- Endomorphisms of the actual elliptic Frobenius kernel with zero
coordinate differential are the actual zero group morphism. -/
theorem end_eq_counit_of_cotangentMap_eq_zero
    (φ : HF.Coord →ₐc[K] HF.Coord)
    (hφ : HeightOneHopf.cotangentMap φ = 0) :
    ∀ a : HF.Coord, φ a = algebraMap K HF.Coord (counit (R := K) a) :=
  HeightOneHopf.eq_counit_of_cotangentMap_eq_zero p
    HF.pow_eq_zero_of_counit_eq_zero φ hφ

end SupersingularCurves.Geometry.EllipticTorsionRealization.FrobeniusKernelHopf
