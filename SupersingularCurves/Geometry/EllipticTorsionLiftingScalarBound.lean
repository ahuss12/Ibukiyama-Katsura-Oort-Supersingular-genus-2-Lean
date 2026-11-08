/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingFaithfulness

/-!
# Semilinear compatibility fixes the actual Frobenius-kernel scalar

This is the algebraic scalar step of elliptic restriction lifting. Its
semilinear coordinate automorphism and commutation hypotheses are explicit;
their geometric construction from ambient F/V is a separate task.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.HeightOneHopf
open Coalgebra
variable {K : Type u} [Field K]
  {H : Type v} [CommRing H] [HopfAlgebra K H] [Module.Finite K H]

/-- An augmentation-preserving semilinear ring automorphism preserves its
augmentation square. -/
theorem map_augmentation_sq (σ : K ≃+* K) (τ : H ≃+* H)
    (hε : ∀ a : H, counit (R := K) (τ a) = σ (counit (R := K) a)) :
    Ideal.map τ.toRingHom (RingHom.ker (Bialgebra.counitAlgHom K H) ^ 2) =
      RingHom.ker (Bialgebra.counitAlgHom K H) ^ 2 := by
  let I : Ideal H := RingHom.ker (Bialgebra.counitAlgHom K H)
  have hI : Ideal.map τ.toRingHom I = I := by
    ext a
    rw [Ideal.mem_map_iff_of_surjective τ.toRingHom τ.toEquiv.surjective]
    constructor
    · rintro ⟨b, hb, rfl⟩
      change counit (R := K) b = 0 at hb
      change counit (R := K) (τ b) = 0
      rw [hε, hb, map_zero]
    · intro ha
      refine ⟨τ.symm a, ?_, τ.apply_symm_apply a⟩
      change counit (R := K) (τ.symm a) = 0
      apply σ.injective
      rw [map_zero, ← hε, τ.apply_symm_apply]
      exact ha
  change Ideal.map τ.toRingHom (I ^ 2) = I ^ 2
  rw [Ideal.map_pow, hI]

/-- A scalar cotangent action commuting with an invertible semilinear
augmentation action is fixed by its scalar-field automorphism. -/
theorem scalar_fixed_of_commute
    (σ : K ≃+* K) (τ : H ≃+* H)
    (hτ : ∀ c : K, τ (algebraMap K H c) = algebraMap K H (σ c))
    (hε : ∀ a : H, counit (R := K) (τ a) = σ (counit (R := K) a))
    (φ : H →ₐc[K] H) (c : K)
    (hφ : cotangentMap φ = c • LinearMap.id)
    (hcomm : ∀ a : H, φ (τ a) = τ (φ a))
    (a : H) (ha : counit (R := K) a = 0)
    (hne : a ∉ RingHom.ker (Bialgebra.counitAlgHom K H) ^ 2) :
    σ c = c := by
  let I : Ideal H := RingHom.ker (Bialgebra.counitAlgHom K H)
  have hsq : Ideal.map τ.toRingHom (I ^ 2) = I ^ 2 :=
    map_augmentation_sq σ τ hε
  have map_sq {b : H} (hb : b ∈ I ^ 2) : τ b ∈ I ^ 2 := by
    rw [← hsq]
    exact Ideal.mem_map_of_mem τ.toRingHom hb
  have hτa : counit (R := K) (τ a) = 0 := by rw [hε, ha, map_zero]
  have hτne : τ a ∉ I ^ 2 := by
    intro h
    rw [← hsq, Ideal.mem_map_iff_of_surjective τ.toRingHom τ.toEquiv.surjective] at h
    obtain ⟨b, hb, he⟩ := h
    have hab : b = a := τ.injective he
    exact hne (hab ▸ hb)
  have scalar_sq (b : H) (hb : counit (R := K) b = 0) :
      φ b - c • b ∈ I ^ 2 := by
    have h := LinearMap.congr_fun hφ
      (I.toCotangent ⟨b, hb⟩)
    change I.toCotangent ⟨φ b, _⟩ = c • I.toCotangent ⟨b, hb⟩ at h
    have hh := h.trans ((I.toCotangent.restrictScalars K).map_smul c ⟨b, hb⟩).symm
    exact (I.toCotangent_eq).mp hh
  have h₁ := map_sq (scalar_sq a ha)
  have h₂ := scalar_sq (τ a) hτa
  have hmul : τ (c • a) = σ c • τ a := by
    simp only [Algebra.smul_def, map_mul, hτ]
  rw [map_sub, hmul, ← hcomm] at h₁
  have hd : (σ c - c) • τ a ∈ I ^ 2 := by
    have hdiff := (I ^ 2).sub_mem h₂ h₁
    have he : (φ (τ a) - c • τ a) - (φ (τ a) - σ c • τ a) =
        (σ c - c) • τ a := by rw [sub_smul]; abel
    rwa [he] at hdiff
  have hz : (σ c - c) • I.toCotangent ⟨τ a, hτa⟩ = 0 := by
    exact ((I.toCotangent.restrictScalars K).map_smul (σ c - c) ⟨τ a, hτa⟩).symm.trans
      ((I.toCotangent_eq_zero _).mpr hd)
  have hc : σ c - c = 0 := (smul_eq_zero.mp hz).resolve_right (by
    intro h
    exact hτne ((I.toCotangent_eq_zero _).mp h))
  exact sub_eq_zero.mp hc

end SupersingularCurves.Geometry.HeightOneHopf

namespace SupersingularCurves.Geometry.EllipticTorsionRealization.FrobeniusKernelHopf
open Coalgebra
variable {K : Type u} [Field K] [IsAlgClosed K]
  {p : ℕ} [Fact p.Prime] [CharP K p] {E : AbelianVariety K 1}
  (HF : FrobeniusKernelHopf p E)

/-- Apply the semilinear scalar constraint to the actual elliptic Frobenius
kernel, constructing a nonzero cotangent direction from its proved rank. -/
theorem cotangentScalar_fixed_of_commute
    (σ : K ≃+* K) (τ : HF.Coord ≃+* HF.Coord)
    (hτ : ∀ c : K, τ (algebraMap K HF.Coord c) = algebraMap K HF.Coord (σ c))
    (hε : ∀ a : HF.Coord, counit (R := K) (τ a) = σ (counit (R := K) a))
    (φ : HF.Coord →ₐc[K] HF.Coord) (hcomm : ∀ a, φ (τ a) = τ (φ a)) :
    σ (HF.cotangentScalar φ) = HF.cotangentScalar φ := by
  let I : Ideal HF.Coord := RingHom.ker (Bialgebra.counitAlgHom K HF.Coord)
  letI : Module.Finite K I := inferInstanceAs (Module.Finite K (I.restrictScalars K))
  letI : Module.Finite K I.Cotangent :=
    Module.Finite.of_surjective (I.toCotangent.restrictScalars K) I.toCotangent_surjective
  have hpos : 0 < Module.finrank K I.Cotangent := by rw [HF.cotangent_finrank]; decide
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  obtain ⟨a, rfl⟩ := I.toCotangent_surjective x
  exact HeightOneHopf.scalar_fixed_of_commute σ τ hτ hε φ
    (HF.cotangentScalar φ) (HF.cotangentMap_eq_scalar φ) hcomm a a.property
    (fun h => hx ((I.toCotangent_eq_zero _).mpr h))

end SupersingularCurves.Geometry.EllipticTorsionRealization.FrobeniusKernelHopf
