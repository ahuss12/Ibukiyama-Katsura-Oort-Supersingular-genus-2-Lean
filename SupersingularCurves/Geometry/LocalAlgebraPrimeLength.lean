/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.LocalAlgebraFrobeniusOrder

/-!
# Prime length and the actual local cotangent space

A finite local augmented algebra of length p has one-dimensional cotangent
space if each nonzero cotangent class is detected by a unit-valued derivation.
The proof constructs a power basis, without a finite-group classification.
-/
set_option autoImplicit false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.LocalAlgebraPrimeLength
open Polynomial
variable {K : Type u} [Field K] {R : Type v} [CommRing R] [Algebra K R]
  [Module.Finite K R]

/-- A nilpotent element vanishes at the vector-space length of the algebra. -/
theorem nilpotent_pow_finrank [Nontrivial R] {x : R} (hx : IsNilpotent x) :
    x ^ Module.finrank K R = 0 := by
  obtain ⟨n, hn⟩ := hx
  have hi : IsIntegral K x := ⟨X ^ n, monic_X_pow n, by simpa using hn⟩
  have hdvd : minpoly K x ∣ X ^ n := minpoly.dvd K x (by simpa using hn)
  obtain ⟨m, _, hm⟩ := (dvd_prime_pow (prime_X (R := K)) n).mp hdvd
  have heq : minpoly K x = X ^ m :=
    eq_of_monic_of_associated (minpoly.monic hi) (monic_X_pow m) hm
  have hxm : x ^ m = 0 := by simpa only [heq, map_pow, aeval_X] using minpoly.aeval K x
  have hle : m ≤ Module.finrank K R := by
    simpa only [heq, natDegree_X_pow] using minpoly.natDegree_le (A := K) x
  exact pow_eq_zero_of_le hle hxm

omit [Module.Finite K R] in
/-- A power basis based at an augmentation-zero element makes its ideal the
entire augmentation ideal. -/
theorem ker_eq_span_of_span_powers (ε : R →ₐ[K] K) (x : R) (hx : ε x = 0)
    (n : ℕ) (hspan : Submodule.span K (Set.range fun i : Fin n => x ^ (i : ℕ)) = ⊤) :
    RingHom.ker ε.toRingHom = Ideal.span {x} := by
  have hmem : ∀ a : R, a - algebraMap K R (ε a) ∈ Ideal.span {x} := by
    intro a
    have ha : a ∈ Submodule.span K (Set.range fun i : Fin n => x ^ (i : ℕ)) := by
      rw [hspan]; trivial
    induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      by_cases hi : (i : ℕ) = 0
      · simp [hi]
      · simp only [map_pow, hx, zero_pow hi, map_zero, sub_zero]
        exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton x)) _
          (Nat.pos_of_ne_zero hi)
    | zero => simp
    | add a b _ _ ha hb =>
      convert (Ideal.span {x}).add_mem ha hb using 1
      simp only [map_add]
      ring
    | smul k a _ ha =>
      convert (Ideal.span {x}).smul_mem (algebraMap K R k) ha using 1
      simp only [Algebra.smul_def, map_mul, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply]
      ring
  apply le_antisymm
  · intro a ha
    have hεa : ε a = 0 := ha
    simpa only [hεa, map_zero, sub_zero] using hmem a
  · apply Ideal.span_le.mpr
    rintro y (rfl : y = x)
    exact hx

omit [Module.Finite K R] in
/-- Over a split residue field, a principal maximal ideal has a cotangent
space spanned by its generator over the original field. -/
theorem cotangent_finrank_eq_one_of_generator [IsLocalRing R]
    (ε : R →ₐ[K] K) (hker : RingHom.ker ε.toRingHom = IsLocalRing.maximalIdeal R)
    (x : IsLocalRing.maximalIdeal R)
    (hgen : IsLocalRing.maximalIdeal R = Ideal.span {x.1})
    (hx : (IsLocalRing.maximalIdeal R).toCotangent x ≠ 0) :
    Module.finrank K (IsLocalRing.CotangentSpace R) = 1 := by
  apply finrank_eq_one_iff'.mpr
  refine ⟨(IsLocalRing.maximalIdeal R).toCotangent x, hx, ?_⟩
  intro z
  obtain ⟨y, rfl⟩ := (IsLocalRing.maximalIdeal R).toCotangent_surjective z
  have hy : (y : R) ∈ Ideal.span {x.1} := hgen ▸ y.2
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hy
  refine ⟨ε b, ?_⟩
  have hbker : b - algebraMap K R (ε b) ∈ IsLocalRing.maximalIdeal R := by
    rw [← hker, RingHom.mem_ker]
    simp
  have hz := Ideal.Cotangent.smul_eq_zero_of_mem hbker
    ((IsLocalRing.maximalIdeal R).toCotangent x)
  have hsmul : b • (IsLocalRing.maximalIdeal R).toCotangent x =
      (ε b) • (IsLocalRing.maximalIdeal R).toCotangent x := by
    simpa only [sub_smul, sub_eq_zero, IsScalarTower.algebraMap_smul] using hz
  rw [← hsmul, ← map_smul]
  congr 1
  apply Subtype.ext
  simpa only [Submodule.coe_smul_of_tower, smul_eq_mul, mul_comm] using hb.symm

/-- Prime vector-space length forces cotangent dimension one when actual
invariant derivations detect every nonzero cotangent class. -/
theorem cotangent_finrank_eq_one [IsLocalRing R] [IsNoetherianRing R]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ε : R →ₐ[K] K) (hker : RingHom.ker ε.toRingHom = IsLocalRing.maximalIdeal R)
    (hlen : Module.finrank K R = p)
    (hder : ∀ x : IsLocalRing.maximalIdeal R,
      (IsLocalRing.maximalIdeal R).toCotangent x ≠ 0 →
      ∃ D : Derivation K R R, IsUnit (D x)) :
    Module.finrank K (IsLocalRing.CotangentSpace R) = 1 := by
  have hn : Nontrivial (IsLocalRing.CotangentSpace R) := by
    by_contra h
    have hsub := not_nontrivial_iff_subsingleton.mp h
    have hm : IsLocalRing.maximalIdeal R = ⊥ :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mp
        (IsLocalRing.subsingleton_cotangentSpace_iff.mp hsub)
    have hinj : Function.Injective ε := (RingHom.injective_iff_ker_eq_bot ε.toRingHom).mpr (hker.trans hm)
    have hle := LinearMap.finrank_le_finrank_of_injective (f := ε.toLinearMap) hinj
    rw [hlen, Module.finrank_self] at hle
    exact (Fact.out : p.Prime).one_lt.not_ge hle
  let := hn
  obtain ⟨z, hz⟩ := exists_ne (0 : IsLocalRing.CotangentSpace R)
  obtain ⟨x, rfl⟩ := (IsLocalRing.maximalIdeal R).toCotangent_surjective z
  obtain ⟨D, hD⟩ := hder x hz
  let : IsArtinianRing R := IsArtinianRing.of_finite K R
  have hxnil : IsNilpotent (x : R) :=
    Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr x.2
  have hxp : (x : R) ^ p = 0 := by simpa only [hlen] using nilpotent_pow_finrank (K := K) hxnil
  have hlin : LinearIndependent K (fun i : Fin p => (x : R) ^ (i : ℕ)) := by
    have h := linearIndependent_pow (K := K) (x : R)
    have hdeg : (minpoly K (x : R)).natDegree = p := by
      rw [LocalAlgebraFrobeniusOrder.minpoly_eq_X_pow_prime p (x : R) hxp D hD,
        natDegree_X_pow]
    exact h.comp (finCongr hdeg.symm) (finCongr hdeg.symm).injective
  have hspan := hlin.span_eq_top_of_card_eq_finrank' (by simpa using hlen.symm)
  have hxaug : ε x = 0 := RingHom.mem_ker.mp (hker.symm ▸ x.2)
  have hgen := ker_eq_span_of_span_powers ε x hxaug p hspan
  exact cotangent_finrank_eq_one_of_generator ε hker x (hker.symm.trans hgen) hz

end SupersingularCurves.Geometry.LocalAlgebraPrimeLength
